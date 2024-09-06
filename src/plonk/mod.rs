// This module implements plonk circuits, prover and verifier.

pub mod gadgets;

use std::collections::{HashMap, HashSet};
use std::fmt::Debug;
use std::ops::{Add, Div, DivAssign, Mul, MulAssign, Sub};
use std::time::Instant;
use ark_ec::PairingEngine;
use ark_ff::{BigInteger, Field, One, PrimeField, Zero};
use ark_poly::{EvaluationDomain, GeneralEvaluationDomain, Polynomial, UVPolynomial};
use ark_poly::univariate::DensePolynomial;
use rand::RngCore;
use crate::{CaulkTranscript, KZGCommit, PublicParameters};
use crate::ramlookup::{compute_aggregate_poly, compute_scaled_polynomial, compute_shifted_difference, compute_sum_poly};
use rayon::iter::ParallelIterator;

pub struct PlonkSetup<F: PrimeField> {
    pub h_domain_size: usize,                   // domain size in bits
    pub domain: GeneralEvaluationDomain<F>,     // the subgroup H of roots of unity
    pub l0_poly: DensePolynomial<F>,            // lagrange polynomial at w^0
    pub k1: F,                                  // k1 coset identifier
    pub k2: F,                                  // k2 coset identifier: k1.H, k2.H, H are distinct
}

pub struct PlonkCircuitPolynomials<F: PrimeField> {
    pub q_M: DensePolynomial<F>,
    pub q_L: DensePolynomial<F>,
    pub q_R: DensePolynomial<F>,
    pub q_O: DensePolynomial<F>,
    pub q_C: DensePolynomial<F>,
    pub S_a: DensePolynomial<F>,
    pub S_b: DensePolynomial<F>,
    pub S_c: DensePolynomial<F>,
    pub permutation: Vec<F>,
}

pub struct PlonkCircuitKeys<E: PairingEngine> {
    pub qm_com: E::G1Affine,                    // commitment to q_M polynomial
    pub ql_com: E::G1Affine,                    // commitment to q_L polynomial
    pub qr_com: E::G1Affine,                    // commitment to q_R polynomial
    pub qo_com: E::G1Affine,                    // commitment to q_O polynomial
    pub qc_com: E::G1Affine,                    // commitment to q_C polynomial
    pub Sa_com: E::G1Affine,                    // commitment to S_a polynomial
    pub Sb_com: E::G1Affine,                    // commitment to S_b polynomial
    pub Sc_com: E::G1Affine,                    // commitment to S_c polynomial
    pub g2_tau: E::G2Affine,                    // KZG verification key
}

pub struct PlonkProof<E: PairingEngine> {
    pub wa_com: E::G1Affine,                    // commitment to a(X) poly
    pub wb_com: E::G1Affine,                    // commitment to b(X) poly
    pub wc_com: E::G1Affine,                    // commitment to c(X) poly
    pub z_com:  E::G1Affine,                    // commitment to z(X) poly
    pub t_lo_com: E::G1Affine,                  // comm to t_lo(X)
    pub t_mid_com: E::G1Affine,                 // comm to t_mid(X)
    pub t_hi_com: E::G1Affine,                  // comm to t_hi(X)
    pub wa_phi: E::Fr,                          // a(\phi)
    pub wb_phi: E::Fr,                          // b(\phi)
    pub wc_phi: E::Fr,                          // c(\phi)
    pub S_a_phi: E::Fr,                         // S_a(\phi)
    pub S_b_phi: E::Fr,                         // S_b(\phi)
    pub z_wphi: E::Fr,                          // z(\omega \phi)
    pub pi_phi: E::G1Affine,                    // opening proof at phi
    pub pi_wphi: E::G1Affine,                   // opening proof at \omega \phi
}


pub fn compute_plonk_proof<E: PairingEngine>(
    instance: &PlonkCircuitKeys<E>,
    circuit: &PlonkCircuitPolynomials<E::Fr>,
    witness: &Vec<E::Fr>,
    plonk_setup: &PlonkSetup<E::Fr>,
    pp: &PublicParameters<E>,
) -> PlonkProof<E> {

    let n = 1usize << plonk_setup.h_domain_size;
    let mut transcript = CaulkTranscript::<E::Fr>::new();
    let mut start = Instant::now();
    let mut begin = Instant::now();
    // add the initial commitments to the transcript
    transcript.append_element(b"qm_com", &instance.qm_com);
    transcript.append_element(b"ql_com", &instance.ql_com);
    transcript.append_element(b"qr_com", &instance.qr_com);
    transcript.append_element(b"qo_com", &instance.qo_com);
    transcript.append_element(b"qc_com", &instance.qc_com);
    transcript.append_element(b"sa_com", &instance.Sa_com);
    transcript.append_element(b"sb_com", &instance.Sb_com);
    transcript.append_element(b"sc_com", &instance.Sc_com);

    // compute and add commitments to witness polynomials to the transcript
    let (wa_poly, wb_poly, wc_poly, wa_com, wb_com, wc_com) =
        compute_witness_polynomials(
            witness,
            plonk_setup,
            pp
        );
    println!("Committed witness in {} secs", start.elapsed().as_secs());
    transcript.append_element(b"a_com", &wa_com);
    transcript.append_element(b"b_com", &wb_com);
    transcript.append_element(b"c_com", &wc_com);

    // get challenges beta, gamma for computing z polynomial
    let beta = E::Fr::one(); //transcript.get_and_append_challenge(b"beta");
    let gamma = transcript.get_and_append_challenge(b"gamma");
    let (z_poly, z_com) = compute_z_polynomial(witness, beta, gamma, circuit, plonk_setup,pp);

    println!("Computed z polynomial in {} secs", start.elapsed().as_secs());
    // append commitment to z polynomial to transcript
    transcript.append_element(b"z_com", &z_com);
    let alpha = transcript.get_and_append_challenge(b"alpha");

    // compute polynomial t(X)
    start = Instant::now();
    let x_poly: DensePolynomial<E::Fr> = DensePolynomial::from_coefficients_vec(vec![E::Fr::zero(), E::Fr::one()]);
    let one_poly: DensePolynomial<E::Fr> = DensePolynomial::from_coefficients_vec(vec![E::Fr::one()]);
    let t_part_1  = compute_sum_poly::<E>(
        &[
            &wa_poly * &(&wb_poly * &circuit.q_M),
            &wa_poly * &circuit.q_L,
            &wb_poly * &circuit.q_R,
            &wc_poly * &circuit.q_O,
            circuit.q_C.clone()
        ]);
    let factor_1 = &wa_poly + &(&compute_scaled_polynomial::<E>(&x_poly, beta) + &DensePolynomial::from_coefficients_vec(vec![gamma]));
    let factor_2 = &wb_poly + &(&compute_scaled_polynomial::<E>(&x_poly, beta*plonk_setup.k1) + &DensePolynomial::from_coefficients_vec(vec![gamma]));
    let factor_3 = &wc_poly + &(&compute_scaled_polynomial::<E>(&x_poly, beta*plonk_setup.k2) + &DensePolynomial::from_coefficients_vec(vec![gamma]));
    let t_part_2 = &(&factor_1 * &factor_2) * &(&factor_3 * &z_poly);
    let zw_poly = &compute_shifted_difference::<E>(&z_poly, plonk_setup.h_domain_size) + &z_poly;
    let factor_1 = &wa_poly + &(&compute_scaled_polynomial::<E>(&circuit.S_a, beta) + &DensePolynomial::from_coefficients_vec(vec![gamma]));
    let factor_2 = &wb_poly + &(&compute_scaled_polynomial::<E>(&circuit.S_b, beta) + &DensePolynomial::from_coefficients_vec(vec![gamma]));
    let factor_3 = &wc_poly + &(&compute_scaled_polynomial::<E>(&circuit.S_c, beta) + &DensePolynomial::from_coefficients_vec(vec![gamma]));
    let t_part_3 = &(&factor_1 * &factor_2) * &(&factor_3 * &zw_poly);


    let l0_poly = plonk_setup.l0_poly.clone();
    let t_part_4 = &l0_poly * &(&z_poly - &DensePolynomial::from_coefficients_vec(vec![E::Fr::one()]));

    let t_part_23 = &t_part_2 - &t_part_3;
    let t_poly_num = compute_aggregate_poly::<E>(&[t_part_1.clone(), t_part_23.clone(), t_part_4.clone()], alpha);
    //println!("Computed t numerator in {} secs", start.elapsed().as_secs());

    start = Instant::now();
    let (t_poly, _) = t_poly_num.divide_by_vanishing_poly(plonk_setup.domain).unwrap();


    //let u = transcript.get_and_append_challenge(b"u");
    //assert_eq!(t_poly.evaluate(&u) * plonk_setup.domain.evaluate_vanishing_polynomial(u), t_poly_num.evaluate(&u), "Polynomial constraints not satisfied");

    let mut t_coeffs = t_poly.coeffs().to_vec().clone();
    t_coeffs.resize(3*n, E::Fr::zero());

    // Split t_poly into three polynomials t_lo, t_mid and t_hi
    let t_lo = DensePolynomial::from_coefficients_slice(&t_coeffs[0..n]);
    let t_mid = DensePolynomial::from_coefficients_slice(&t_coeffs[n..2*n]);
    let t_hi = DensePolynomial::from_coefficients_slice(&t_coeffs[2*n..3*n]);

    // Commit to above polynomials and add to the transcript
    let t_lo_com = KZGCommit::commit_g1(&pp.poly_ck, &t_lo);
    let t_mid_com = KZGCommit::commit_g1(&pp.poly_ck, &t_mid);
    let t_hi_com = KZGCommit::commit_g1(&pp.poly_ck, &t_hi);

    transcript.append_element(b"t_lo_com", &t_lo_com);
    transcript.append_element(b"t_mid_com", &t_mid_com);
    transcript.append_element(b"t_hi_com", &t_hi_com);

    //println!("Committed to t polynomial in {} secs", start.elapsed().as_secs());
    let phi = transcript.get_and_append_challenge(b"phi");

    start = Instant::now();
    // Send partial evaluations
    let wa_phi = wa_poly.evaluate(&phi);
    let wb_phi = wb_poly.evaluate(&phi);
    let wc_phi = wc_poly.evaluate(&phi);
    let sa_phi = circuit.S_a.evaluate(&phi);
    let sb_phi = circuit.S_b.evaluate(&phi);
    let zw_phi = zw_poly.evaluate(&phi);
    //assert_eq!(z_poly.evaluate(&(phi * plonk_setup.domain.element(1))), zw_poly.evaluate(&phi), "Z(X) and Z(wX) don't match");

    transcript.append_element(b"wa_phi", &wa_phi);
    transcript.append_element(b"wb_phi", &wb_phi);
    transcript.append_element(b"wc_phi", &wc_phi);
    transcript.append_element(b"sa_phi", &sa_phi);
    transcript.append_element(b"sb_phi", &sb_phi);
    transcript.append_element(b"zw_phi", &zw_phi);
    //println!("Sent evaluations in {} secs", start.elapsed().as_secs());

    let v = transcript.get_and_append_challenge(b"v");
    start = Instant::now();
    // compute linearisation polynomial r(X)
    let r_part_1 = &compute_scaled_polynomial::<E>(&circuit.q_M, wa_phi*wb_phi)
                                            .add(compute_scaled_polynomial::<E>(&circuit.q_L, wa_phi))
                                            .add(compute_scaled_polynomial::<E>(&circuit.q_R, wb_phi))
                                            .add(compute_scaled_polynomial::<E>(&circuit.q_O, wc_phi)) + &circuit.q_C;
    let r_part_2 = compute_scaled_polynomial::<E>(&z_poly, (wa_phi + beta * phi + gamma)*(wb_phi + beta * plonk_setup.k1 * phi + gamma)*(wc_phi + beta * plonk_setup.k2 * phi + gamma));
    let r_part_31 = &compute_scaled_polynomial::<E>(&circuit.S_c, beta) + &DensePolynomial::from_coefficients_vec(vec![gamma + wc_phi]);
    let r_part_32 = compute_scaled_polynomial::<E>(&r_part_31, (wa_phi + beta*sa_phi + gamma)*(wb_phi + beta * sb_phi + gamma)*zw_phi);
    let r_part_23 = &r_part_2 - &r_part_32;

    let zh_phi = plonk_setup.domain.evaluate_vanishing_polynomial(phi);
    let l0_phi = phi.sub(E::Fr::one()).inverse().unwrap() * E::Fr::from(n as u128).inverse().unwrap() * zh_phi;

    let r_part_4 = compute_scaled_polynomial::<E>(&(&z_poly - &one_poly), l0_phi);
    let r_part_5 = &(&compute_scaled_polynomial::<E>(&t_lo, zh_phi) + &compute_scaled_polynomial::<E>(&t_mid, zh_phi * phi.pow(E::Fr::from(n as u128).into_repr()))) +
                            &compute_scaled_polynomial::<E>(&t_hi, zh_phi * phi.square().pow(E::Fr::from(n as u128).into_repr()));

    let r_poly_combined = compute_aggregate_poly::<E>(&[r_part_1.clone(), r_part_23.clone(), r_part_4.clone()], alpha);
    let r_poly = &r_poly_combined - &r_part_5;

    //assert_eq!(r_poly.evaluate(&phi), E::Fr::zero(), "r(X) is not correctly computed");

    // compute opening polynomial W
    let w_sub_polys = [
        r_poly,
        wa_poly,
        wb_poly,
        wc_poly,
        circuit.S_a.clone(),
        circuit.S_b.clone(),
    ];
    let w_poly = &compute_aggregate_poly::<E>(&w_sub_polys, v) - &DensePolynomial::from_coefficients_vec(vec![v*wa_phi + v*v*wb_phi + v*v*v*wc_phi + v*v*v*v*sa_phi + v*v*v*v*v*sb_phi]);

    //assert_eq!(w_poly.evaluate(&phi), E::Fr::zero(), "W(X) is not correctly computed");

    let w_q_poly = &w_poly / &DensePolynomial::from_coefficients_vec(vec![E::Fr::zero() - phi, E::Fr::one()]);

    //assert_eq!(w_poly.evaluate(&alpha), w_q_poly.evaluate(&alpha) * (alpha - phi), "W_Q(X) is not correctly computed");

    let z_q_poly =
        &(&z_poly - &DensePolynomial::from_coefficients_slice(&[zw_phi])) / &DensePolynomial::from_coefficients_vec(vec![E::Fr::zero() - phi*plonk_setup.domain.element(1usize), E::Fr::one()]);

    //assert_eq!(z_poly.evaluate(&alpha) - zw_phi, z_q_poly.evaluate(&alpha) * (alpha - phi*plonk_setup.domain.element(1usize)), "Z_Q(X) is not correctly computed");

    let w_q_com = KZGCommit::commit_g1(&pp.poly_ck, &w_q_poly);
    let z_q_com = KZGCommit::commit_g1(&pp.poly_ck, &z_q_poly);

    transcript.append_element(b"w_q_com", &w_q_com);
    transcript.append_element(b"z_q_com", &z_q_com);

    println!("Committed to linearized polynomials in {} secs", start.elapsed().as_secs());


    PlonkProof::<E> {
        wa_com: wa_com,
        wb_com: wb_com,
        wc_com: wc_com,
        z_com: z_com,
        t_lo_com: t_lo_com,
        t_mid_com: t_mid_com,
        t_hi_com: t_hi_com,
        wa_phi: wa_phi,
        wb_phi: wb_phi,
        wc_phi: wc_phi,
        S_a_phi: sa_phi,
        S_b_phi: sb_phi,
        z_wphi: zw_phi,
        pi_phi: w_q_com,
        pi_wphi: z_q_com,
    }

}


pub fn compute_plonk_circuit_polynomials<F: PrimeField>(
    pb: &mut Protoboard<F>,
    plonk_setup: &PlonkSetup<F>,
) -> PlonkCircuitPolynomials<F> {
    let (q_M, q_L, q_R, q_O, q_C, S_a, S_b, S_c, permutation) = pb.output_circuit_polynomials(plonk_setup);
    PlonkCircuitPolynomials::<F> {
        q_M,
        q_L,
        q_R,
        q_O,
        q_C,
        S_a,
        S_b,
        S_c,
        permutation,
    }
}

pub fn compute_plonk_circuit_keys<E: PairingEngine>(
    circuit: &PlonkCircuitPolynomials<E::Fr>,
    pp: &PublicParameters<E>,
) -> PlonkCircuitKeys<E> {
    let qm_com = KZGCommit::commit_g1(&pp.poly_ck, &circuit.q_M);
    let ql_com = KZGCommit::commit_g1(&pp.poly_ck, &circuit.q_L);
    let qr_com = KZGCommit::commit_g1(&pp.poly_ck, &circuit.q_R);
    let qo_com = KZGCommit::commit_g1(&pp.poly_ck, &circuit.q_O);
    let qc_com = KZGCommit::commit_g1(&pp.poly_ck, &circuit.q_C);
    let Sa_com = KZGCommit::commit_g1(&pp.poly_ck, &circuit.S_a);
    let Sb_com = KZGCommit::commit_g1(&pp.poly_ck, &circuit.S_b);
    let Sc_com = KZGCommit::commit_g1(&pp.poly_ck, &circuit.S_c);

    PlonkCircuitKeys::<E> {
        qm_com: qm_com,
        ql_com: ql_com,
        qr_com: qr_com,
        qo_com: qo_com,
        qc_com: qc_com,
        Sa_com: Sa_com,
        Sb_com: Sb_com,
        Sc_com: Sc_com,
        g2_tau: pp.g2_powers[1],
    }

}

pub fn compute_witness_polynomials<E: PairingEngine>(
    witness: &Vec<E::Fr>,
    plonk_setup: &PlonkSetup<E::Fr>,
    pp: &PublicParameters<E>,
) -> (DensePolynomial<E::Fr>, DensePolynomial<E::Fr>, DensePolynomial<E::Fr>, E::G1Affine, E::G1Affine, E::G1Affine)
{
    let n = 1usize << plonk_setup.h_domain_size;
    let wa_poly = DensePolynomial::from_coefficients_vec(plonk_setup.domain.ifft(&witness[0..n]));
    let wb_poly = DensePolynomial::from_coefficients_vec(plonk_setup.domain.ifft(&witness[n..2*n]));
    let wc_poly = DensePolynomial::from_coefficients_vec(plonk_setup.domain.ifft(&witness[2*n..3*n]));
    let wa_com = KZGCommit::commit_g1(&pp.poly_ck, &wa_poly);
    let wb_com = KZGCommit::commit_g1(&pp.poly_ck, &wb_poly);
    let wc_com = KZGCommit::commit_g1(&pp.poly_ck, &wc_poly);

    (
        wa_poly,
        wb_poly,
        wc_poly,
        wa_com,
        wb_com,
        wc_com
    )
}

pub fn compute_z_polynomial<E: PairingEngine>(
    witness: &Vec<E::Fr>,
    beta: E::Fr,
    gamma: E::Fr,
    circuit: &PlonkCircuitPolynomials<E::Fr>,
    plonk_setup: &PlonkSetup<E::Fr>,
    pp: &PublicParameters<E>,
) -> (DensePolynomial<E::Fr>, E::G1Affine)
{
    let n = 1usize << plonk_setup.h_domain_size;
    let mut z_evals: Vec<E::Fr> = Vec::new();
    z_evals.resize(n, E::Fr::zero());
    let mut prod = E::Fr::one();
    for i in 0..n {
        let wi = plonk_setup.domain.element(i);
        let k1wi = plonk_setup.k1 * wi;
        let k2wi = plonk_setup.k2 * wi;
        prod.mul_assign((witness[i] + beta * wi + gamma) * (witness[n+i] + beta * k1wi + gamma) * (witness[2*n+i] + beta * k2wi + gamma));
        prod.div_assign((witness[i] + beta * circuit.permutation[i] + gamma) * (witness[n+i] + beta * circuit.permutation[n+i] + gamma) * (witness[2*n+i] + beta * circuit.permutation[2*n+i] + gamma));
        z_evals[(i+1) % n] = prod;
    }
    //println!("{}", prod);
    assert_eq!(z_evals[0], E::Fr::one(), "Permutation not satisfied");
    let z_poly_vec = plonk_setup.domain.ifft(&z_evals);
    let z_poly = DensePolynomial::from_coefficients_vec(z_poly_vec);
    let z_com = KZGCommit::commit_g1(&pp.poly_ck, &z_poly);
    (z_poly, z_com)
}

#[derive(Clone, Debug)]
pub struct Variable {
    pub name: String,
    pub pb_index: usize,
}

// Defines the plonk constraint
// q_m(x[a]x[b]) + q_l x[a] + q_r x[b] + q_o x[c] + q_c = 0
#[derive(Clone, Debug)]
pub struct Constraint<F: PrimeField> {
    pub q_m: F,
    pub q_l: F,
    pub q_r: F,
    pub q_o: F,
    pub q_c: F,
    pub idx_a: usize,
    pub idx_b: usize,
    pub idx_c: usize
}

#[derive(Clone, Debug)]
pub struct ConstraintSystem<F: PrimeField> {
    pub constraints: Vec<Constraint<F>>,
    pub permuation: HashMap<usize,usize>,
    pub a_wires: Vec<usize>,
    pub b_wires: Vec<usize>,
    pub c_wires: Vec<usize>,
    pub qm_poly_coeffs: Vec<F>,
    pub ql_poly_coeffs: Vec<F>,
    pub qr_poly_coeffs: Vec<F>,
    pub qo_poly_coeffs: Vec<F>,
    pub qc_poly_coeffs: Vec<F>,
}

// Defines a component/gadget.
// input: a set of assigned variables on protoboard
// output: a set of assigned variables on protoboard
pub trait Component<F: PrimeField> {
    fn attach(&mut self, pb:&mut Protoboard<F>, inputs: &Vec<Variable>, outputs: &Vec<Variable>);
    fn generate_constraints(&mut self, pb:&mut Protoboard<F>);
    fn generate_witness(&mut self, pb:&mut Protoboard<F>);
}



pub struct Protoboard<F: PrimeField> {
    pub n_variables: usize,
    pub n_inputs: usize,
    pub n_constraints: usize,
    pub permutation: Vec<usize>,
    pub pb_vals: Vec<F>,
    pub cs: ConstraintSystem<F>,
}

// Implementations of Classes
impl<F:PrimeField> PlonkSetup<F> {
    pub fn new(h_domain_size: usize, rng: &mut RngCore) -> Self {
        let n: usize = 1usize << h_domain_size;
        let domain = GeneralEvaluationDomain::<F>::new(n).unwrap();
        let mut k1: F = F::rand(rng);
        let mut k2: F = F::rand(rng);
        let mut prod = domain.evaluate_vanishing_polynomial(k1) * domain.evaluate_vanishing_polynomial(k2) * domain.evaluate_vanishing_polynomial(k1.mul(k2));
        while prod.eq(&F::zero()) {
            k1 = F::rand(rng);
            k2 = F::rand(rng);
            prod = domain.evaluate_vanishing_polynomial(k1) * domain.evaluate_vanishing_polynomial(k2) * domain.evaluate_vanishing_polynomial(k1.mul(k2));
        }

        let mut l0_evals: Vec<F> = Vec::new();
        l0_evals.resize(n, F::zero());
        l0_evals[0] = F::one();
        let l0_poly = DensePolynomial::from_coefficients_vec(domain.ifft(&l0_evals));

        Self {
            h_domain_size,
            domain: domain,
            l0_poly: l0_poly,
            k1: k1,
            k2: k2,
        }
    }
}


impl Variable {

    pub fn new(name: &str) -> Self {
        Variable {
            name: name.to_string(),
            pb_index: usize::MAX
        }
    }
}


impl<F:PrimeField> Protoboard<F> {
    pub fn new() -> Self {
        Protoboard::<F> {
            n_variables: 0,
            n_inputs: 0,
            n_constraints: 0,
            permutation: vec![],
            pb_vals: vec![],
            cs: ConstraintSystem::<F> {
                constraints: vec![],
                permuation: HashMap::default(),
                a_wires: vec![],
                b_wires: vec![],
                c_wires: vec![],
                qm_poly_coeffs: vec![],
                ql_poly_coeffs: vec![],
                qr_poly_coeffs: vec![],
                qo_poly_coeffs: vec![],
                qc_poly_coeffs: vec![],
            },
        }
    }

    pub fn get_input_size(&self) -> usize {
        self.n_inputs
    }

    pub fn get_num_constraints(&self) -> usize {
        self.cs.constraints.len()
    }

    pub fn get_num_variables(&self) -> usize {
        self.n_variables
    }

    pub fn assign_index(&mut self, var: &mut Variable) {
        var.pb_index = self.n_variables;
        self.pb_vals.push(F::zero());
        self.n_variables = self.n_variables+1;
    }

    pub fn assign_val(&mut self, var:&Variable, val: F) {
        self.pb_vals[var.pb_index] = val;
    }

    pub fn val(&self, var:&Variable) -> F {
        self.pb_vals[var.pb_index]
    }

    pub fn add_constraint(&mut self, constraint: &Constraint<F>) {
        let constraint: Constraint<F> = (*constraint).clone();
        assert_eq!(constraint.idx_a < self.n_variables, true, "Left variable {} un-assigned", constraint.idx_a);
        assert_eq!(constraint.idx_b < self.n_variables, true, "Right variable {} un-assigned", constraint.idx_b);
        assert_eq!(constraint.idx_c < self.n_variables, true, "Output variable {} un-assigned", constraint.idx_c);
        self.cs.constraints.push(constraint.clone());
        self.cs.a_wires.push(constraint.idx_a);
        self.cs.b_wires.push(constraint.idx_b);
        self.cs.c_wires.push(constraint.idx_c);
        self.cs.qm_poly_coeffs.push(constraint.q_m);
        self.cs.ql_poly_coeffs.push(constraint.q_l);
        self.cs.qr_poly_coeffs.push(constraint.q_r);
        self.cs.qo_poly_coeffs.push(constraint.q_o);
        self.cs.qc_poly_coeffs.push(constraint.q_c);
        self.n_constraints = self.n_constraints + 1;
    }

    // add gate such that out = a.left + b.right + c
    pub fn add_addition_gate(&mut self, left: &Variable, right: &Variable, out: &Variable, a: F, b: F, c: F) {
        let constraint: Constraint<F> = Constraint {
            q_m: F::zero(),
            q_l: a,
            q_r: b,
            q_o: F::zero().sub(F::one()),
            q_c: c,
            idx_a: left.pb_index,
            idx_b: right.pb_index,
            idx_c: out.pb_index
        };

        self.add_constraint(&constraint);
    }

    // add gate such that out = left * right
    pub fn add_multiplication_gate(&mut self, left: &Variable, right: &Variable, out: &Variable) {
        let constraint: Constraint<F> = Constraint {
            q_m: F::one(),
            q_l: F::zero(),
            q_r: F::zero(),
            q_o: F::zero() - F::one(),
            q_c: F::zero(),
            idx_a: left.pb_index,
            idx_b: right.pb_index,
            idx_c: out.pb_index
        };

        self.add_constraint(&constraint);
    }

    // add gate such that left = left * right
    pub fn add_boolean_gate(&mut self, left: &Variable) {
        let constraint: Constraint<F> = Constraint {
            q_m: F::one(),
            q_l: F::zero() - F::one(),
            q_r: F::zero(),
            q_o: F::zero(),
            q_c: F::zero(),
            idx_a: left.pb_index,
            idx_b: left.pb_index,
            idx_c: left.pb_index
        };

        self.add_constraint(&constraint);
    }

    pub fn add_public_input(&mut self, left: &Variable) {
        let constraint: Constraint<F> = Constraint {
            q_m: F::zero(),
            q_l: F::one(),
            q_r: F::zero(),
            q_o: F::zero(),
            q_c: F::zero(),
            idx_a: left.pb_index,
            idx_b: left.pb_index,
            idx_c: left.pb_index
        };
        self.add_constraint(&constraint);

    }


    pub fn output_circuit_polynomials(&mut self, plonk_setup: &PlonkSetup<F>) -> (
        DensePolynomial<F>,                 // q_M
        DensePolynomial<F>,                 // q_L
        DensePolynomial<F>,                 // q_R
        DensePolynomial<F>,                 // q_O
        DensePolynomial<F>,                 // q_C
        DensePolynomial<F>,                 // S_a
        DensePolynomial<F>,                 // S_b
        DensePolynomial<F>,                 // S_c
        Vec<F>,
    ) {
        // extend all polynomials to the domain size
        let n = plonk_setup.domain.size();
        self.cs.qm_poly_coeffs.resize(n, F::zero());
        self.cs.ql_poly_coeffs.resize(n, F::zero());
        self.cs.qr_poly_coeffs.resize(n, F::zero());
        self.cs.qo_poly_coeffs.resize(n, F::zero());
        self.cs.qc_poly_coeffs.resize(n, F::zero());
        self.cs.a_wires.resize(n, 0);
        self.cs.b_wires.resize(n, 0);
        self.cs.c_wires.resize(n, 0);

        // build permutation
        // for each i in m = number of variables, partition[i] contains the vector
        // with entries from 0..3n, which point to the variable i.
        // We identify a-wires witn indices 0..n, b-wires with indices n..2n, and c-wires with indices 2n..3n
        let mut partition: HashMap<usize, Vec<usize>> = HashMap::new();
        for i in 0..n {
            match partition.get_mut(&self.cs.a_wires[i]) {
                Some(list) => { list.push(i) }
                None => { partition.insert(self.cs.a_wires[i], vec![i]); }
            }
            match partition.get_mut(&self.cs.b_wires[i]) {
                Some(list) => { list.push(n+i) }
                None => { partition.insert(self.cs.b_wires[i], vec![n+i]); }
            }
            match partition.get_mut(&self.cs.c_wires[i]) {
                Some(list) => { list.push(n+n+i) }
                None => { partition.insert(self.cs.c_wires[i], vec![n+n+i]); }
            }
        }

        // print permutation
        self.permutation.resize(3*n, 0);
        for v_idx in partition.keys() {
            let cycle = partition.get(v_idx).unwrap();
            let n_cycle = cycle.len();
            for i in 0..n_cycle {
                self.permutation[cycle[i]] = cycle[(i+1) % n_cycle];
            }

            /*
            print!("(");
            for i in 0..n_cycle {
                print!("{} ", cycle[i]);
            }
            println!(")");

             */
        }

        // map the permutation to cosets of H
        let mut permutation_on_coset: Vec<F> = Vec::new();
        for i in 0..self.permutation.len() {
            let x = &self.permutation[i];
            if *x < n {
                permutation_on_coset.push(plonk_setup.domain.element(*x));
            } else if *x < 2 * n {
                permutation_on_coset.push(plonk_setup.k1 * plonk_setup.domain.element(*x - n));
            } else {
                permutation_on_coset.push(plonk_setup.k2 * plonk_setup.domain.element(*x - (2 * n)));
            }
        }


        let q_M = DensePolynomial::from_coefficients_vec(plonk_setup.domain.ifft(&self.cs.qm_poly_coeffs));
        let q_L = DensePolynomial::from_coefficients_vec(plonk_setup.domain.ifft(&self.cs.ql_poly_coeffs));
        let q_R = DensePolynomial::from_coefficients_vec(plonk_setup.domain.ifft(&self.cs.qr_poly_coeffs));
        let q_O = DensePolynomial::from_coefficients_vec(plonk_setup.domain.ifft(&self.cs.qo_poly_coeffs));
        let q_C = DensePolynomial::from_coefficients_vec(plonk_setup.domain.ifft(&self.cs.qc_poly_coeffs));

        let mut s_a_coeffs: Vec<F> = Vec::new();
        let mut s_b_coeffs: Vec<F> = Vec::new();
        let mut s_c_coeffs: Vec<F> = Vec::new();

        for i in 0..n {
            s_a_coeffs.push(permutation_on_coset[i]);
            s_b_coeffs.push(permutation_on_coset[i+n]);
            s_c_coeffs.push(permutation_on_coset[i + 2*n]);
        }

        let S_a: DensePolynomial<F> = DensePolynomial::from_coefficients_vec(plonk_setup.domain.ifft(&s_a_coeffs));
        let S_b: DensePolynomial<F> = DensePolynomial::from_coefficients_vec(plonk_setup.domain.ifft(&s_b_coeffs));
        let S_c: DensePolynomial<F> = DensePolynomial::from_coefficients_vec(plonk_setup.domain.ifft(&s_c_coeffs));

        (
            q_M,
            q_L,
            q_R,
            q_O,
            q_C,
            S_a,
            S_b,
            S_c,
            permutation_on_coset,
        )
    }

    pub fn output_witness(&self) -> Vec<F> {
        let wires: Vec<usize> = vec![self.cs.a_wires.clone(), self.cs.b_wires.clone(), self.cs.c_wires.clone()].concat();
        let witness: Vec<F> = wires.into_iter().map(|x| self.pb_vals[x]).collect();
        witness
    }


    pub fn is_satisfied(&mut self) ->bool {
        for i in 0..self.cs.constraints.len() {
            let constraint: Constraint<F> = self.cs.constraints[i].clone();
            let q_m = constraint.q_m;
            let q_l = constraint.q_l;
            let q_r = constraint.q_r;
            let q_o = constraint.q_o;
            let q_c = constraint.q_c;

            let sum:F = q_m * self.pb_vals[constraint.idx_a] * self.pb_vals[constraint.idx_b] + q_l * self.pb_vals[constraint.idx_a]
                        + q_r * self.pb_vals[constraint.idx_b] + q_o * self.pb_vals[constraint.idx_c] + q_c;
            if sum != F::zero() {
                println!("Constraint {} with {:?} not satisfied", i, constraint);
                return false;
            }

        }
        true
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::ops::{Add, Mul};
    use std::time::Instant;
    use ark_bls12_381::Bls12_381;
    use ark_ec::bls12::Bls12;
    use ark_ec::PairingEngine;
    use ark_ff::{One, Zero};
    use ark_std::{test_rng, UniformRand};
    use rayon::iter::IntoParallelIterator;
    use crate::afgo::AFGSetup;
    use crate::aplonk::compute_aplonk_proof;
    use crate::plonk::gadgets::{InnerProductComponent, RangeCheckComponent};


    #[test]
    pub fn test_simple_satisfiability()
    {
        test_simple_satisfiability_helper::<Bls12_381>();
    }

    #[test]
    pub fn test_range_component()
    {
        test_range_component_helper::<Bls12_381>();
    }

    #[test]
    pub fn test_inner_product_component()
    {
        test_inner_product_helper::<<Bls12<ark_bls12_381::Parameters> as ark_ec::PairingEngine>::Fr>();
    }

    #[test]
    pub fn test_witness_polynomials()
    {
        test_witness_polynomials_helper::<Bls12_381>();
    }


    fn test_range_component_helper<E: PairingEngine>() {
        let mut pb: Protoboard<E::Fr> = Protoboard::new();
        let mut range_checker: RangeCheckComponent = RangeCheckComponent::new(5usize);
        let n_inputs: usize = 2;
        let mut inputs: Vec<Variable> = Vec::new();
        for i in 0..n_inputs {
            inputs.push(Variable::new("input"));
        }

        for i in 0..inputs.len() {
            pb.assign_index(&mut inputs[i]);
        }

        range_checker.attach(&mut pb, &inputs, &inputs);
        range_checker.generate_constraints(&mut pb);

        // assign values to inputs
        for i in 0..inputs.len() {
            pb.assign_val(&inputs[i], E::Fr::from(11u128));
        }
        range_checker.generate_witness(&mut pb);

        // Print Variables and Check circuit satisfiability
        for i in 0..pb.pb_vals.len() {
            println!("Value of variable {} = {}", i, pb.pb_vals[i]);
        }

        println!("Circuit Satisfied = {}", pb.is_satisfied());

    }

    fn test_inner_product_helper<F: PrimeField>() {

        let mut rng = test_rng();
        let plonk_setup = PlonkSetup::<F>::new(5usize, &mut rng);

        let mut pb: Protoboard<F> = Protoboard::new();
        let n: usize = 10;
        let zero_var: Variable = Variable {name: "zero".to_string(), pb_index: 0};
        let mut inner_product: InnerProductComponent = InnerProductComponent::new(n);

        let x_vals: Vec<u128> = vec![0,1,2,3,4,5,6,7,8,9];
        let y_vals: Vec<u128> = vec![1,1,1,1,1,1,1,1,1,1];

        // declare variables on protoboard
        let mut input: Vec<Variable> = Vec::new(); input.resize(2*n, zero_var.clone());
        let mut output = zero_var.clone();

        for i in 0..2*n {
            pb.assign_index(&mut input[i]);
        }

        pb.assign_index(&mut output);

        // Attach the inner product gadget
        inner_product.attach(&mut pb, &input, &vec![output.clone()]);
        inner_product.generate_constraints(&mut pb);

        let (q_M, q_L, q_R, q_O, q_C, S_a, S_b, S_c, permutation) =
            pb.output_circuit_polynomials(&plonk_setup);

        // Generate witness
        for i in 0..n {
            pb.assign_val(&input[i], F::from(x_vals[i]));
            pb.assign_val(&input[i+n], F::from(y_vals[i]));
        }
        inner_product.generate_witness(&mut pb);

        // Print Variables and Check circuit satisfiability
        for i in 0..pb.pb_vals.len() {
            println!("Value of variable {} = {}", i, pb.pb_vals[i]);
        }
        println!("Circuit Satisfied = {}", pb.is_satisfied());
        println!("Number of constraints = {}", pb.n_constraints);

        let witness = pb.output_witness();
        for i in 0..witness.len() {
            println!("Wire {}:{}", i, witness[i]);
        }
    }


    fn test_simple_satisfiability_helper<E: PairingEngine>()
    {
        let mut pb: Protoboard<E::Fr> = Protoboard::new();

        // Encode the following circuit:
        // Inputs: x, y, z
        // Output: w
        // sq_x = x*x, sq_y = y*y, sq_z = z*z,
        // c_xy = x*y, c_yz = y*z, c_zx = z*x
        // sum_cross_1 = 2*c_xy + 2*c_yz
        // sum_cross = sum_cross_1 + 2*c_zx
        // sum_square_1 = sq_x + sq_y
        // sum_square = sum_square_1 + sq_z
        // w = sum_square + sum_cross

        let mut x: Variable = Variable::new("x");
        let mut y: Variable = Variable::new("y");
        let mut z: Variable = Variable::new("z");
        let mut w: Variable = Variable::new("w");

        // Internal variables
        let mut sq_x: Variable = Variable::new("");
        let mut sq_y: Variable = Variable::new("");
        let mut sq_z: Variable = Variable::new("");
        let mut c_xy: Variable = Variable::new("");
        let mut c_yz: Variable = Variable::new("");
        let mut c_zx: Variable = Variable::new("");
        let mut sum_cross_1: Variable = Variable::new("");
        let mut sum_square_1: Variable = Variable::new("");
        let mut sum_cross: Variable = Variable::new("");
        let mut sum_square: Variable = Variable::new("");

        // Assign variables
        pb.assign_index(&mut x);
        pb.assign_index(&mut y);
        pb.assign_index(&mut z);
        pb.assign_index(&mut w);
        pb.assign_index(&mut sq_x);
        pb.assign_index(&mut sq_y);
        pb.assign_index(&mut sq_z);
        pb.assign_index(&mut c_xy);
        pb.assign_index(&mut c_yz);
        pb.assign_index(&mut c_zx);
        pb.assign_index(&mut sum_cross_1);
        pb.assign_index(&mut sum_square_1);
        pb.assign_index(&mut sum_cross);
        pb.assign_index(&mut sum_square);

        // Generate constraints
        pb.add_multiplication_gate(&x, &x, &sq_x);
        pb.add_multiplication_gate(&y, &y, &sq_y);
        pb.add_multiplication_gate(&z, &z, &sq_z);
        pb.add_multiplication_gate(&x, &y, &c_xy);
        pb.add_multiplication_gate(&y, &z, &c_yz);
        pb.add_multiplication_gate(&z, &x, &c_zx);
        pb.add_addition_gate(&c_xy, &c_yz, &sum_cross_1, E::Fr::from(2u128), E::Fr::from(2u128), E::Fr::zero());
        pb.add_addition_gate(&c_zx, &sum_cross_1, &sum_cross, E::Fr::from(2u128), E::Fr::one(), E::Fr::zero());
        pb.add_addition_gate(&sq_x, &sq_y, &sum_square_1, E::Fr::one(), E::Fr::one(), E::Fr::zero());
        pb.add_addition_gate(&sq_z, &sum_square_1, &sum_square, E::Fr::one(), E::Fr::one(), E::Fr::zero());
        pb.add_addition_gate(&sum_cross, &sum_square, &w, E::Fr::one(), E::Fr::one(), E::Fr::zero());



        // Assign values
        pb.assign_val(&x, E::Fr::from(5u128));
        pb.assign_val(&y, E::Fr::from(3u128));
        pb.assign_val(&z, E::Fr::from(2u128));
        pb.assign_val(&c_xy, pb.val(&x) * pb.val(&y));
        pb.assign_val(&c_yz, pb.val(&y)*pb.val(&z));
        pb.assign_val(&c_zx, pb.val(&z) * pb.val(&x));
        pb.assign_val(&sq_x, pb.val(&x) * pb.val(&x));
        pb.assign_val(&sq_y, pb.val(&y) * pb.val(&y));
        pb.assign_val(&sq_z, pb.val(&z) * pb.val(&z));
        pb.assign_val(&sum_cross_1, pb.val(&c_xy) + pb.val(&c_xy) + pb.val(&c_yz) + pb.val(&c_yz));
        pb.assign_val(&sum_cross, pb.val(&sum_cross_1) + pb.val(&c_zx) + pb.val(&c_zx));
        pb.assign_val(&sum_square_1, pb.val(&sq_x) + pb.val(&sq_y));
        pb.assign_val(&sum_square, pb.val(&sum_square_1) + pb.val(&sq_z));
        pb.assign_val(&w, pb.val(&sum_square) + pb.val(&sum_cross));

        println!("The value of output w is {}", pb.val(&w).to_string());
        println!("Circuit satisfied {}", pb.is_satisfied());
    }

    fn test_witness_polynomials_helper<E: PairingEngine>()
    {
        let mut rng = test_rng();
        let srs_size: usize = 10;
        let N = 1usize << srs_size;
        let D: usize = 1usize << 12;
        let m = 1usize << 5;
        let max_degree = D;
        let k_domain_size: usize = 10;
        // Generate SRS for degree N
        let pp: PublicParameters<E> = PublicParameters::setup(&max_degree, &D, &m, &srs_size);
        let plonk_setup = PlonkSetup::<E::Fr>::new(srs_size, &mut rng);

        let mut pb: Protoboard<E::Fr> = Protoboard::new();
        let n: usize = N >> 3;
        let zero_var: Variable = Variable {name: "zero".to_string(), pb_index: 0};
        let mut inner_product: InnerProductComponent = InnerProductComponent::new(n);

        let x_vals: Vec<u128> = vec![1; n];
        let y_vals: Vec<u128> = vec![1; n];

        // declare variables on protoboard
        let mut input: Vec<Variable> = Vec::new(); input.resize(2*n, zero_var.clone());
        let mut output = zero_var.clone();

        for i in 0..2*n {
            pb.assign_index(&mut input[i]);
        }

        pb.assign_index(&mut output);

        // Attach the inner product gadget
        inner_product.attach(&mut pb, &input, &vec![output.clone()]);
        inner_product.generate_constraints(&mut pb);

        // Generate circuit polynomials for the prover

        let circuit: PlonkCircuitPolynomials<E::Fr> = compute_plonk_circuit_polynomials(&mut pb, &plonk_setup);
        let circuit_pp: PlonkCircuitKeys<E> = compute_plonk_circuit_keys(&circuit, &pp);

        // Generate witness
        for i in 0..n {
            pb.assign_val(&input[i], E::Fr::from(x_vals[i]));
            pb.assign_val(&input[i+n], E::Fr::from(y_vals[i]));
        }
        inner_product.generate_witness(&mut pb);

        println!("pb.satisfied() = {}", pb.is_satisfied());

        let mut start = Instant::now();
        let witness = pb.output_witness();
        //let (wa_poly, wb_poly, wc_poly, wa_com, wb_com, wc_com) = compute_witness_polynomials(&witness, &plonk_setup, &pp);
        println!("Time to generate witness: {}", start.elapsed().as_secs());

        // comnpute circuit witness polynomial
        //let cw_poly = (&circuit.q_M * &(&wa_poly * &wb_poly)).add(&circuit.q_L * &wa_poly).add(&circuit.q_R * &wb_poly).add(&circuit.q_O * &wc_poly).add(circuit.q_C.clone());
        //let (q_poly, _) = cw_poly.divide_by_vanishing_poly(plonk_setup.domain).unwrap();
        //let alpha = E::Fr::rand(&mut rng);

        //assert_eq!(cw_poly.evaluate(&alpha), q_poly.evaluate(&alpha) * plonk_setup.domain.evaluate_vanishing_polynomial(alpha), "Polynomial Identity not Satisfied");

        // To test plonk aggregation, we duplicate the witness K times
        // Now generate an aggregate proof (we will aggregate
        let K = 1usize << k_domain_size;
        let afg_pp = AFGSetup::<E>::new(k_domain_size, &mut rng);
        let mut agg_witness: Vec<Vec<E::Fr>> = Vec::new();
        for _ in 0..K {
            agg_witness.push(witness.clone());
        }

        /*
        println!("Generating PLONK Proofs");
        let mut start = Instant::now();
        let proof = (0..K).into_par_iter().map(|i| compute_plonk_proof(&circuit_pp, &circuit, &agg_witness[i], &plonk_setup, &pp)).collect::<Vec<_>>();
        println!("Time to generate proofs = {} secs", start.elapsed().as_secs());
        */


        println!("Generating Aggregated Proof");
        start = Instant::now();
        compute_aplonk_proof(k_domain_size, &circuit_pp, &circuit, &agg_witness, &plonk_setup, &pp, &afg_pp);
        println!("Time to generate aggregate proof = {} secs", start.elapsed().as_secs());

    }



}


