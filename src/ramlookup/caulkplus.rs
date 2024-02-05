// This file contains implementation of the Caulk+ scheme

use std::collections::HashSet;
use std::marker::PhantomData;
use std::ops::{Mul, MulAssign, Neg};
use ark_ec::{AffineCurve, PairingEngine, ProjectiveCurve};
use ark_ff::{Field, One, PrimeField, Zero};
use ark_msm::msm::VariableBaseMSM;
use ark_poly::{EvaluationDomain, Evaluations, GeneralEvaluationDomain, Polynomial, UVPolynomial};
use ark_poly::univariate::DensePolynomial;
use ark_std::{cfg_into_iter, UniformRand};
use crate::{CaulkTranscript, compute_vanishing_poly, fast_poly_evaluate, fast_poly_interpolate, field_dft, group_dft, KZGCommit, PublicParameters};
use rand::{Rng, RngCore};
use crate::multi::TableInput;



#[allow(non_snake_case)]
// CaulkPlus parameters on top of caulk Public Parameters
pub struct CaulkPlusPublicParams<E: PairingEngine> {
    pub z_h_com: E::G1Affine,                       // commitment to vanishing poly
    pub log_poly_com: E::G1Affine,                  // commitment to log polynomial
    pub log_poly: DensePolynomial<E::Fr>,           // log polynomial on h_domain
    pub openings_z_h_poly: Vec<E::G2Affine>,        // opening proofs for polynomial X^N - 1
    pub openings_log_poly: Vec<E::G2Affine>,        // opening proofs for log polynomial
    pub openings_mu_polys: Vec<E::G2Affine>,        // these are proofs for i^th lagrange poly at xi^i.
}

// CaulkPlus table related inputs, also includes pre-computed KZG proofs
pub struct CaulkPlusProverInput<E: PairingEngine> {
    pub t_com: E::G1Affine,                          // commitment to table
    pub t_poly: DensePolynomial<E::Fr>,             // polynomial interpolating the table on h_domain
    pub openings_t_poly: Vec<E::G2Affine>,          // opening proofs of the t-polynomial
}

// Committed index lookup instance
pub struct CaulkPlusLookupInstance<E: PairingEngine> {
    pub t_com: E::G1Affine,                         // commitment of the table
    pub a_com: E::G1Affine,                         // commitment of the a-vector (addresses)
    pub v_com: E::G1Affine,                         // commitment of v=t[a] vector
    pub m_domain_size: usize,                       // domain size of a vector
    pub h_domain_size: usize,                       // domain size of table
}

// Prover's input (witness) for an instance of committed index lookup
pub struct CiLookupProverInput<E: PairingEngine> {
    pub a_poly: DensePolynomial<E::Fr>,             // a polynomial
    pub v_poly: DensePolynomial<E::Fr>,             // v polynomial
    pub t_i_poly: DensePolynomial<E::Fr>,           // t_I polynomial
    pub l_i_poly: DensePolynomial<E::Fr>,           // l_I polynomial
    pub z_i_poly: DensePolynomial<E::Fr>,           // z_I polynomial
    pub h_poly: DensePolynomial<E::Fr>,             // h polynomial mapping
    pub z_i_poly_dvt: Vec<E::Fr>,                   // derivatives of z_i polynomial at set H_I
    pub i_vec: Vec<usize>,                          // indices involved
}

// Generated with respect to a pre-processed table.
pub struct CaulkPlusExample {
    pub a_vec: Vec<usize>,                          // lookup indices
    pub v_vec: Vec<usize>,                          // value vector v = t[a]
}

// Proof structure for committed index lookup
pub struct CommittedIndexLookupProof<E: PairingEngine> {
    pub t_i_com: E::G1Affine,                       // commitment to t_i poly
    pub l_i_com: E::G1Affine,                       // commitment to l_i poly
    pub z_i_com: E::G1Affine,                       // commitment to z_i poly
    pub q_com:  E::G1Affine,                        // commitment to quotient of composition poly
    pub h_com:  E::G1Affine,                        // commitment to h_poly (mapping poly)
    pub a_s: E::Fr,                                 // evaluation of a at s
    pub v_s: E::Fr,                                 // evaluation of v at s
    pub h_s: E::Fr,                                 // evaluation of h at s
    pub q_s: E::Fr,                                 // evaluation of q at s
    pub g_hs: E::Fr,                                // evaluation of g at h(s)
    pub g2_opening: E::G2Affine,                    // openings for "real" pairing checks
    pub pi_s:   E::G1Affine,                        // KZG proof for evaluations of polynomials at s
    pub pi_hs:    E::G1Affine,                      // KZG proof for evaluation of g at h(s)
}

pub fn compute_committed_index_lookup_proof<E: PairingEngine>(
    instance: &CaulkPlusLookupInstance<E>,          // instance of committed index lookup
    instance_input: &CiLookupProverInput<E>,        // instance specific witness/input
    table_pp: &CaulkPlusProverInput<E>,             // table-specific pre-computed inputs
    caulk_pp: &CaulkPlusPublicParams<E>,            // additional public params for Caulk+
    pp: &PublicParameters<E>,                       // KZG+Caulk public params
) -> CommittedIndexLookupProof<E> {
    let mut rng = ark_std::test_rng();
    let m_domain: GeneralEvaluationDomain<E::Fr> = GeneralEvaluationDomain::new(1 << instance.m_domain_size).unwrap();
    let h_domain: GeneralEvaluationDomain<E::Fr> = GeneralEvaluationDomain::new(1 << instance.h_domain_size).unwrap();

    // Round0: Add instance and first prover message to transcript
    let mut transcript: CaulkTranscript<E::Fr> = CaulkTranscript::new();
    transcript.append_element(b"t_com", &instance.t_com);
    transcript.append_element(b"a_com", &instance.a_com);
    transcript.append_element(b"v_com", &instance.v_com);

    // compute commitments to t_i, l_i,z_i and h polynomials
    let t_i_com = KZGCommit::<E>::commit_g1(&pp.poly_ck, &instance_input.t_i_poly);
    let l_i_com = KZGCommit::<E>::commit_g1(&pp.poly_ck, &instance_input.l_i_poly);
    let z_i_com = KZGCommit::<E>::commit_g1(&pp.poly_ck, &instance_input.z_i_poly);
    let h_com = KZGCommit::<E>::commit_g1(&pp.poly_ck, &instance_input.h_poly);
    transcript.append_element(b"t_i_com", &t_i_com);
    transcript.append_element(b"l_i_com", &l_i_com);
    transcript.append_element(b"z_i_com", &z_i_com);
    transcript.append_element(b"h_com", &h_com);

    let beta = transcript.get_and_append_challenge(b"ch_beta");

    // Round1: Prover sends commitment to the quotient: ((T_I + \beta.L_I + \beta^2 Z_I)(h(X)) - (v(X) + \beta a(X)))/Z_I(X)
    let g_poly = &instance_input.t_i_poly +
        &(&instance_input.l_i_poly.mul(beta) + &instance_input.z_i_poly.mul(beta.square()));
    let g1_poly = &instance_input.v_poly + &instance_input.a_poly.mul(beta);
    // compute composition polynomial g1(h(X))
    let domain_m_sq = GeneralEvaluationDomain::<E::Fr>::new(m_domain.size()*m_domain.size()).unwrap();
    let evals: Vec<E::Fr> = cfg_into_iter!(0..domain_m_sq.size())
        .map(|k| {
            g_poly.evaluate(
                &instance_input.h_poly.evaluate(&domain_m_sq.element(k)))
        })
        .collect();

    let g_h_poly =
        Evaluations::from_vec_and_domain(evals, domain_m_sq).interpolate();
    let temp_poly = &g_h_poly - &g1_poly;
    // compute quotient polynomial q by dividing by vanishing polynomial of m_domain
    let (q_poly, rem) = temp_poly.divide_by_vanishing_poly(m_domain).unwrap();

    assert_eq!(rem, DensePolynomial::<E::Fr>::zero(), "Z_V does not divide");
    // commit to the q polynomial
    let q_com = KZGCommit::<E>::commit_g1(&pp.poly_ck, &q_poly);
    transcript.append_element(b"q_com", &q_com);

    let s = transcript.get_and_append_challenge(b"eval_s");

    // Round2: Prover sends evaluations of polynomials
    // [a(s), v(s), h(s), q(s), g(h(s))]
    let a_s = instance_input.a_poly.evaluate(&s);
    let v_s = instance_input.v_poly.evaluate(&s);
    let h_s= instance_input.h_poly.evaluate(&s);
    let q_s = q_poly.evaluate(&s);
    let g_hs = g_poly.evaluate(&h_s);

    transcript.append_element(b"a_s", &a_s);
    transcript.append_element(b"v_s", &v_s);
    transcript.append_element(b"h_s", &h_s);
    transcript.append_element(b"q_s", &q_s);
    transcript.append_element(b"g_hs", &g_hs);

    let gamma = transcript.get_and_append_challenge(b"ch_gamma");
    let gamma_sq: E::Fr = gamma * gamma;
    let gamma_cube: E::Fr = gamma_sq * gamma;
    // The prover combines polynomials evaluated at s using gamma
    // P_s(X) = v(X) + \gamma a(X) + \gamma^2 h(X) + \gamma^3 q(X)
    let poly_p_s = &(&instance_input.v_poly + &instance_input.a_poly.mul(gamma)) +
        &(&instance_input.h_poly.mul(gamma_sq) + &q_poly.mul(gamma_cube));
    let (val_s, pi_s) = KZGCommit::<E>::open_g1_batch(
        &pp.poly_ck,
        &poly_p_s,
        None,
        &[s]
    );
    let (_, pi_hs) = KZGCommit::<E>::open_g1_batch(
        &pp.poly_ck,
        &g_poly,
        None,
        &[h_s]
    );

    assert_eq!(g_h_poly.evaluate(&s), g_hs, "Polynomial composition is incorrect");

    // now compute openings for the real pairing check
    // We compute opening (U - U_I) for the aggregated polynomial, U = (T + \beta L + \beta^2 Z_H)
    // First compute derivative of the Z_I polynomial, and evaluate it at the set H_I
    let mut g2_scalars: Vec<E::Fr> = Vec::new();
    let mut g2_openings: Vec<E::G2Affine> = Vec::new();
    let d = instance_input.z_i_poly.degree();
    g2_scalars.resize(3*d, E::Fr::zero());
    g2_openings.resize(3*d, E::G2Affine::zero());

    for i in 0..d {
        g2_scalars[i] = instance_input.z_i_poly_dvt[i].inverse().unwrap();
        g2_scalars[i+d] = g2_scalars[i].mul(beta);
        g2_scalars[i+d+d] = g2_scalars[i].mul(beta.square());
        g2_openings[i] = table_pp.openings_t_poly[instance_input.i_vec[i]];
        g2_openings[i+d] = caulk_pp.openings_log_poly[instance_input.i_vec[i]];
        g2_openings[i+d+d] = caulk_pp.openings_z_h_poly[instance_input.i_vec[i]];
    }

    let g2_scalars_bigint = g2_scalars.into_iter().map(|x| x.into_repr()).collect::<Vec<_>>();
    let g2_opening = ark_ec::msm::VariableBaseMSM::multi_scalar_mul(g2_openings.as_slice(), g2_scalars_bigint.as_slice());


    CommittedIndexLookupProof::<E> {
        t_i_com: t_i_com,
        l_i_com: l_i_com,
        z_i_com: z_i_com,
        q_com: q_com,
        h_com: h_com,
        a_s: a_s,
        v_s: v_s,
        h_s: h_s,
        q_s: q_s,
        g_hs: g_hs,
        g2_opening: g2_opening.into(),
        pi_s: pi_s,
        pi_hs: pi_hs,
    }
}

pub fn verify_committed_index_lookup_proof<E: PairingEngine>(
    instance: &CaulkPlusLookupInstance<E>,
    proof: &CommittedIndexLookupProof<E>,
    caulk_pp: &CaulkPlusPublicParams<E>,
    pp: &PublicParameters<E>,
) -> bool {
    let m_domain = GeneralEvaluationDomain::<E::Fr>::new(1 << instance.m_domain_size).unwrap();
    // initialize the caulk
    let mut transcript: CaulkTranscript<E::Fr> = CaulkTranscript::new();
    // add instance to the
    transcript.append_element(b"t_com", &instance.t_com);
    transcript.append_element(b"a_com", &instance.a_com);
    transcript.append_element(b"v_com", &instance.v_com);
    // add first prover message
    transcript.append_element(b"t_i_com", &proof.t_i_com);
    transcript.append_element(b"l_i_com", &proof.l_i_com);
    transcript.append_element(b"z_i_com", &proof.z_i_com);
    transcript.append_element(b"h_com", &proof.h_com);

    // derive challenge beta
    let beta = transcript.get_and_append_challenge(b"ch_beta");
    // add the second prover message consisting of commitment of q_poly to transcript
    transcript.append_element(b"q_com", &proof.q_com);
    // obtain the evaluation point
    let s = transcript.get_and_append_challenge(b"eval_s");
    // add the proof evaluations to the transcript
    transcript.append_element(b"a_s", &proof.a_s);
    transcript.append_element(b"v_s", &proof.v_s);
    transcript.append_element(b"h_s", &proof.h_s);
    transcript.append_element(b"q_s", &proof.q_s);
    transcript.append_element(b"g_hs", &proof.g_hs);

    // derive the challenge gamma
    let gamma = transcript.get_and_append_challenge(b"ch_gamma");
    let gamma_sq: E::Fr = gamma * gamma;
    let gamma_cube: E::Fr = gamma_sq * gamma;

    // verifier computes:
    // (i) commitment to polynomial g, for checking evaluation at h(s),
    // (ii) commitment to polynomial P_s, for checking evaluations at s.
    let g_com_1 = proof.t_i_com + proof.l_i_com.mul(beta).into_affine();
    let g_com_2 = proof.z_i_com.mul(beta.square()).into_affine();
    let g_com: E::G1Affine = g_com_1 + g_com_2;

    let p_com_1 = instance.v_com + instance.a_com.mul(gamma).into_affine();
    let p_com_2 = proof.h_com.mul(gamma_sq).into_affine() + proof.q_com.mul(gamma_cube).into_affine();
    let p_com: E::G1Affine = p_com_1 + p_com_2;

    let val_s = (proof.a_s + proof.v_s.mul(gamma)) + (proof.h_s.mul(gamma_sq) + proof.q_s.mul(gamma_cube));

    // verify kzg proofs
    let b_h = KZGCommit::<E>::verify_g1(&pp.poly_ck.powers_of_g, &pp.g2_powers, &g_com, None,
                                        &[proof.h_s], &[proof.g_hs], &proof.pi_hs);
    let b_p = KZGCommit::<E>::verify_g1(&pp.poly_ck.powers_of_g, &pp.g2_powers, &p_com, None,
                                             &[s], &[val_s], &proof.pi_s);

    // check the polynomial identity
    let lhs: E::Fr = proof.q_s * m_domain.evaluate_vanishing_polynomial(s);
    let rhs: E::Fr = (proof.g_hs + proof.v_s.neg()) + proof.a_s.mul(beta).neg();
    let b_c = (lhs == rhs);

    // check the "real" pairing check e([U]-[U_I], [1])=e([Z_I], opening)
    let u1_com:E::G1Affine = instance.t_com + proof.t_i_com.neg();
    let u2_com:E::G1Affine = caulk_pp.log_poly_com + proof.l_i_com.neg();
    let u_com:E::G1Affine = (u1_com + u2_com.mul(beta).into_affine()) + caulk_pp.z_h_com.mul(beta.square()).into_affine();
    let g2 = pp.g2_powers[0];
    let b_opening = (E::pairing(u_com, g2) == E::pairing(proof.z_i_com, proof.g2_opening));

    b_h & b_p & b_c & b_opening
}


impl<E: PairingEngine> CaulkPlusProverInput<E> {
    // store the prover input in a file
    pub fn store(&self, h_domain_size: usize) {
        let path = format!(
            "polys/poly_{}_openings_{}_{}.setup",
            "tbl",
            1usize << h_domain_size,
            E::Fq::size_in_bits()
        );


        let table: TableInput<E> = TableInput {
            c_poly: self.t_poly.clone(),
            c_com: self.t_com.clone(),
            openings: self.openings_t_poly.clone()
        };
        table.store(&path);

    }

    // load prover input from a file
    pub fn load(h_domain_size: usize) -> CaulkPlusProverInput<E> {
        let path = format!(
            "polys/poly_{}_openings_{}_{}.setup",
            "tbl",
            1usize << h_domain_size,
            E::Fq::size_in_bits()
        );


        let table = TableInput::<E>::load(&path);

        CaulkPlusProverInput {
            t_com: table.c_com,
            t_poly: table.c_poly,
            openings_t_poly: table.openings
        }
    }
}

// helpful functions for storing/generating caulkplus public parameters
impl<E: PairingEngine> CaulkPlusPublicParams<E> {
    
    pub fn store(&self) {

        let path_z_h = format!(
            "polys/poly_{}_openings_{}_{}.setup",
            "z_h",
            self.log_poly.degree()+1,
            E::Fq::size_in_bits()
        );

        let path_log_poly = format!(
            "polys/poly_{}_openings_{}_{}.setup",
            "log_poly",
            self.log_poly.degree()+1,
            E::Fq::size_in_bits()
        );

        let path_mu_polys = format!(
            "polys/poly_{}_openings_{}_{}.setup",
            "mu_poly",
            self.log_poly.degree()+1,
            E::Fq::size_in_bits()
        );



        let table_z_h: TableInput<E> = TableInput {
            c_com: self.z_h_com.clone(),
            c_poly: Default::default(),
            openings: self.openings_z_h_poly.clone()
        };

        let table_log_poly: TableInput<E> = TableInput {
            c_com: self.log_poly_com.clone(),
            c_poly: self.log_poly.clone(),
            openings: self.openings_log_poly.clone()
        };

        let table_mu_poly: TableInput<E> = TableInput {
            c_com: E::G1Affine::zero(),
            c_poly: Default::default(),
            openings: self.openings_mu_polys.clone(),
        };

        table_z_h.store(&path_z_h);
        table_log_poly.store(&path_log_poly);
        table_mu_poly.store(&path_mu_polys);

    }
    
    pub fn load(domain_size_bits: usize) -> CaulkPlusPublicParams<E> {
        let domain_size: usize = 1 << domain_size_bits;
        let path_z_h = format!(
            "polys/poly_{}_openings_{}_{}.setup",
            "z_h",
            domain_size,
            E::Fq::size_in_bits()
        );

        let path_log_poly = format!(
            "polys/poly_{}_openings_{}_{}.setup",
            "log_poly",
            domain_size,
            E::Fq::size_in_bits()
        );

        let path_mu_polys = format!(
            "polys/poly_{}_openings_{}_{}.setup",
            "mu_poly",
            domain_size,
            E::Fq::size_in_bits()
        );


        let table_z_h: TableInput<E> = TableInput::load(&path_z_h);
        let table_log_poly: TableInput<E> = TableInput::load(&path_log_poly);
        let table_mu_poly: TableInput<E> = TableInput::load(&path_mu_polys);

        CaulkPlusPublicParams::<E> {
            z_h_com: table_z_h.c_com,
            log_poly_com: table_log_poly.c_com,
            log_poly: table_log_poly.c_poly,
            openings_z_h_poly: table_z_h.openings,
            openings_log_poly: table_log_poly.openings,
            openings_mu_polys: table_mu_poly.openings,
        }
    }

    pub fn new(
        pp: &PublicParameters<E>,
        h_domain_size: usize
    ) -> CaulkPlusPublicParams<E> {
        let h_domain: GeneralEvaluationDomain<E::Fr> = GeneralEvaluationDomain::new(1 << h_domain_size).unwrap();
        // commit to the vanishing polynomial
        let z_h_com:E::G1Affine = pp.poly_ck.powers_of_g[h_domain.size()] + pp.poly_ck.powers_of_g[0].neg();
        let mut l_i_vec: Vec<E::Fr> = Vec::new();
        for i in 0..h_domain.size() {
            l_i_vec.push(E::Fr::from(i as u128));
        }
        let log_poly = DensePolynomial::from_coefficients_vec(h_domain.ifft(&l_i_vec));
        let log_poly_com = KZGCommit::<E>::commit_g1(&pp.poly_ck, &log_poly);

        // above does not work for Z_H openings as Z_H has degree = domain size.
        // Z_H/(X-w) = X^{N-1} + wX^{N-2}+...+w^{N-1}
        // Define h(X) = [s_{N-1}] + [s_{N-2}].X + ... + [1].X^{N-1}
        let mut h_vec_g: Vec<E::G2Projective> = Vec::new();
        for i in (0..h_domain.size()).rev() {
            h_vec_g.push(pp.g2_powers[i].into_projective());
        }
        let openings_z_h_projective = group_dft::<E::Fr, _>(&h_vec_g, h_domain_size);
        let openings_z_h_poly: Vec<E::G2Affine> =
            openings_z_h_projective.iter().map(|x| x.into_affine()).collect();

        // compute openings of poly mu_i(X) at xi^i.
        let mut p_vec: Vec<E::G2Projective> = Vec::new();

        for i in (0..h_domain.size()).rev() {
            let scalar = E::Fr::from((h_domain.size()-1-i) as u128);
            p_vec.push(pp.g2_powers[i].mul(scalar));
        }


        let openings_mu_polys_projective = group_dft::<E::Fr, _>(&p_vec, h_domain_size);
        let N_inv = E::Fr::from(h_domain.size() as u128).inverse().unwrap();
        let openings_mu_polys: Vec<E::G2Affine> =
            openings_mu_polys_projective.iter().map(|x| x.into_affine().mul(N_inv).into_affine()).collect();


        let openings_log_poly = KZGCommit::<E>::multiple_open::<E::G2Affine>(
            &log_poly,
            &pp.g2_powers,
            h_domain_size
        );

        CaulkPlusPublicParams::<E> {
            z_h_com,
            log_poly_com,
            log_poly,
            openings_z_h_poly,
            openings_log_poly,
            openings_mu_polys,
        }

    }

    pub fn new_fake(
        pp: &PublicParameters<E>,
        h_domain_size: usize
    ) -> CaulkPlusPublicParams<E> {
        let h_domain: GeneralEvaluationDomain<E::Fr> = GeneralEvaluationDomain::new(1 << h_domain_size).unwrap();
        // commit to the vanishing polynomial
        let z_h_com:E::G1Affine = pp.poly_ck.powers_of_g[h_domain.size()] + pp.poly_ck.powers_of_g[0].neg();
        let mut l_i_vec: Vec<E::Fr> = Vec::new();
        for i in 0..h_domain.size() {
            l_i_vec.push(E::Fr::from(i as u128));
        }
        let log_poly = DensePolynomial::from_coefficients_vec(h_domain.ifft(&l_i_vec));
        let log_poly_com = KZGCommit::<E>::commit_g1(&pp.poly_ck, &log_poly);

        // compute powers of beta for fake parameters generation
        let mut rng = ark_std::test_rng();
        let beta = E::Fr::rand(&mut rng);
        let mut powers: Vec<E::Fr> = Vec::new();
        let mut power = E::Fr::one();
        for i in 0..pp.g2_powers.len() {
            powers.push(power);
            power.mul_assign(beta);
        }
        let g2 = pp.g2_powers[0];
        // -------------- Created powers of beta in srs for fake (faster) setup ------------

        // (1). Compute openings for Z_H
        // Z_H/(X-w) = X^{N-1} + wX^{N-2}+...+w^{N-1}
        // Define h(X) = s_{N-1} + s_{N-2}.X + ... + 1.X^{N-1} for s=beta
        let mut h_vec_g: Vec<E::Fr> = Vec::new();
        for i in (0..h_domain.size()).rev() {
            h_vec_g.push(powers[i]);
        }
        let openings_z_h_vec = field_dft::<E::Fr>(&h_vec_g, h_domain_size);
        // G2 encode the powers of beta and batch normalize to affine
        let mut q3: Vec<E::G2Projective> = Vec::new();
        for i in 0..openings_z_h_vec.len() {
            q3.push(g2.mul(openings_z_h_vec[i]));
        }
        let openings_z_h_poly = E::G2Projective::batch_normalization_into_affine(q3.as_ref());

        // (2) compute openings of poly mu_i(X) at xi^i.
        let mut p_vec: Vec<E::Fr> = Vec::new();
        for i in (0..h_domain.size()).rev() {
            let scalar = E::Fr::from((h_domain.size()-1-i) as u128);
            p_vec.push(powers[i].mul(scalar));
        }
        let openings_mu_polys_ff = field_dft::<E::Fr>(&p_vec, h_domain_size);
        let N_inv = E::Fr::from(h_domain.size() as u128).inverse().unwrap();
        let openings_mu_polys: Vec<E::G2Affine> =
            openings_mu_polys_ff.iter().map(|x| g2.mul(x.mul(N_inv)).into_affine()).collect();

        let openings_log_poly = KZGCommit::<E>::multiple_open_fake::<E::G2Affine>(
            &log_poly,
            powers.as_slice(),
            g2,
            h_domain_size
        );

        CaulkPlusPublicParams::<E> {
            z_h_com,
            log_poly_com,
            log_poly,
            openings_z_h_poly,
            openings_log_poly,
            openings_mu_polys,
        }

    }


}

// helper function to generate table specific parameters for the prover
// inputs:
// @t_vec: the table vector
// @pp: public parameters containing srs of sufficient size for the table
pub fn generate_caulkplus_prover_input<E: PairingEngine>(
    t_vec: &Vec<usize>,
    pp: &PublicParameters<E>,
    h_domain_size: usize,
) -> CaulkPlusProverInput<E> {
    let N: usize = t_vec.len();
    assert_eq!(N, 1usize << h_domain_size);

    let h_domain: GeneralEvaluationDomain<E::Fr> = GeneralEvaluationDomain::new(N).unwrap();
    let mut t_vec_ff: Vec<E::Fr> = Vec::new();
    for i in 0..t_vec.len() {
        t_vec_ff.push(E::Fr::from(t_vec[i] as u128));
    }
    let t_poly = DensePolynomial::from_coefficients_vec(h_domain.ifft(&t_vec_ff));
    let t_com = KZGCommit::<E>::commit_g1(&pp.poly_ck, &t_poly);

    // create powers of beta
    let mut rng = ark_std::test_rng();
    let beta = E::Fr::rand(&mut rng);
    let mut powers: Vec<E::Fr> = Vec::new();
    let mut power = E::Fr::one();
    for i in 0..pp.g2_powers.len() {
        powers.push(power);
        power.mul_assign(beta);
    }


    let openings_t_poly = KZGCommit::<E>::multiple_open_fake::<E::G2Affine>(
        &t_poly,
        powers.as_slice(),
        pp.g2_powers[0],
        h_domain_size
    );

    CaulkPlusProverInput {
        t_com,
        t_poly,
        openings_t_poly,
    }
}

// helper function to generate example instances
pub fn generate_committed_lookup_example<E: PairingEngine>(
    t_vec: &Vec<usize>,
    m_domain_size: usize,
) -> CaulkPlusExample {
    let mut rng = ark_std::test_rng();
    let m = 1usize << m_domain_size;

    // for benchmarking, we will generate a vector to consist of distinct elements
    // this allows set I also to be power of 2, making interpolation algorithms simpler.
    // Same complexity can be obtained for non-power of two, but implementation is slightly
    // more involved.

    let mut a_vec: Vec<usize> = Vec::new();
    let mut v_vec: Vec<usize> = Vec::new();
    for i in 0..m {
        let idx: usize = usize::rand(&mut rng) % t_vec.len();
        a_vec.push(idx);
    }

    // now we collect unique values in a, and brute force extend it to size m
    a_vec = a_vec.clone().into_iter().collect::<HashSet::<_>>().into_iter().collect();
    for i in a_vec.len()..m {
        let mut found: bool = false;
        while !found {
            let extra = usize::rand(&mut rng) % t_vec.len();
            if !a_vec.contains(&extra) {
                a_vec.push(extra);
                found = true;
            }
        }
    }

    for i in 0..a_vec.len() {
        v_vec.push(t_vec[a_vec[i]]);
    }

    CaulkPlusExample {
        a_vec,
        v_vec
    }
}

// function to generate prover witness for an instance/example
pub fn compute_lookup_prover_input<E: PairingEngine>(
    t_vec: &Vec<usize>,
    example: &CaulkPlusExample,
) -> CiLookupProverInput<E> {
    let mut rng = ark_std::test_rng();
    let mut i_vec = example.a_vec.clone();

    let h_domain: GeneralEvaluationDomain<E::Fr> = GeneralEvaluationDomain::new(t_vec.len()).unwrap();
    let m_domain: GeneralEvaluationDomain<E::Fr> = GeneralEvaluationDomain::new(example.a_vec.len()).unwrap();

    let mut h_i_vec: Vec<E::Fr> = Vec::new();
    let mut t_i_vec: Vec<E::Fr> = Vec::new();
    let mut l_i_vec: Vec<E::Fr> = Vec::new();
    let mut i_ff_vec: Vec<E::Fr> = Vec::new();
    let mut a_ff_vec: Vec<E::Fr> = Vec::new();
    let mut v_ff_vec: Vec<E::Fr> = Vec::new();

    for i in 0..i_vec.len() {
        i_ff_vec.push(E::Fr::from(i_vec[i] as u128));
        h_i_vec.push(h_domain.element(i_vec[i]));
        t_i_vec.push(E::Fr::from(t_vec[i_vec[i]] as u128));
        l_i_vec.push(E::Fr::from(i_vec[i] as u128));
    }

    let mut h_val_vec: Vec<E::Fr> = Vec::new();
    for i in 0..m_domain.size() {
        h_val_vec.push(h_domain.element(example.a_vec[i]));
        a_ff_vec.push(E::Fr::from(example.a_vec[i] as u128));
        v_ff_vec.push(E::Fr::from(example.v_vec[i] as u128));
    }

    let z_i_poly = compute_vanishing_poly(&h_i_vec, 1);
    let t_i_poly = fast_poly_interpolate(&h_i_vec, &t_i_vec);
    let l_i_poly = fast_poly_interpolate(&h_i_vec, &l_i_vec);
    let h_poly = DensePolynomial::from_coefficients_vec(m_domain.ifft(&h_val_vec));
    let a_poly = DensePolynomial::from_coefficients_vec(m_domain.ifft(&a_ff_vec));
    let v_poly = DensePolynomial::from_coefficients_vec(m_domain.ifft(&v_ff_vec));

    // compute derivative polynomial of
    let mut z_poly_dv_coeffs: Vec<E::Fr> = Vec::new();
    for i in 0usize..z_i_poly.degree() {
        z_poly_dv_coeffs.push(E::Fr::from((i+1) as u128)*z_i_poly.coeffs[i+1]);
    }
    //let z_dv_poly = DensePolynomial::from_coefficients_vec(z_poly_dv_coeffs);
    let evaluations = fast_poly_evaluate(&z_poly_dv_coeffs, &h_i_vec);

    CiLookupProverInput {
        a_poly,
        v_poly,
        t_i_poly,
        l_i_poly,
        z_i_poly,
        h_poly,
        z_i_poly_dvt: evaluations,
        i_vec,
    }

}


#[cfg(test)]
mod tests {
    use std::ops::{Mul, Neg};
    use std::time::Instant;
    use super::*;
    use ark_bls12_381::Bls12_381;
    use ark_ff::{Field, PrimeField};
    use ark_bls12_381::Fr;
    use ark_ec::{AffineCurve, ProjectiveCurve};
    use ark_poly::{GeneralEvaluationDomain, Polynomial};
    use crate::multi::generate_lookup_input;

    const h_domain_size: usize = 22;
    const m_domain_size: usize = 11;


    #[test]
    pub fn test_committed_index_lookup_proof()
    {
        test_committed_index_lookup_proof_helper::<Bls12_381>();
    }

    #[test]
    pub fn test_construct_prover_input()
    {
        test_construct_prover_input_helper::<Bls12_381>();
    }

    #[test]
    pub fn test_generate_caulkplus_prover_input()
    {
        test_generate_caulkplus_prover_input_helper::<Bls12_381>();
    }

    #[test]
    pub fn test_caulk_public_params()
    {
        test_caulkplus_public_params_helper::<Bls12_381>();
    }

    fn test_committed_index_lookup_proof_helper<E: PairingEngine>()
    {
        let N: usize = 1 << h_domain_size;
        let m: usize = 1 << m_domain_size;
        let n = h_domain_size;
        let max_degree = N;

        let pp: PublicParameters<E> = PublicParameters::setup(&max_degree, &N, &m, &n);
        let mut t_vec: Vec<usize> = Vec::new();
        for i in 0..N {
            t_vec.push(i);
        }
        // load caulk plus public parameters
        let caulk_pp = CaulkPlusPublicParams::<E>::load(h_domain_size);
        // generate table specific setup
        //let table_pp = generate_caulkplus_prover_input(&t_vec, &pp, h_domain_size);
        let table_pp = CaulkPlusProverInput::<E>::load(h_domain_size);

        //let table_pp = CaulkPlusProverInput::load(h_domain_size);
        // generate an example instance
        let example = generate_committed_lookup_example::<E>(&t_vec, m_domain_size);
        // generate instance input for the prover
        let instance_input: CiLookupProverInput<E> = compute_lookup_prover_input(&t_vec, &example);
        // commit to a_poly and v_poly
        let a_com = KZGCommit::<E>::commit_g1(&pp.poly_ck, &instance_input.a_poly);
        let v_com = KZGCommit::<E>::commit_g1(&pp.poly_ck, &instance_input.v_poly);

        let instance = CaulkPlusLookupInstance::<E> {
            t_com: table_pp.t_com,
            a_com: a_com,
            v_com: v_com,
            m_domain_size: m_domain_size,
            h_domain_size: h_domain_size,
        };

        let mut start = Instant::now();
        let proof = compute_committed_index_lookup_proof(
            &instance,
            &instance_input,
            &table_pp,
            &caulk_pp,
            &pp
        );
        println!("Generated committed index lookup proof in {} secs", start.elapsed().as_millis());
        let res = verify_committed_index_lookup_proof(
            &instance,
            &proof,
            &caulk_pp,
            &pp
        );

        println!("Verification result [{}]", res);
    }


    fn test_construct_prover_input_helper<E: PairingEngine>()
    {
        let N: usize = 1 << h_domain_size;
        let m: usize = 1 << m_domain_size;

        let mut t_vec: Vec<usize> = Vec::new();
        for i in 0..N {
            t_vec.push(i);
        }

        let h_domain = GeneralEvaluationDomain::<E::Fr>::new(N).unwrap();
        let m_domain = GeneralEvaluationDomain::<E::Fr>::new(m).unwrap();

        let example = generate_committed_lookup_example::<E>(&t_vec,m_domain_size);
        let input: CiLookupProverInput<E> = compute_lookup_prover_input(&t_vec,&example);
        let a_vec = example.a_vec;
        let v_vec = example.v_vec;
        let (a_poly, v_poly, t_i_poly, l_i_poly, z_i_poly, h_poly) = (
            input.a_poly,
            input.v_poly,
            input.t_i_poly,
            input.l_i_poly,
            input.z_i_poly,
            input.h_poly
        );

        for i in 0..m_domain.size() {
            assert_eq!(a_poly.evaluate(&m_domain.element(i)), E::Fr::from(a_vec[i] as u128), "a_poly interpolation failed");
            assert_eq!(v_poly.evaluate(&m_domain.element(i)), E::Fr::from(v_vec[i] as u128), "v_poly interpolation failed");
            assert_eq!(h_poly.evaluate(&m_domain.element(i)), h_domain.element(a_vec[i]), "h_poly interpolation failed");
        }

        for i in 0..a_vec.len() {
            assert_eq!(t_i_poly.evaluate(&h_domain.element(a_vec[i])), E::Fr::from(t_vec[a_vec[i]] as u128), "t_i_poly_error");
            assert_eq!(l_i_poly.evaluate(&h_domain.element(a_vec[i])), E::Fr::from(a_vec[i] as u128), "l_i_poly_error");
        }
    }

    fn test_generate_caulkplus_prover_input_helper<E: PairingEngine>()
    {
        //let h_domain_size: usize = 10;
        let N: usize = 1 << h_domain_size;
        let m = 1usize << m_domain_size;
        let n = h_domain_size;
        let max_degree = N;

        let pp: PublicParameters<E> = PublicParameters::setup(&max_degree, &N, &m, &n);
        let mut t_vec: Vec<usize> = Vec::new();
        for i in 0..N {
            t_vec.push(i);
        }

        let mut start = Instant::now();
        let cp_prover_input = generate_caulkplus_prover_input(
            &t_vec,
            &pp,
            h_domain_size
        );
        println!("Time to generate table inputs = {}", start.elapsed().as_secs());

        // check t_poly correctly interpolates t_vec
        let h_domain: GeneralEvaluationDomain<E::Fr> = GeneralEvaluationDomain::new(1usize << h_domain_size).unwrap();
        let mut t_evals: Vec<E::Fr> = Vec::new();
        for i in 0..t_vec.len() {
            t_evals.push(E::Fr::from(t_vec[i] as u128));
        }

        // check openings
        let t_com = cp_prover_input.t_com;
        let g1 = pp.poly_ck.powers_of_g[0];
        let g1x = pp.poly_ck.powers_of_g[1];
        let g2 = pp.g2_powers[0];
        for i in 0..N {
            assert_eq!(E::pairing(t_com + g1.mul(t_evals[i]).neg().into_affine(), g2),
                       E::pairing(g1x + g1.mul(h_domain.element(i)).neg().into_affine(), cp_prover_input.openings_t_poly[i]));
        }


    }

    fn test_caulkplus_public_params_helper<E: PairingEngine>()
    {
        let N: usize = 1 << h_domain_size;
        let m = 1usize << m_domain_size;
        let n = h_domain_size;
        let max_degree = N;

        let pp: PublicParameters<E> = PublicParameters::setup(&max_degree, &N, &m, &n);
        let caulk_pp = CaulkPlusPublicParams::<E>::new_fake(&pp, h_domain_size);
        caulk_pp.store();
        //let caulk_pp: CaulkPlusPublicParams<E> = CaulkPlusPublicParams::load(h_domain_size);

        // do sanity check on the correctness of openings
        let h_domain: GeneralEvaluationDomain<E::Fr> = GeneralEvaluationDomain::new(1 << h_domain_size).unwrap();
        let mut rng = ark_std::test_rng();
        let g1 = pp.poly_ck.powers_of_g[0];
        let g1x = pp.poly_ck.powers_of_g[1];
        let g2 = pp.g2_powers[0];

        for i in 0usize..1000 {
            let w = usize::rand(&mut rng) % N;
            // real check for Z_H(X)=(X-w).opening[w]
            assert_eq!(E::pairing(caulk_pp.z_h_com, g2),
                E::pairing(g1x + g1.mul(h_domain.element(w)).into_affine().neg(), caulk_pp.openings_z_h_poly[w]));
            // real check for log_poly
            assert_eq!(E::pairing(caulk_pp.log_poly_com + g1.mul(E::Fr::from(w as u128)).neg().into_affine(), g2),
                       E::pairing(g1x + g1.mul(h_domain.element(w)).neg().into_affine(), caulk_pp.openings_log_poly[w]));

            // check openings for mu polys
            let N_inv = E::Fr::from(N as u128).inverse().unwrap();
            let factor = N_inv.mul(h_domain.element(w));
            let mu_poly_com = caulk_pp.openings_z_h_poly[w].mul(factor).into_affine();
            assert_eq!(E::pairing(g1, mu_poly_com + g2.neg()),
                        E::pairing(g1x + g1.mul(h_domain.element(w)).neg().into_affine(), caulk_pp.openings_mu_polys[w]));
        }

    }
}






