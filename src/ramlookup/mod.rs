pub mod caulkplus;
mod fastupdate;
mod cq;
mod rampoly;

use std::marker::PhantomData;
use std::ops::{AddAssign, Div, Mul, MulAssign, Neg, Sub};
use ark_ec::{AffineCurve, PairingEngine, ProjectiveCurve};
use ark_ff::{BigInteger, FftField, Field, One, PrimeField, Zero};
use ark_poly::{univariate::DensePolynomial, EvaluationDomain, GeneralEvaluationDomain};
use ark_poly_commit::{kzg10, Polynomial, UVPolynomial};
use ark_poly_commit::kzg10::{Proof, VerifierKey};
use ark_std::{log2, test_rng, time::Instant, UniformRand};
use merlin::Transcript;
use crate::{multi::{
    compute_lookup_proof, get_poly_and_g2_openings, verify_lookup_proof, LookupInstance,
    LookupProverInput,
}, KZGCommit, PublicParameters, CaulkTranscript, compute_vanishing_poly};
use rand::{Rng, RngCore};
use crate::ramlookup::cq::{compute_cq_proof, CqExample, CqLookupInstance, CqProof, CqProverInput, CqPublicParams};

/**
 * RAM related structures corresponding to description in Sections 4 and 5 of https://eprint.iacr.org/2024/840.pdf
 * RAM related structures:-
 *  - CommittedRAM models a RAM with address and value columns
 *  - OperationBatch models operation sequence with three columns operation type, address, value
 *  - RAMTranscript models transcript assembled from RAM states and operation batch. Consists of four columns (timestamp, operation type, address, value)
 *  - RAMTranscriptCom models commitment to the RAMTranscript object
 */
pub struct CommittedRAM<E: PairingEngine> {
    pub a_poly: DensePolynomial<E::Fr>,         // polynomial denoting address column
    pub v_poly: DensePolynomial<E::Fr>,         // polynomial denoting value column
}

pub struct OperationBatch<E: PairingEngine> {
    pub op_poly: DensePolynomial<E::Fr>,        // polynomial denoting operation type column
    pub a_poly: DensePolynomial<E::Fr>,         // polynomial denoting address column
    pub v_poly: DensePolynomial<E::Fr>,         // polynomial denoting value column
}

pub struct RAMTranscript<E: PairingEngine> {
    pub ts_poly: DensePolynomial<E::Fr>,        // polynomial denoting timestamp column
    pub op_poly: DensePolynomial<E::Fr>,        // polynomial denoting operation column
    pub a_poly: DensePolynomial<E::Fr>,         // polynomial denoting address column
    pub v_poly: DensePolynomial<E::Fr>,         // polynomial denoting value column
}

#[derive(Clone, Debug)]
pub struct RAMTranscriptCom<E: PairingEngine> {
    pub ts_poly_com: E::G1Affine,
    pub op_poly_com: E::G1Affine,
    pub a_poly_com: E::G1Affine,
    pub v_poly_com: E::G1Affine,
}

/**
 * ------------------------------------------------ Utility Functions ----------------------------------
 *
 */

// Generate random field vector of size vec_size
pub fn generate_random_vector<E: PairingEngine, R: RngCore>(
    vec_size: usize,
    rng: &mut R,
) -> Vec<E::Fr> {
    let mut res: Vec<E::Fr> = Vec::new();
    for i in 0..vec_size {
        res.push(E::Fr::from(u128::rand(rng) % 100));
    }
    res
}

// Given a polynomial A(X), and k, outputs polynomial A(\omega X) - A(X)
// where omega is k^th root of unity
pub fn compute_shifted_difference<E: PairingEngine>(
    a_poly: &DensePolynomial<E::Fr>,
    k_domain_size: usize,
) -> DensePolynomial<E::Fr> {
    let k = 1usize << k_domain_size;
    let k_domain: GeneralEvaluationDomain<E::Fr> = GeneralEvaluationDomain::new(k).unwrap();
    let d = a_poly.degree();

    let mut coeffs_aw: Vec<E::Fr> = Vec::new();
    for i in 0..=d {
        coeffs_aw.push(a_poly.coeffs[i].mul(k_domain.element(i).sub(E::Fr::one())));
    }

    DensePolynomial::from_coefficients_vec(coeffs_aw)
}

// Given polynomial A(X) and scalar gamma, outputs the polynomial \gamma A(X)
pub fn compute_scaled_polynomial<E: PairingEngine>(
    a_poly: &DensePolynomial<E::Fr>,
    gamma: E::Fr,
) -> DensePolynomial<E::Fr>
{
    let mut scaled_coeffs: Vec<E::Fr> = Vec::new();
    for i in 0..a_poly.coeffs.len() {
        scaled_coeffs.push(a_poly.coeffs[i].mul(gamma));
    }

    DensePolynomial::from_coefficients_vec(scaled_coeffs)
}

// Compute polynomials Q1 and Q2 as detailed in the protocol in
// Figure 8 in the paper https://eprint.iacr.org/2024/840.pdf
pub fn compute_q1_and_q2_poly<E: PairingEngine>(
    a_poly: &DensePolynomial<E::Fr>,
    t_poly: &DensePolynomial<E::Fr>,
    v_poly: &DensePolynomial<E::Fr>,
    op_poly: &DensePolynomial<E::Fr>,
    delta_A_poly: &DensePolynomial<E::Fr>,
    delta_T_poly: &DensePolynomial<E::Fr>,
    z1_poly: &DensePolynomial<E::Fr>,
    z2_poly: &DensePolynomial<E::Fr>,
    gamma: E::Fr,
    k_domain_size: usize,
) -> (DensePolynomial<E::Fr>, DensePolynomial<E::Fr>)
{
    let dA_poly:DensePolynomial<E::Fr> = compute_shifted_difference::<E>(&a_poly, k_domain_size);
    let dT_poly: DensePolynomial<E::Fr> = compute_shifted_difference::<E>(&t_poly, k_domain_size);
    let dV_poly: DensePolynomial<E::Fr> = compute_shifted_difference::<E>(&v_poly, k_domain_size);
    let dOp_poly: DensePolynomial<E::Fr> = compute_shifted_difference::<E>(&op_poly, k_domain_size);

    let gamma_sq = gamma.square();
    let dA_dash_poly:DensePolynomial<E::Fr> = dA_poly.sub(delta_A_poly);
    let q1_poly = dA_dash_poly.div(z1_poly);

    assert_eq!(dA_dash_poly, z1_poly.mul(&q1_poly), "Division failed");

    let dT_dash_poly: DensePolynomial<E::Fr> = dT_poly.sub(delta_T_poly);
    let poly_one: DensePolynomial<E::Fr> = DensePolynomial::from_coefficients_vec(vec![E::Fr::one()]);
    let op_dash_poly:DensePolynomial<E::Fr> = &dOp_poly.sub(&poly_one) + op_poly;
    let num_poly: DensePolynomial<E::Fr> = compute_scaled_polynomial::<E>(&dT_dash_poly, gamma);
    let op_dV_poly: DensePolynomial<E::Fr> = &op_dash_poly * &dV_poly;
    let op_dV_poly = compute_scaled_polynomial::<E>(&op_dV_poly, gamma_sq);
    let mut numerator_q2 = dA_poly.clone();
    numerator_q2 = &numerator_q2 + &num_poly;
    numerator_q2 = &numerator_q2 + &op_dV_poly;
    let q2_poly = numerator_q2.div(z2_poly);

    (q1_poly, q2_poly)
}

// Given polynomial vector (p_0(X),...,p_{k-1}(X)) and scalar r
// outputs the polynomial \sum_{i=0}^{k-1} r^i p_i(X)
fn compute_aggregate_poly<E: PairingEngine>(
    poly_vec: &[DensePolynomial<E::Fr>],
    r: <E as PairingEngine>::Fr
) -> DensePolynomial<E::Fr> {
    let mut ch = E::Fr::one();
    let mut agg_poly = DensePolynomial::<E::Fr>::zero();
    for i in 0..poly_vec.len() {
        let scaled_poly = compute_scaled_polynomial::<E>(&poly_vec[i], ch);
        agg_poly.add_assign(&scaled_poly);
        ch.mul_assign(r);
    }
    agg_poly
}

/**
 * Pre-processed parameters for constructing/verifying lookup proofs
 *
 */
pub struct ProverInputCommon<E: PairingEngine> {
    pub t_poly: DensePolynomial<E::Fr>,         // last pre-processed RAM table
    pub l_poly: DensePolynomial<E::Fr>,         // log-polynomial
    pub zh_poly: DensePolynomial<E::Fr>,        // vanishing polynomial X^N - 1
    pub t_poly_openings: Vec<E::G2Affine>,      // pre-computed openings for t_poly
    pub l_poly_openings: Vec<E::G2Affine>,      // pre-computed openings for l_poly
    pub zh_poly_openings: Vec<E::G2Affine>,     // pre-computed openings for domain_n
}


pub struct VerifierInputCommon<E: PairingEngine> {
    pub poly_vk: VerifierKey<E>,                // KZG verification key
    pub z_com: E::G1Affine,                     // Commitment to poly (X-1)..(X-w^{m-1}) where w^{4m}=1
    pub domain_m_size: usize,                   // size of domain m
    pub domain_k_size: usize,                   // size of domain k=4m
    pub domain_n_size: usize,                   // size of big RAM domain
}


/**
 * ---------------------------- Objects for Concatenation Protocol ----------------------------
 * ConcatProverInput - prover's input to construct proof for concatenation
 * ConcatExample - for creating examples
 * ConcatInstance - an instance of concatenation relation
 * ProofConcat - proof of concatenation
 */
#[allow(non_snake_case)]
pub struct ConcatProverInput<E: PairingEngine> {
    pub a_poly: DensePolynomial<E::Fr>,         // interpolates vector a over V
    pub v_poly: DensePolynomial<E::Fr>,         // interpolates vector b over V

    pub op_bar_poly: DensePolynomial<E::Fr>,    // interpolates op bar over V
    pub a_bar_poly: DensePolynomial<E::Fr>,     // interpolates vector a_bar over V
    pub v_bar_poly: DensePolynomial<E::Fr>,     // interpolates vector v_bar over K

    pub a_dash_poly: DensePolynomial<E::Fr>,    // interpolates a_dash over V
    pub v_dash_poly: DensePolynomial<E::Fr>,    // interpolates v_dash over V

    pub Op_poly: DensePolynomial<E::Fr>,        // interpolates Op vector over K
    pub A_poly: DensePolynomial<E::Fr>,         // interpolates A vector over K
    pub V_poly: DensePolynomial<E::Fr>,         // interpolates V vector over K
}

#[allow(non_snake_case)]
#[derive(Clone, Debug)]
pub struct ConcatExample<E: PairingEngine> {
    pub a_vec: Vec<E::Fr>,
    pub v_vec: Vec<E::Fr>,

    pub op_bar_vec: Vec<E::Fr>,
    pub a_bar_vec: Vec<E::Fr>,
    pub v_bar_vec: Vec<E::Fr>,

    pub a_dash_vec: Vec<E::Fr>,
    pub v_dash_vec: Vec<E::Fr>,

    pub Op_vec: Vec<E::Fr>,
    pub A_vec: Vec<E::Fr>,
    pub V_vec: Vec<E::Fr>,
}

#[allow(non_snake_case)]
impl<E: PairingEngine> ConcatExample<E> {

    pub fn new(m_domain_size: usize) -> Self {
        let mut rng = ark_std::test_rng();
        let m = 1 << m_domain_size;
        let mut zero_vec: Vec<E::Fr> = Vec::new();
        zero_vec.resize(m, E::Fr::zero());
        let a_vec = generate_random_vector::<E, _>(m, &mut rng);
        let a_bar_vec = generate_random_vector::<E, _>(m, &mut rng);
        let a_dash_vec = generate_random_vector::<E, _>(m, &mut rng);
        let v_vec = generate_random_vector::<E, _>(m, &mut rng);
        let v_bar_vec = generate_random_vector::<E, _>(m, &mut rng);
        let v_dash_vec = generate_random_vector::<E, _>(m, &mut rng);
        let op_bar_vec = generate_random_vector::<E, _>(m, &mut rng);
        let A_vec = vec![a_vec.clone(), a_vec.clone(), a_bar_vec.clone(), a_dash_vec.clone()].concat();
        let V_vec = vec![v_vec.clone(), v_vec.clone(), v_bar_vec.clone(), v_dash_vec.clone()].concat();
        let Op_vec = vec![zero_vec.clone(), zero_vec.clone(), op_bar_vec.clone(), zero_vec.clone()].concat();

        ConcatExample {
            a_vec,
            v_vec,
            op_bar_vec,
            a_bar_vec,
            v_bar_vec,
            a_dash_vec,
            v_dash_vec,
            Op_vec,
            A_vec,
            V_vec,

        }
    }

    pub fn display(&self) {
        for i in 0..self.a_vec.len() {
            println!("{} {} {}", 0, self.a_vec[i].into_repr(), self.v_vec[i].into_repr());
        }
        println!("-------------");
        for i in 0..self.a_bar_vec.len() {
            println!("{} {} {}", self.op_bar_vec[i].into_repr(), self.a_bar_vec[i].into_repr(), self.v_bar_vec[i].into_repr());
        }
        println!("-------------");
        for i in 0..self.a_dash_vec.len() {
            println!("{} {} {}", 0, self.a_dash_vec[i].into_repr(), self.v_dash_vec[i].into_repr());
        }
    }
}

#[allow(non_snake_case)]
pub struct ConcatInstance<E: PairingEngine> {
    pub a_com: E::G1Affine,
    pub v_com: E::G1Affine,

    pub op_bar_com: E::G1Affine,
    pub a_bar_com: E::G1Affine,
    pub v_bar_com: E::G1Affine,

    pub a_dash_com: E::G1Affine,
    pub v_dash_com: E::G1Affine,

    pub Op_com: E::G1Affine,
    pub A_com: E::G1Affine,
    pub V_com: E::G1Affine,

    pub m_domain_size: usize,
}

pub struct ProofConcat<E: PairingEngine> {
    pub q_com: E::G1Affine,             // Commitment to polynomial Q
    pub v_h: E::Fr,                     // value of H at s^4
    pub v_g: E::Fr,                     // value of G at s
    pub v_g1: E::Fr,                    // Value of G at w^m s
    pub v_g2: E::Fr,                    // value of G at w^{2m} s
    pub v_g3: E::Fr,                    // value of G at w^{3m} s
    pub v_z: E::Fr,                     // value of Z at s
    pub v_q: E::Fr,                     // value of q at s
    pub pi_h: E::G1Affine,              // proof for H(s^4)=v_h
    pub pi_g: E::G1Affine,              // proof for evaluations of G
    pub pi_z: E::G1Affine,              // proof for evaluation of z
    pub pi_q: E::G1Affine,              // proof for evaluation of q
}

// Generate proof of concatenation of vectors
// Implements the protocol in Figure 7 of the paper https://eprint.iacr.org/2024/840.pdf
// However, instead of proving concatenation x = a||b||c for input vectors a,b and c, the code
// below proves concatenation x = a||a||b||c for input a,b,c. This allows the concatenated vector
// to be interpolated over smooth subgroup of F. The modification does not affect memory consistency.
pub fn compute_concat_proof<E: PairingEngine>(
    instance: &ConcatInstance<E>,
    input: &ConcatProverInput<E>,
    pp: &PublicParameters<E>,
) -> Option<ProofConcat<E>>
{
    let mut proof: Option<ProofConcat<E>> = None;
    let k_domain_size = instance.m_domain_size + 2;
    let m_domain: GeneralEvaluationDomain<E::Fr> = GeneralEvaluationDomain::new(1 << instance.m_domain_size).unwrap();
    let k_domain: GeneralEvaluationDomain<E::Fr> = GeneralEvaluationDomain::new(1 << k_domain_size).unwrap();

    // Round0: Calculate the Z(X)=(X-1)...(X-w^{m-1}) polynomial (this will eventually be pre-computed)
    let mut k_domain_vec: Vec<E::Fr> = Vec::new();
    for i in 0..m_domain.size() {
        k_domain_vec.push(k_domain.element(i))
    }
    // The second argument is unused in the function.
    let z_poly = compute_vanishing_poly::<E::Fr>(&k_domain_vec, 0);

    // Round1: Add commitments to the transcript
    let mut transcript = CaulkTranscript::<E::Fr>::new();
    transcript.append_element(b"a_com", &instance.a_com);
    transcript.append_element(b"v_com", &instance.v_com);

    transcript.append_element(b"op_bar_com", &instance.op_bar_com);
    transcript.append_element(b"a_bar_com", &instance.a_bar_com);
    transcript.append_element(b"v_bar_com", &instance.v_bar_com);

    transcript.append_element(b"a_dash_com", &instance.a_dash_com);
    transcript.append_element(b"v_dash_com", &instance.v_dash_com);

    transcript.append_element(b"Op_com", &instance.Op_com);
    transcript.append_element(b"A_com", &instance.A_com);
    transcript.append_element(b"V_com", &instance.V_com);

    let beta = transcript.get_and_append_challenge(b"beta");
    let gamma = transcript.get_and_append_challenge(b"gamma");
    let gamma_square = gamma.square();
    let gamma_cube: E::Fr = gamma_square * gamma;

    // Round2
    // Compute polynomials g1, g2, g3 representing column aggregation
    let g1_poly = &input.a_poly + &input.v_poly.mul(beta);
    let g2_poly = &input.a_bar_poly + &(&input.v_bar_poly.mul(beta) + &input.op_bar_poly.mul(beta.square()));
    let g3_poly = &input.a_dash_poly + &input.v_dash_poly.mul(beta);
    let mut g_poly = &input.A_poly + &(&input.V_poly.mul(beta) + &input.Op_poly.mul(beta.square()));

    // Calculate H polynomial = (1+\gamma)G_1(X) + \gamma^2 G_2(X) + \gamma^3 G_3(X)
    let h_poly_1 = &g1_poly + &g1_poly.mul(gamma);
    let h_poly_2 = &g2_poly.mul(gamma_square) + &g3_poly.mul(gamma_cube);
    let mut h_poly = &h_poly_1 + &h_poly_2;

    g_poly.coeffs.resize(k_domain.size(), E::Fr::zero());
    h_poly.coeffs.resize(m_domain.size(), E::Fr::zero());

    // compute polynomials H(X^4), G(\omega^m X), G(\omega^{2m} X), G(\omega^{3m} X)
    let mut h4_poly_coeffs: Vec<E::Fr> = Vec::new();
    let mut g_omega_m_coeffs: Vec<E::Fr> = Vec::new();
    let mut g_omega_2m_coeffs: Vec<E::Fr> = Vec::new();
    let mut g_omega_3m_coeffs: Vec<E::Fr> = Vec::new();
    // these polynomials are defined over k_domain
    h4_poly_coeffs.resize(k_domain.size(), E::Fr::zero());
    g_omega_m_coeffs.resize(k_domain.size(), E::Fr::zero());
    g_omega_2m_coeffs.resize(k_domain.size(), E::Fr::zero());
    g_omega_3m_coeffs.resize(k_domain.size(), E::Fr::zero());

    for i in 0..m_domain.size() {
        h4_poly_coeffs[4*i] = h_poly.coeffs[i];
    }

    for i in 0..k_domain.size() {
        g_omega_m_coeffs[i] = k_domain.element((i*m_domain.size()) % k_domain.size()) * g_poly.coeffs[i];
        g_omega_2m_coeffs[i] = k_domain.element((2*i*m_domain.size()) % k_domain.size()) * g_poly.coeffs[i];
        g_omega_3m_coeffs[i] = k_domain.element((3*i*m_domain.size()) % k_domain.size()) * g_poly.coeffs[i];
    }
    let h4_poly = DensePolynomial::from_coefficients_vec(h4_poly_coeffs);
    let g_omega_m_poly = DensePolynomial::from_coefficients_vec(g_omega_m_coeffs);
    let g_omega_2m_poly = DensePolynomial::from_coefficients_vec(g_omega_2m_coeffs);
    let g_omega_3m_poly = DensePolynomial::from_coefficients_vec(g_omega_3m_coeffs);

    // strip away leading zeroes from h and g polynomials
    h_poly = DensePolynomial::from_coefficients_vec(h_poly.coeffs);
    g_poly = DensePolynomial::from_coefficients_vec(g_poly.coeffs);

    // compute q polynomial
    let g_agg_poly = &(&g_poly + &g_omega_m_poly.mul(gamma)) +
        &(&g_omega_2m_poly.mul(gamma_square) + &g_omega_3m_poly.mul(gamma_cube));
    let q_poly = &(&h4_poly - &g_agg_poly) / &z_poly;

    // Commit to q polynomial and add the commitment to transcript
    let q_com = KZGCommit::commit_g1(&pp.poly_ck, &q_poly);
    transcript.append_element(b"q_com", &q_com);

    let s = transcript.get_and_append_challenge(b"s_eval");
    let m = m_domain.size();
    println!("Eval point prover: {}", s);
    let s4: E::Fr = s*s*s*s;
    let p_g = vec![s, k_domain.element(m)*s, k_domain.element(2*m)*s, k_domain.element(3*m)*s];
    let g_com = KZGCommit::commit_g1(&pp.poly_ck, &g_poly);

    let (evals_h, pi_h) = KZGCommit::open_g1_batch(&pp.poly_ck, &h_poly, None, &[s4]);
    let (evals_g, pi_g) = KZGCommit::open_g1_batch(&pp.poly_ck, &g_poly, None, &p_g);
    let (evals_z, pi_z) = KZGCommit::open_g1_batch(&pp.poly_ck, &z_poly, None, &[s]);
    let (evals_q, pi_q) = KZGCommit::open_g1_batch(&pp.poly_ck, &q_poly, None, &[s]);

    assert_eq!(evals_z[0]*evals_q[0],
               evals_h[0] - evals_g[0] - gamma*evals_g[1] - gamma_square*evals_g[2] - gamma_cube*evals_g[3]);

    proof = Some(ProofConcat {
        q_com: q_com,
        v_h: evals_h[0],
        v_g: evals_g[0],
        v_g1: evals_g[1],
        v_g2: evals_g[2],
        v_g3: evals_g[3],
        v_z: evals_z[0],
        v_q: evals_q[0],
        pi_g: pi_g,
        pi_h: pi_h,
        pi_q: pi_q,
        pi_z: pi_z
    });

    proof
}

// verify proof of concatenation according to protocol in Fig 7 of
// the paper https://eprint.iacr.org/2024/840.pdf
pub fn verify_concat_proof<E: PairingEngine>(
    instance: &ConcatInstance<E>,
    proof: &ProofConcat<E>,
    pp: &PublicParameters<E>,
) -> bool {
    let mut status: bool = false;
    let k_domain_size = instance.m_domain_size + 2;
    let m = 1usize << instance.m_domain_size;
    let k = 1 << k_domain_size;

    let k_domain = GeneralEvaluationDomain::<E::Fr>::new(k).unwrap();

    // Compute commitment to z polynomial
    // @todo This will be pre-computed eventually
    let mut k_domain_vec: Vec<E::Fr> = Vec::new();
    for i in 0..m {
        k_domain_vec.push(k_domain.element(i))
    }
    let z_poly = compute_vanishing_poly::<E::Fr>(&k_domain_vec, 0);
    let z_com = KZGCommit::commit_g1(&pp.poly_ck, &z_poly);

    // initialize empty transcript
    let mut transcript = CaulkTranscript::<E::Fr>::new();
    // add the instance commitments to transcript
    transcript.append_element(b"a_com", &instance.a_com);
    transcript.append_element(b"v_com", &instance.v_com);

    transcript.append_element(b"op_bar_com", &instance.op_bar_com);
    transcript.append_element(b"a_bar_com", &instance.a_bar_com);
    transcript.append_element(b"v_bar_com", &instance.v_bar_com);

    transcript.append_element(b"a_dash_com", &instance.a_dash_com);
    transcript.append_element(b"v_dash_com", &instance.v_dash_com);

    transcript.append_element(b"Op_com", &instance.Op_com);
    transcript.append_element(b"A_com", &instance.A_com);
    transcript.append_element(b"V_com", &instance.V_com);

    let beta = transcript.get_and_append_challenge(b"beta");
    let gamma = transcript.get_and_append_challenge(b"gamma");
    let gamma_square = gamma.square();
    let gamma_cube: E::Fr = gamma_square * gamma;
    let beta_square: E::Fr = beta.square();

    // verifier computes commitments to h and g polynomials
    let g1_com: E::G1Affine = instance.a_com + instance.v_com.mul(beta).into_affine();
    let g2_com: E::G1Affine = instance.a_bar_com + instance.v_bar_com.mul(beta).into_affine() + instance.op_bar_com.mul(beta_square).into_affine();
    let g3_com: E::G1Affine = instance.a_dash_com + instance.v_dash_com.mul(beta).into_affine();
    let h_com: E::G1Affine = g1_com + g1_com.mul(gamma).into_affine() + g2_com.mul(gamma_square).into_affine() + g3_com.mul(gamma_cube).into_affine();
    let g_com: E::G1Affine = instance.A_com + instance.V_com.mul(beta).into_affine() + instance.Op_com.mul(beta_square).into_affine();

    // add the commitment q_com to transcript to obtain evaluation point
    transcript.append_element(b"q_com", &proof.q_com);
    let s = transcript.get_and_append_challenge(b"s_eval");

    // verify evaluation proofs
    let b_h = KZGCommit::<E>::verify_g1(&pp.poly_ck.powers_of_g, &pp.g2_powers, &h_com, None,
                                        &[s*s*s*s], &[proof.v_h], &proof.pi_h);
    let b_g = KZGCommit::<E>::verify_g1(&pp.poly_ck.powers_of_g, &pp.g2_powers, &g_com, None,
                                        &[s, k_domain.element(m)*s, k_domain.element(2*m)*s, k_domain.element(3*m)*s],
                                        &[proof.v_g, proof.v_g1, proof.v_g2, proof.v_g3], &proof.pi_g);
    let b_q = KZGCommit::<E>::verify_g1(&pp.poly_ck.powers_of_g, &pp.g2_powers, &proof.q_com, None,
                                        &[s], &[proof.v_q], &proof.pi_q);
    let b_z = KZGCommit::<E>::verify_g1(&pp.poly_ck.powers_of_g, &pp.g2_powers, &z_com, None,
                                        &[s], &[proof.v_z], &proof.pi_z);

    status = b_h & b_g & b_q & b_z;
    status
}

/**
 * ---------------------------- Objects for Proving Monotonicity of RAM Transcript ----------------------------
 * MonotonicTranscriptInstance - generates instance of monotonic transcript relation
 * MonotonicTranscriptExample - generates example of monotonic transcript
 * ProofMonotonic - proof of monotonicity of committed transcript
 * MonotonicProverInput - auxiliary information needed by prover to construct the proof.
 */
pub struct MonotonicTranscriptInstance<E: PairingEngine> {
    pub tr_com: RAMTranscriptCom<E>,
    pub m_domain_size: usize,
    pub h_domain_size: usize,
}

#[allow(non_snake_case)]
pub struct MonotonicTranscriptExample<E: PairingEngine> {
    pub a_vec: Vec<usize>,
    pub v_vec: Vec<usize>,
    pub a_dash_vec: Vec<usize>,
    pub v_dash_vec: Vec<usize>,
    pub op_vec: Vec<usize>,
    pub a_bar_vec: Vec<usize>,
    pub v_bar_vec: Vec<usize>,
    pub A_ast_vec: Vec<usize>,
    pub V_ast_vec: Vec<usize>,
    pub T_ast_vec: Vec<usize>,
    pub Op_ast_vec: Vec<usize>,
    pub tr: RAMTranscript<E>,
    pub addr_tr: RAMTranscript<E>,
    pub tr_com: RAMTranscriptCom<E>,
    pub addr_tr_com: RAMTranscriptCom<E>,
    pub m_domain_size: usize,
    pub h_domain_size: usize,
}

#[allow(non_snake_case)]
impl <E: PairingEngine> MonotonicTranscriptExample<E> {
    pub fn new(m_domain_size: usize, h_domain_size:usize, pp: &PublicParameters<E>) -> Self {
        let m = 1usize << m_domain_size;
        let k = 4*m;
        let N = 1usize << h_domain_size;

        let m_domain = GeneralEvaluationDomain::<E::Fr>::new(m).unwrap();
        let k_domain = GeneralEvaluationDomain::<E::Fr>::new(k).unwrap();

        let mut table: Vec<usize> = Vec::new();
        let mut rng = ark_std::test_rng();
        let range_max: usize = 10000;

        for _ in 0..N {
            table.push(usize::rand(&mut rng) % range_max);
        }

        let mut a_vec: Vec<usize> = Vec::new();
        let mut v_vec: Vec<usize> = Vec::new();
        let mut op_vec: Vec<usize> = Vec::new();
        let mut v_bar_vec: Vec<usize> = Vec::new();

        // initial sub-ram
        for _ in 0..m {
            let k = usize::rand(&mut rng) % N;
            a_vec.push(k);
            v_vec.push(table[k]);
        }

        // operations
        for i in 0..m {
            let op = usize::rand(&mut rng) % 2;
            op_vec.push(op);

            let v = if op == 0 {
                table[a_vec[i]]
            } else {
                usize::rand(&mut rng) % range_max
            };

            v_bar_vec.push(v);
            table[a_vec[i]] = v;
        }

        // final ram
        let mut v_dash_vec: Vec<usize> = Vec::new();
        for i in 0..m {
            v_dash_vec.push(table[a_vec[i]]);
        }

        // concatenated vectors
        let zero_vec = vec![0usize;m];
        let A_vec = vec![a_vec.clone(), a_vec.clone(), a_vec.clone(), a_vec.clone()].concat();
        let V_vec = vec![v_vec.clone(), v_vec.clone(), v_bar_vec.clone(), v_dash_vec.clone()].concat();
        let Op_vec = vec![zero_vec.clone(), zero_vec.clone(), op_vec.clone(), zero_vec.clone()].concat();
        let T_vec: Vec<usize> = (0..k).collect();

        let mut sort_vec: Vec<u64> = Vec::new();
        for i in 0..k {
            let key = (m as u64)*(A_vec[i] as u64) + (T_vec[i] as u64);
            sort_vec.push(key);
        }

        let perm = permutation::sort(&sort_vec);
        let A_ast_vec = perm.apply_slice(&A_vec);
        let T_ast_vec = perm.apply_slice(&T_vec);
        let Op_ast_vec = perm.apply_slice(&Op_vec);
        let V_ast_vec = perm.apply_slice(&V_vec);

        // Convert vectors to field vectors to commit.
        let A_vec_ff = A_vec.iter().map(|x| E::Fr::from(*x as u128)).collect::<Vec<_>>();
        let V_vec_ff = V_vec.iter().map(|x| E::Fr::from(*x as u128)).collect::<Vec<_>>();
        let Op_vec_ff = Op_vec.iter().map(|x| E::Fr::from(*x as u128)).collect::<Vec<_>>();
        let T_vec_ff = T_vec.iter().map(|x| E::Fr::from(*x as u128)).collect::<Vec<_>>();

        let A_ast_vec_ff = A_ast_vec.iter().map(|x| E::Fr::from(*x as u128)).collect::<Vec<_>>();
        let V_ast_vec_ff = V_ast_vec.iter().map(|x| E::Fr::from(*x as u128)).collect::<Vec<_>>();
        let Op_ast_vec_ff = Op_ast_vec.iter().map(|x| E::Fr::from(*x as u128)).collect::<Vec<_>>();
        let T_ast_vec_ff = T_ast_vec.iter().map(|x| E::Fr::from(*x as u128)).collect::<Vec<_>>();

        let ts_poly = DensePolynomial::from_coefficients_vec(k_domain.ifft(&T_vec_ff));
        let a_poly = DensePolynomial::from_coefficients_vec(k_domain.ifft(&A_vec_ff));
        let v_poly = DensePolynomial::from_coefficients_vec(k_domain.ifft(&V_vec_ff));
        let op_poly = DensePolynomial::from_coefficients_vec(k_domain.ifft(&Op_vec_ff));

        let ts_ast_poly = DensePolynomial::from_coefficients_vec(k_domain.ifft(&T_ast_vec_ff));
        let a_ast_poly = DensePolynomial::from_coefficients_vec(k_domain.ifft(&A_ast_vec_ff));
        let v_ast_poly = DensePolynomial::from_coefficients_vec(k_domain.ifft(&V_ast_vec_ff));
        let op_ast_poly = DensePolynomial::from_coefficients_vec(k_domain.ifft(&Op_ast_vec_ff));

        let ts_poly_com = KZGCommit::<E>::commit_g1(&pp.poly_ck, &ts_poly);
        let a_poly_com = KZGCommit::<E>::commit_g1(&pp.poly_ck, &a_poly);
        let v_poly_com = KZGCommit::<E>::commit_g1(&pp.poly_ck, &v_poly);
        let op_poly_com = KZGCommit::<E>::commit_g1(&pp.poly_ck, &op_poly);

        let ts_ast_poly_com = KZGCommit::<E>::commit_g1(&pp.poly_ck, &ts_ast_poly);
        let a_ast_poly_com = KZGCommit::<E>::commit_g1(&pp.poly_ck, &a_ast_poly);
        let v_ast_poly_com = KZGCommit::<E>::commit_g1(&pp.poly_ck, &v_ast_poly);
        let op_ast_poly_com = KZGCommit::<E>::commit_g1(&pp.poly_ck, &op_ast_poly);

        MonotonicTranscriptExample::<E> {
            a_vec: a_vec.clone(),
            v_vec: v_vec,
            a_dash_vec: a_vec.clone(),
            v_dash_vec: v_dash_vec,
            op_vec: op_vec,
            a_bar_vec: a_vec,
            v_bar_vec: v_bar_vec,
            A_ast_vec: A_ast_vec,
            V_ast_vec: V_ast_vec,
            T_ast_vec: T_ast_vec,
            Op_ast_vec: Op_ast_vec,
            tr: RAMTranscript {
                ts_poly: ts_poly,
                op_poly: op_poly,
                a_poly: a_poly,
                v_poly: v_poly,
            },
            addr_tr: RAMTranscript {
                ts_poly: ts_ast_poly,
                op_poly: op_ast_poly,
                a_poly: a_ast_poly,
                v_poly: v_ast_poly,
            },
            tr_com: RAMTranscriptCom {
                ts_poly_com: ts_poly_com,
                op_poly_com: op_poly_com,
                a_poly_com: a_poly_com,
                v_poly_com: v_poly_com,
            },
            addr_tr_com: RAMTranscriptCom {
                ts_poly_com: ts_ast_poly_com,
                op_poly_com: op_ast_poly_com,
                a_poly_com: a_ast_poly_com,
                v_poly_com: v_ast_poly_com,
            },
            m_domain_size,
            h_domain_size,
        }
    }

    pub fn display(&self) {
        let k = 4 * (1usize << self.m_domain_size);
        println!(" TS | OP | A | V");

        for i in 0..k {
            println!(" {} | {} | {} | {} ",
                     self.T_ast_vec[i], self.Op_ast_vec[i], self.A_ast_vec[i], self.V_ast_vec[i]
            );

        }
    }
}

#[allow(non_snake_case)]
pub struct ProofMonotonic<E: PairingEngine> {
    pub z1_com: E::G1Affine,
    pub z2_com: E::G1Affine,
    pub delta_A_com: E::G1Affine,
    pub delta_T_com: E::G1Affine,
    pub q1_com: E::G1Affine,
    pub q2_com: E::G1Affine,

    pub val_A_s: E::Fr,
    pub val_A_ws: E::Fr,
    pub val_deltaA_s: E::Fr,
    pub val_deltaT_s: E::Fr,
    pub val_T_s: E::Fr,
    pub val_T_ws: E::Fr,
    pub val_op_ws: E::Fr,
    pub val_V_s: E::Fr,
    pub val_V_ws: E::Fr,
    pub val_Q1_s: E::Fr,
    pub val_Q2_s: E::Fr,
    pub val_Z1_s: E::Fr,
    pub val_Z2_s: E::Fr,

    pub pi_s: E::G1Affine,
    pub pi_ws: E::G1Affine,

    pub range_proof_A: CqProof<E>,
    pub range_proof_deltaA: CqProof<E>,
    pub range_proof_deltaT: CqProof<E>,
    pub range_proof_t: CqProof<E>
}

#[allow(non_snake_case)]
pub struct ProofMonotonicProverInput<E: PairingEngine> {
    pub set_I1: Vec<usize>,
    pub set_I2: Vec<usize>,
    pub z1_poly: DensePolynomial<E::Fr>,
    pub z2_poly: DensePolynomial<E::Fr>,
    pub delta_A_vec: Vec<usize>,
    pub delta_T_vec: Vec<usize>,
    pub delta_A_poly: DensePolynomial<E::Fr>,
    pub delta_T_poly: DensePolynomial<E::Fr>,
}

// The function generates the inputs needed for proof from
// the example for a monotonic transcript
#[allow(non_snake_case)]
pub fn generate_monotonic_prover_input<E: PairingEngine>(
    example: &MonotonicTranscriptExample<E>,
    pp: &PublicParameters<E>
) -> ProofMonotonicProverInput<E>
{
    let m_domain_size = example.m_domain_size;
    let k_domain_size = m_domain_size + 2;
    let k = 1usize << k_domain_size;

    let mut vec_I1: Vec<usize> = Vec::new();
    let mut vec_I2: Vec<usize> = Vec::new();
    let mut delta_A_vec: Vec<usize> = Vec::new();
    let mut delta_T_vec: Vec<usize> = Vec::new();

    // compute sets I1 and I2
    for i in 0..k-1 {
        if example.A_ast_vec[i] != example.A_ast_vec[i+1] {
            vec_I1.push(i);
            assert_eq!(example.A_ast_vec[i+1] > example.A_ast_vec[i], true, "Wrong transcript (address)");
            delta_A_vec.push(example.A_ast_vec[i+1] - example.A_ast_vec[i]);
            delta_T_vec.push(0);
        } else {
            vec_I2.push(i);
            assert_eq!(example.T_ast_vec[i+1] > example.T_ast_vec[i], true, "Wrong transcript (time)");
            delta_A_vec.push(0);
            delta_T_vec.push(example.T_ast_vec[i+1] - example.T_ast_vec[i]);
        }
    }

    // set the final entry of these vectors to 0. It is not used in the checks.
    delta_A_vec.push(0);
    delta_T_vec.push(0);
    assert_eq!(delta_A_vec.len(), k, "Wrong length: delta_A_vec");
    assert_eq!(delta_T_vec.len(), k, "Wrong length: delta_T_vec");

    let i1_len = vec_I1.len();
    let i2_len = vec_I2.len();

    let k_domain: GeneralEvaluationDomain<E::Fr> = GeneralEvaluationDomain::new(k).unwrap();

    // compute field vectors from integer vectors
    let mut vec_I1_ff = vec_I1.iter().map(|x| k_domain.element(*x)).collect::<Vec<_>>();
    let mut vec_I2_ff = vec_I2.iter().map(|x| k_domain.element(*x)).collect::<Vec<_>>();
    let delta_A_vec_ff = delta_A_vec.iter().map(|x| E::Fr::from(*x as u128)).collect::<Vec<_>>();
    let delta_T_vec_ff = delta_T_vec.iter().map(|x| E::Fr::from(*x as u128)).collect::<Vec<_>>();

    // resize to power of 2 for vanishing polynomial computation.
    vec_I1_ff.resize(k, E::Fr::zero());
    vec_I2_ff.resize(k, E::Fr::zero());

    let extra_I1 = k - i1_len;
    let extra_I2 = k - i2_len;

    // compute vanishing polynomials
    let mut z1_poly = compute_vanishing_poly(&vec_I1_ff, 1);
    let mut z2_poly = compute_vanishing_poly(&vec_I2_ff, 1);
    let delta_A_poly = DensePolynomial::from_coefficients_vec(k_domain.ifft(&delta_A_vec_ff));
    let delta_T_poly = DensePolynomial::from_coefficients_vec(k_domain.ifft(&delta_T_vec_ff));

    assert_eq!(z1_poly.degree(), k, "Incorrect degree z1_poly");
    assert_eq!(z2_poly.degree(), k, "Incorrect degree z2_poly");

    let mut coeffs_z1: Vec<E::Fr> = Vec::new();
    let mut coeffs_z2: Vec<E::Fr> = Vec::new();

    for i in 0..=i1_len {
        coeffs_z1.push(z1_poly.coeffs[i+extra_I1]);
    }

    for i in 0..=i2_len {
        coeffs_z2.push(z2_poly.coeffs[i+extra_I2]);
    }

    z1_poly = DensePolynomial::from_coefficients_vec(coeffs_z1);
    z2_poly = DensePolynomial::from_coefficients_vec(coeffs_z2);

    ProofMonotonicProverInput::<E> {
        set_I1: vec_I1,
        set_I2: vec_I2,
        z1_poly: z1_poly,
        z2_poly: z2_poly,
        delta_A_vec: delta_A_vec,
        delta_T_vec: delta_T_vec,
        delta_A_poly: delta_A_poly,
        delta_T_poly: delta_T_poly,
    }
}

// Compute proof for monotonic transcript instance
#[allow(non_snake_case)]
pub fn compute_monotonic_proof<E: PairingEngine>(
    instance: &MonotonicTranscriptInstance<E>,
    example: &MonotonicTranscriptExample<E>,
    input: &ProofMonotonicProverInput<E>,
    pp: &PublicParameters<E>
) -> ProofMonotonic<E> {

    let m_domain_size = instance.m_domain_size;
    let h_domain_size = instance.h_domain_size;
    let k_domain_size = instance.m_domain_size + 2;

    let m = 1usize << m_domain_size;
    let k = 1usize << k_domain_size;

    let m_domain: GeneralEvaluationDomain<E::Fr> = GeneralEvaluationDomain::new(m).unwrap();
    let k_domain: GeneralEvaluationDomain<E::Fr> = GeneralEvaluationDomain::new(k).unwrap();

    let mut transcript = CaulkTranscript::<E::Fr>::new();

    // add the instance to the transcript
    transcript.append_element(b"T_com", &instance.tr_com.ts_poly_com);
    transcript.append_element(b"A_com", &instance.tr_com.a_poly_com);
    transcript.append_element(b"Op_com", &instance.tr_com.op_poly_com);
    transcript.append_element(b"V_com", &instance.tr_com.v_poly_com);

    // add prover's first message
    let z1_com: E::G1Affine = KZGCommit::commit_g1(&pp.poly_ck, &input.z1_poly);
    let z2_com: E::G1Affine = KZGCommit::commit_g1(&pp.poly_ck, &input.z2_poly);
    let delta_A_com: E::G1Affine = KZGCommit::commit_g1(&pp.poly_ck, &input.delta_A_poly);
    let delta_T_com: E::G1Affine = KZGCommit::commit_g1(&pp.poly_ck, &input.delta_T_poly);

    transcript.append_element(b"z1_com", &z1_com);
    transcript.append_element(b"z2_com", &z2_com);
    transcript.append_element(b"delta_A_com", &delta_A_com);
    transcript.append_element(b"delta_T_com", &delta_T_com);

    // generate verifier challenge
    let gamma = transcript.get_and_append_challenge(b"gamma");
    let gamma_sq = gamma.square();

    // send prover's second message
    let (q1_poly, q2_poly) = compute_q1_and_q2_poly::<E>(
        &example.addr_tr.a_poly,
        &example.addr_tr.ts_poly,
        &example.addr_tr.v_poly,
        &example.addr_tr.op_poly,
        &input.delta_A_poly,
        &input.delta_T_poly,
        &input.z1_poly,
        &input.z2_poly,
        gamma.clone(),
        k_domain_size
    );

    let q1_com = KZGCommit::<E>::commit_g1(&pp.poly_ck, &q1_poly);
    let q2_com = KZGCommit::<E>::commit_g1(&pp.poly_ck, &q2_poly);

    transcript.append_element(b"q1_com", &q1_com);
    transcript.append_element(b"q2_com", &q2_com);

    // verifier sends evaluation point
    let s = transcript.get_and_append_challenge(b"s_eval");
    let ws: E::Fr = s.mul(k_domain.element(1));
    // prover sends evaluations
    let v_A_s = example.addr_tr.a_poly.evaluate(&s);
    let v_A_ws = example.addr_tr.a_poly.evaluate(&ws);
    let v_delta_A_s = input.delta_A_poly.evaluate(&s);
    let v_T_s = example.addr_tr.ts_poly.evaluate(&s);
    let v_T_ws = example.addr_tr.ts_poly.evaluate(&ws);
    let v_delta_T_s = input.delta_T_poly.evaluate(&s);
    let v_op_ws = example.addr_tr.op_poly.evaluate(&ws);
    let v_V_s = example.addr_tr.v_poly.evaluate(&s);
    let v_V_ws = example.addr_tr.v_poly.evaluate(&ws);
    let v_Q1_s = q1_poly.evaluate(&s);
    let v_Q2_s = q2_poly.evaluate(&s);
    let v_Z1_s = input.z1_poly.evaluate(&s);
    let v_Z2_s = input.z2_poly.evaluate(&s);

    // add the evaluations to the transcript
    transcript.append_element(b"v_A_s", &v_A_s);
    transcript.append_element(b"v_A_ws", &v_A_ws);
    transcript.append_element(b"v_delta_A_s", &v_delta_A_s);
    transcript.append_element(b"v_T_s", &v_T_s);
    transcript.append_element(b"v_T_ws", &v_T_ws);
    transcript.append_element(b"v_delta_T_s", &v_delta_T_s);
    transcript.append_element(b"v_op_ws", &v_op_ws);
    transcript.append_element(b"v_V_s", &v_V_s);
    transcript.append_element(b"v_V_ws", &v_V_ws);
    transcript.append_element(b"v_Q1_s", &v_Q1_s);
    transcript.append_element(b"v_Q2_s", &v_Q2_s);
    transcript.append_element(b"v_Z1_s", &v_Z1_s);
    transcript.append_element(b"v_Z2_s", &v_Z2_s);


    // sanity checks
    assert_eq!(v_Q1_s * v_Z1_s, v_A_ws.sub(v_A_s) - v_delta_A_s, "Q1(s).Z1(s) != v_A(ws)-v_A(s)-delta_A(s)");
    assert_eq!(v_Z1_s * v_Z2_s * (s-k_domain.element(k-1)), k_domain.evaluate_vanishing_polynomial(s), "Z1(s).Z2(s).(s-1)=s^k-1");
    assert_eq!(v_Q2_s * v_Z2_s, (v_A_ws - v_A_s) + (gamma * (v_T_ws - v_T_s - v_delta_T_s)) +
        (gamma_sq * (v_op_ws - E::Fr::one()) * (v_V_ws - v_V_s)), "Q2(s).Z2(s)=A(ws)-A(s)+gamma(T(ws)-T(s)-delta_T(s)+...");

    // verifier sends evaluation aggregation challenge
    let r1 = transcript.get_and_append_challenge(b"r1");
    let r2 = transcript.get_and_append_challenge(b"r2");

    let polys_s = vec![
        example.addr_tr.a_poly.clone(),
        input.delta_A_poly.clone(),
        example.addr_tr.ts_poly.clone(),
        input.delta_T_poly.clone(),
        example.addr_tr.v_poly.clone(),
        q1_poly.clone(),
        q2_poly.clone(),
        input.z1_poly.clone(),
        input.z2_poly.clone()
    ];

    let polys_ws = vec![
        example.addr_tr.a_poly.clone(),
        example.addr_tr.ts_poly.clone(),
        example.addr_tr.v_poly.clone(),
        example.addr_tr.op_poly.clone()
    ];

    let agg_poly_s = compute_aggregate_poly::<E>(&polys_s, r1);
    let agg_poly_ws = compute_aggregate_poly::<E>(&polys_ws, r2);

    let (val_s, proof_s) = KZGCommit::<E>::open_g1_batch(
        &pp.poly_ck,
        &agg_poly_s,
        None,
        &[s],
    );

    let (val_ws, proof_ws) = KZGCommit::<E>::open_g1_batch(
        &pp.poly_ck,
        &agg_poly_ws,
        None,
        &[ws]
    );

    let N = 1usize << h_domain_size;
    let table = (0..N).into_iter().collect::<Vec<_>>();
    let table_pp: CqProverInput<E> = CqProverInput::load(h_domain_size);
    let cq_pp: CqPublicParams<E> = CqPublicParams::load(h_domain_size);

    let example_A: CqExample<E::Fr> = CqExample::new_fixed_subvec(
        &table,
        &example.A_ast_vec,
        k_domain_size,
        k_domain_size);

    let example_T: CqExample<E::Fr> = CqExample::new_fixed_subvec(
        &table,
        &example.T_ast_vec,
        k_domain_size,
        k_domain_size);

    let example_delta_A: CqExample<E::Fr> = CqExample::new_fixed_subvec(
        &table,
        &input.delta_A_vec,
        k_domain_size,
        k_domain_size);

    let example_delta_T: CqExample<E::Fr> = CqExample::new_fixed_subvec(
        &table,
        &input.delta_T_vec,
        k_domain_size,
        k_domain_size);



    let t_com = KZGCommit::<E>::commit_g2(&pp.g2_powers, &example_A.t_poly);
    // compute CQ proofs
    let range_check_A:CqLookupInstance<E> = CqLookupInstance::<E> {
        t_com: t_com,
        f_com: instance.tr_com.a_poly_com,
        m_domain_size,
        h_domain_size,
    };

    let range_check_T:CqLookupInstance<E> = CqLookupInstance::<E> {
        t_com: t_com,
        f_com: instance.tr_com.ts_poly_com,
        m_domain_size,
        h_domain_size,
    };

    let range_check_delta_A:CqLookupInstance<E> = CqLookupInstance::<E> {
        t_com: t_com,
        f_com: delta_A_com,
        m_domain_size,
        h_domain_size,
    };

    let range_check_delta_T:CqLookupInstance<E> = CqLookupInstance::<E> {
        t_com: t_com,
        f_com: delta_T_com,
        m_domain_size,
        h_domain_size,
    };


    let proof_range_A: CqProof<E> = compute_cq_proof(
        &range_check_A,
        &table_pp,
        &example_A,
        &cq_pp,
        &pp,
        false,
    );

    let proof_range_T: CqProof<E> = compute_cq_proof(
        &range_check_T,
        &table_pp,
        &example_T,
        &cq_pp,
        &pp,
        false,
    );

    let proof_range_delta_A: CqProof<E> = compute_cq_proof(
        &range_check_delta_A,
        &table_pp,
        &example_delta_A,
        &cq_pp,
        &pp,
        false,
    );

    let proof_range_delta_T: CqProof<E> = compute_cq_proof(
        &range_check_delta_T,
        &table_pp,
        &example_delta_T,
        &cq_pp,
        &pp,
        false,
    );

    // prover sends aggregated KZG proofs
    ProofMonotonic::<E> {
        z1_com: z1_com,
        z2_com: z2_com,
        delta_A_com: delta_A_com,
        delta_T_com: delta_T_com,
        q1_com: q1_com,
        q2_com: q2_com,
        val_A_s: v_A_s,
        val_A_ws: v_A_ws,
        val_deltaA_s: v_delta_A_s,
        val_deltaT_s: v_delta_T_s,
        val_T_s: v_T_s,
        val_T_ws: v_T_ws,
        val_op_ws: v_op_ws,
        val_V_s: v_V_s,
        val_V_ws: v_V_ws,
        val_Q1_s: v_Q1_s,
        val_Q2_s: v_Q2_s,
        val_Z1_s: v_Z1_s,
        val_Z2_s: v_Z2_s,
        pi_s: proof_s,
        pi_ws: proof_ws,
        range_proof_A: proof_range_A,
        range_proof_deltaA: proof_range_delta_A,
        range_proof_deltaT: proof_range_delta_T,
        range_proof_t: proof_range_T,
    }
}









#[cfg(test)]
mod tests {
    use super::*;
    use ark_bls12_381::Bls12_381;
    use ark_ff::PrimeField;
    use ark_bls12_381::Fr;
    use ark_poly::GeneralEvaluationDomain;

    #[test]
    #[allow(non_snake_case)]
    fn test_transcript() {
        test_transcript_helper::<Bls12_381>();
    }

    fn test_transcript_helper<E: PairingEngine>() {
        let m_domain_size: usize = 7;
        let k_domain_size: usize = 9;
        let h_domain_size: usize = 16   ;
        let N: usize = 1 << h_domain_size;
        let m = 1usize << m_domain_size;
        let n = h_domain_size;
        let max_degree = N;

        let pp: PublicParameters<E> = PublicParameters::setup(&max_degree, &N, &m, &n);
        let example: MonotonicTranscriptExample<E> = MonotonicTranscriptExample::new(m_domain_size, h_domain_size, &pp);
        example.display();

        let input = generate_monotonic_prover_input::<E>(&example, &pp);
        let instance: MonotonicTranscriptInstance<E> = MonotonicTranscriptInstance {
            tr_com: example.tr_com.clone(),
            m_domain_size,
            h_domain_size,
        };

        let mut start = Instant::now();
        let proof = compute_monotonic_proof::<E>(
            &instance,
            &example,
            &input,
            &pp
        );
        println!("Computing monotonicity proof took {} secs", start.elapsed().as_secs());

    }
    #[test]
    #[allow(non_snake_case)]
    fn test_concat() {
        let mut rng = ark_std::test_rng();

        let m_domain_size: usize = 2;
        let k_domain_size: usize = 4;
        let n_domain_size: usize = 0;
        let N_domain_size: usize = 10;

        let m: usize = 1 << m_domain_size;
        let k: usize = 1 << k_domain_size;
        let N: usize = 1 << N_domain_size;

        let example = ConcatExample::<Bls12_381>::new(m_domain_size);
        example.display();

        // Get evaluation domains and interpolate polynomials
        let m_domain = GeneralEvaluationDomain::<Fr>::new(1 << m_domain_size).unwrap();
        let k_domain = GeneralEvaluationDomain::<Fr>::new(1 << k_domain_size).unwrap();

        let a_poly = DensePolynomial::<Fr>::from_coefficients_slice(&m_domain.ifft(&example.a_vec));
        let a_bar_poly = DensePolynomial::<Fr>::from_coefficients_slice(&m_domain.ifft(&example.a_bar_vec));
        let a_dash_poly = DensePolynomial::<Fr>::from_coefficients_slice(&m_domain.ifft(&example.a_dash_vec));
        let v_poly = DensePolynomial::<Fr>::from_coefficients_slice(&m_domain.ifft(&example.v_vec));
        let v_bar_poly = DensePolynomial::<Fr>::from_coefficients_slice(&m_domain.ifft(&example.v_bar_vec));
        let v_dash_poly = DensePolynomial::<Fr>::from_coefficients_slice(&m_domain.ifft(&example.v_dash_vec));
        let op_bar_poly = DensePolynomial::<Fr>::from_coefficients_slice(&m_domain.ifft(&example.op_bar_vec));

        let A_poly = DensePolynomial::<Fr>::from_coefficients_slice(&k_domain.ifft(&example.A_vec));
        let V_poly = DensePolynomial::<Fr>::from_coefficients_slice(&k_domain.ifft(&example.V_vec));
        let Op_poly = DensePolynomial::<Fr>::from_coefficients_slice(&k_domain.ifft(&example.Op_vec));

        // Compute KZG commitments

        let pp: PublicParameters<Bls12_381> = PublicParameters::setup(&N, &N, &m, &N_domain_size);

        let (a_com, a_bar_com, a_dash_com,
            v_com, v_bar_com, v_dash_com,
            op_bar_com, Op_com, A_com, V_com) = (
            KZGCommit::<Bls12_381>::commit_g1(&pp.poly_ck, &a_poly),
            KZGCommit::<Bls12_381>::commit_g1(&pp.poly_ck, &a_bar_poly),
            KZGCommit::<Bls12_381>::commit_g1(&pp.poly_ck, &a_dash_poly),
            KZGCommit::<Bls12_381>::commit_g1(&pp.poly_ck, &v_poly),
            KZGCommit::<Bls12_381>::commit_g1(&pp.poly_ck, &v_bar_poly),
            KZGCommit::<Bls12_381>::commit_g1(&pp.poly_ck, &v_dash_poly),
            KZGCommit::<Bls12_381>::commit_g1(&pp.poly_ck, &op_bar_poly),
            KZGCommit::<Bls12_381>::commit_g1(&pp.poly_ck, &Op_poly),
            KZGCommit::<Bls12_381>::commit_g1(&pp.poly_ck, &A_poly),
            KZGCommit::<Bls12_381>::commit_g1(&pp.poly_ck, &V_poly),

        );

        let instance: ConcatInstance<Bls12_381> = ConcatInstance {
            a_com,
            v_com,
            op_bar_com,
            a_bar_com,
            v_bar_com,
            a_dash_com,
            v_dash_com,
            Op_com,
            A_com,
            V_com,
            m_domain_size
        };

        let input: ConcatProverInput<Bls12_381> = ConcatProverInput {
            a_poly,
            v_poly,
            op_bar_poly,
            a_bar_poly,
            v_bar_poly,
            a_dash_poly,
            v_dash_poly,
            Op_poly,
            A_poly,
            V_poly,
        };

        let proof = compute_concat_proof::<Bls12_381>(
            &instance,
            &input,
            &pp,
        );

        let status = verify_concat_proof::<Bls12_381>(
            &instance,
            &proof.unwrap(),
            &pp
        );

        println!("Verification Status [ {} ]", status);
    }

    #[test]
    #[allow(non_snake_case)]
    fn cost_simulation() {
        let depth: usize = 5;
        let totalops: usize = 1usize << 20;
        let delta: usize = 1usize << 17;
        let mut rng = rand::thread_rng();


        // a vector to model accounting tree as a binary tree.
        // Indices (2i+1, 2i+2) are the left and right children of
        // index i. Conversely, the parent of i is given by integer division (i-1)/2
        let mut tree: Vec<usize> = Vec::new();
        let num_nodes: usize = (1usize << (depth + 1)) - 1;
        tree.resize(num_nodes, 0);

        // start simulation and accumulate the cost
        let mut cost: f64 = 0.0;
        let mut tcost: usize = 0;


        for _ in 0..totalops {
            let mut current_idx:usize = 0;
            tree[current_idx] += 1;

            for j in 0..depth {
                // randomly pick left or right child to add the operation to
                current_idx = 2*current_idx + 1 + (rng.gen::<usize>() % 2);
                tree[current_idx] += 1;
            }

            // prune the tree accumulating the cost
            let mut cur_node:usize = 0;
            let mut level_threshold = delta;
            let mut level_tab_size: usize = totalops;
            if (tree[cur_node] >= level_threshold) {
                let start_dist = tree[cur_node];
                for _ in 0..depth {
                    // find next node with >= level_threshold/2
                    level_threshold /= 2;
                    level_tab_size /= 2;
                    if tree[2*cur_node + 1] >= level_threshold {
                        cur_node = 2*cur_node + 1;
                    } else {
                        cur_node = 2*cur_node + 2;
                    }
                }

                // at this point, cur_node points to the leaf node that
                // needs to be processed.
                let adj = tree[cur_node];
                tcost += level_tab_size;

                // travel backwards and update the distances of the nodes
                tree[cur_node] -= adj;
                for _ in 0..depth {
                    cur_node = (cur_node - 1)/2;
                    tree[cur_node] -= adj;
                }

                println!("start_dist: {}, adj: {}", start_dist, adj);
                assert_eq!(tree[0], start_dist - adj, "Incorrect dist adjustment");

            }

        }

        cost = (tcost as f64).div(totalops as f64);
        println!("Average cost: {}", cost);






    }
}

