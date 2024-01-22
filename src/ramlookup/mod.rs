pub mod caulkplus;
mod fastupdate;

use std::marker::PhantomData;
use std::ops::{Mul, Neg, Sub};
use ark_ec::{AffineCurve, PairingEngine, ProjectiveCurve};
use ark_ff::{FftField, Field, One, PrimeField, Zero};
use ark_poly::{univariate::DensePolynomial, EvaluationDomain, GeneralEvaluationDomain};
use ark_poly_commit::{kzg10, Polynomial, UVPolynomial};
use ark_poly_commit::kzg10::VerifierKey;
use ark_std::{log2, test_rng, time::Instant, UniformRand};
use merlin::Transcript;
use crate::{multi::{
    compute_lookup_proof, get_poly_and_g2_openings, verify_lookup_proof, LookupInstance,
    LookupProverInput,
}, KZGCommit, PublicParameters, CaulkTranscript, compute_vanishing_poly};
use rand::{Rng, RngCore};




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

pub struct ProverInputCommon<E: PairingEngine> {
    pub t_poly: DensePolynomial<E::Fr>,         // last pre-processed RAM table
    pub l_poly: DensePolynomial<E::Fr>,         // log-polynomial
    pub zh_poly: DensePolynomial<E::Fr>,        // vanishing polynomial X^N - 1
    pub t_poly_openings: Vec<E::G2Affine>,      // pre-computed openings for t_poly
    pub l_poly_openings: Vec<E::G2Affine>,      // pre-computed openings for l_poly
    pub zh_poly_openings: Vec<E::G2Affine>,     // pre-computed openings for domain_n
}

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

impl<E: PairingEngine> ConcatExample<E> {
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

#[allow(non_snake_case)]
pub fn generate_concat_prover_example<E: PairingEngine>(
    m_domain_size: usize,
) -> ConcatExample<E> {
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

pub struct VerifierInputCommon<E: PairingEngine> {
    pub poly_vk: VerifierKey<E>,                // KZG verification key
    pub z_com: E::G1Affine,                     // Commitment to poly (X-1)..(X-w^{m-1}) where w^{4m}=1
    pub domain_m_size: usize,                   // size of domain m
    pub domain_k_size: usize,                   // size of domain k=4m
    pub domain_n_size: usize,                   // size of big RAM domain
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

pub fn compute_concat_proof<E: PairingEngine>(
    instance: &ConcatInstance<E>,
    input: &ConcatProverInput<E>,
    pp: &PublicParameters<E>,
) -> Option<ProofConcat<E>>
{
    let mut proof: Option<ProofConcat<E>> = None;
    let k_domain_size = instance.m_domain_size + 2;
    // m_domain = [1,v,..,v^{m-1}], k_domain = [1,w,...,w^{k-1}} where k=4m
    let m_domain: GeneralEvaluationDomain<E::Fr> = GeneralEvaluationDomain::new(1 << instance.m_domain_size).unwrap();
    let k_domain: GeneralEvaluationDomain<E::Fr> = GeneralEvaluationDomain::new(1 << k_domain_size).unwrap();

    // Round0: Calculate the Z(X)=(X-1)...(X-w^{m-1}) polynomial (this will eventually be pre-computed
    // The second argument is unused in the function.
    let mut k_domain_vec: Vec<E::Fr> = Vec::new();
    for i in 0..m_domain.size() {
        k_domain_vec.push(k_domain.element(i))
    }
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
    println!("Eval point verifier: {}", s);

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

    println!("b_h b_g b_q b_z {} {} {} {}", b_h, b_g, b_q, b_z);
    status = b_h & b_g & b_q & b_z;
    status
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
    fn test_concat() {
        let mut rng = ark_std::test_rng();

        let m_domain_size: usize = 2;
        let k_domain_size: usize = 4;
        let n_domain_size: usize = 0;
        let N_domain_size: usize = 10;

        let m: usize = 1 << m_domain_size;
        let k: usize = 1 << k_domain_size;
        let N: usize = 1 << N_domain_size;

        let example = generate_concat_prover_example::<Bls12_381>(m_domain_size);
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

        let pp: PublicParameters<Bls12_381> = PublicParameters::setup(&N, &k, &m, &N_domain_size);

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
}

