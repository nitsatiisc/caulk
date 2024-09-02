// This file contains artifacts for AFG commitment scheme

use std::ops::{Mul, MulAssign};
use ark_ec::msm::VariableBaseMSM;
use ark_ec::{AffineCurve, PairingEngine, ProjectiveCurve};
use ark_ff::{One, PrimeField, Zero, Field};
use ark_msm::types::BigInt;
use ark_poly::{EvaluationDomain, GeneralEvaluationDomain, Polynomial, UVPolynomial};
use ark_poly::univariate::DensePolynomial;
use ark_std::UniformRand;
use ark_test_curves::AffineRepr;
use rand::RngCore;
use crate::{CaulkTranscript, KZGCommit, PublicParameters};

pub struct AFGSetup<E: PairingEngine> {
    pub k_domain_size: usize,
    pub domain: GeneralEvaluationDomain<E::Fr>,
    pub ck: Vec<E::G2Affine>,
    pub vk: Vec<E::G1Affine>,
}

pub struct LagrangeFoldingArgument<F: PrimeField> {
    pub k_domain_size: usize,                           // l = domain size
    pub domain: GeneralEvaluationDomain<F>,             // domain
    pub ch_vec: Vec<F>,                                 // challenge vector (c_0,\ldots,c_{l-1})
    pub z: F,                                           // evaluation point
    pub seed: F,                                        // challenge seed for protocol composition
}

pub struct LagrangianFoldingProof<F: PrimeField> {
    pub round_polynomials: Vec<DensePolynomial<F>>,
}

pub fn split_vec<T: Clone>(v: &Vec<T>) -> (Vec<T>, Vec<T>)
{
    let n = v.len();
    let mut v_left: Vec<T> = Vec::new();
    let mut v_right: Vec<T> = Vec::new();
    for i in 0..n/2 {
        v_left.push(v[i].clone());
        v_right.push(v[n/2+i].clone());
    }

    (v_left, v_right)
}

pub fn combine_g1_vec<E: PairingEngine>(v_left: &Vec<E::G1Affine>, v_right: &Vec<E::G1Affine>, ch: E::Fr) -> Vec<E::G1Affine> {
    let mut v: Vec<E::G1Affine> = Vec::new();
    for i in 0..v_left.len() {
        v.push(v_left[i] + v_right[i].into_projective().mul(ch.into_repr()).into_affine());
    }
    v
}

pub fn combine_g2_vec<E: PairingEngine>(v_left: &Vec<E::G2Affine>, v_right: &Vec<E::G2Affine>, ch: E::Fr) -> Vec<E::G2Affine> {
    let mut v: Vec<E::G2Affine> = Vec::new();
    for i in 0..v_left.len() {
        v.push(v_left[i] + v_right[i].into_projective().mul(ch.into_repr()).into_affine());
    }
    v
}

pub fn combine_field_vec<E: PairingEngine>(v_left: &Vec<E::Fr>, v_right: &Vec<E::Fr>, ch: E::Fr) -> Vec<E::Fr> {
    let mut v: Vec<E::Fr> = Vec::new();
    for i in 0..v_left.len() {
        v.push(v_left[i] + (ch * v_right[i]));
    }
    v
}



impl<E: PairingEngine> AFGSetup<E> {
    pub fn new(k_domain_size: usize, rng: &mut dyn RngCore) -> Self {
        let K:usize = 1usize << k_domain_size;
        let domain = GeneralEvaluationDomain::<E::Fr>::new(K).unwrap();
        let afg_pp = PublicParameters::<E>::setup(&K, &K, &k_domain_size, &k_domain_size);
        let mut ck: Vec<E::G2Affine> = Vec::new();
        ck.push(afg_pp.g2_powers[0]);
        for i in 0..K {
            ck.push(afg_pp.g2_powers[i]);
        }

        let vk:Vec<E::G1Affine> = vec![afg_pp.poly_ck.powers_of_g[0], afg_pp.poly_ck.powers_of_g[1]];

        Self {
            k_domain_size,
            domain,
            ck,
            vk
        }

    }
}

pub struct PackedPolynomial<E: PairingEngine> {
    pub k_domain_size: usize,
    pub domain: GeneralEvaluationDomain<E::Fr>,
    pub coeffs: Vec<DensePolynomial<E::Fr>>,            // univariate coefficients in lagrange basis
    pub com: E::Fqk,
    pub ucomms: Vec<E::G1Affine>,                       // univariate commitments
}

pub struct PartialOpenProof<E: PairingEngine> {
    uni_com: E::G1Affine,                               // commitment to univariate restriction
    round_comms: Vec<E::Fqk>,                           // round cross commitments (of folded witness)
    round_ip:    Vec<E::G1Affine>,                      // round cross inner products (of folded witness and linear form)
    lf_proof: Vec<DensePolynomial<E::Fr>>,              // lagrangian folding proof
}

impl<E: PairingEngine> PackedPolynomial<E> {
    pub fn new(k_domain_size: usize, coeffs: &Vec<DensePolynomial<E::Fr>>, afg_pp: &AFGSetup<E>, pp: &PublicParameters<E>) -> Self {
        let n: usize = 1usize << k_domain_size;
        let domain: GeneralEvaluationDomain<E::Fr> = GeneralEvaluationDomain::new(n).unwrap();
        let mut ucomms: Vec<E::G1Affine> = Vec::new();
        for i in 0..n {
            ucomms.push(KZGCommit::commit_g1(&pp.poly_ck, &coeffs[i]));
        }

        let mut com = E::Fqk::one();
        for i in 0..n {
            com.mul_assign(E::pairing(ucomms[i], afg_pp.ck[i]));
        }

        Self {
            k_domain_size,
            domain,
            coeffs: coeffs.clone(),
            com,
            ucomms
        }

    }

    pub fn partial_open(&self, x: E::Fr, afg_pp: &AFGSetup<E>) -> PartialOpenProof<E> {
        // compute vector [\mu_0(x),\ldots,m_{n-1}(x)} of lagrange evaluations at x
        let n = 1usize << self.k_domain_size;
        let domain: GeneralEvaluationDomain<E::Fr> = GeneralEvaluationDomain::new(n).unwrap();
        let mut lf: Vec<E::Fr> = Vec::new();
        let zh_x = domain.evaluate_vanishing_polynomial(x);
        for i in 0..n {
            let temp = zh_x.mul((x - domain.element(i)).inverse().unwrap()).mul(domain.element(i));
            lf.push(temp * E::Fr::from(n as u128).inverse().unwrap());
        }

        let lf_bigint = lf.iter().map(|x| x.into_repr()).collect::<Vec<_>>();
        // compute commitment to P(x,Y) = prod_{i=0}^{n-1} e(coeffs[i], ck[i])
        let uni_com = VariableBaseMSM::multi_scalar_mul(&self.ucomms, &lf_bigint).into_affine();

        // cross commitments and cross inner products for each round
        let mut round_comms: Vec<E::Fqk> = Vec::new();
        let mut round_ip: Vec<E::G1Affine> = Vec::new();

        let mut transcript = CaulkTranscript::<E::Fr>::new();
        transcript.append_element(b"uni_comm", &uni_com);
        let mut pairing_comm = self.com.clone();
        let mut ip_com = uni_com.clone();

        // the vectors to be folded: the witness, pairing commitment key, linear form
        let mut witness_vec = self.ucomms.clone();
        let mut ck_vec = afg_pp.ck.clone();
        let mut ch_vec: Vec<E::Fr> = Vec::new();

        while lf.len() > 1 {
            // split the vectors for computing cross commitments
            let (wit_left, wit_right) = split_vec::<E::G1Affine>(&witness_vec);
            let (lf_left, lf_right) = split_vec::<E::Fr>(&lf);
            let (ck_left, ck_right) = split_vec::<E::G2Affine>(&ck_vec);

            let lf_left_bigint = lf_left.iter().map(|x| x.into_repr()).collect::<Vec<_>>();
            let lf_right_bigint = lf_right.iter().map(|x| x.into_repr()).collect::<Vec<_>>();

            let mut pairing_inputs_left: Vec<(E::G1Prepared, E::G2Prepared)> = Vec::new();
            let mut pairing_inputs_right: Vec<(E::G1Prepared, E::G2Prepared)> = Vec::new();

            for i in 0..wit_left.len() {
                pairing_inputs_left.push(
                    (E::G1Prepared::from(wit_right[i]), E::G2Prepared::from(ck_left[i]))
                );

                pairing_inputs_right.push(
                    (E::G1Prepared::from(wit_left[i]), E::G2Prepared::from(ck_right[i]))
                );
            }

            // compute cross-commitments, namely the product of pairings and scalar products
            let c_L = E::product_of_pairings(pairing_inputs_left.iter());
            let c_R= E::product_of_pairings(pairing_inputs_right.iter());
            let ip_L = VariableBaseMSM::multi_scalar_mul(&wit_right, &lf_left_bigint).into_affine();
            let ip_R = VariableBaseMSM::multi_scalar_mul(&wit_left, &lf_right_bigint).into_affine();

            round_comms.push(c_L);
            round_comms.push(c_R);
            round_ip.push(ip_L);
            round_ip.push(ip_R);

            // add cross commitments to transcript
            transcript.append_element(b"c_L", &c_L);
            transcript.append_element(b"c_R", &c_R);
            transcript.append_element(b"lf_L", &ip_L);
            transcript.append_element(b"lf_R", &ip_R);

            let ch = transcript.get_and_append_challenge(b"ch");
            ch_vec.push(ch);

            pairing_comm.mul_assign(c_L.pow(ch.into_repr()).inverse().unwrap().mul(c_R.pow(ch.into_repr())));
            let ch_inv = ch.inverse().unwrap();
            ip_com = ip_com + (ip_L.into_projective().mul(ch_inv.into_repr()).into_affine()) + (ip_R.into_projective().mul(ch.into_repr()).into_affine());

            // collapse the vectors
            lf = combine_field_vec::<E>(&lf_left, &lf_right, ch);
            witness_vec = combine_g1_vec::<E>(&wit_left, &wit_right, ch.inverse().unwrap());
            ck_vec = combine_g2_vec::<E>(&ck_left, &ck_right, ch);
        }

        // sanity test
        // ck_vec[0] is commitment to the univariate polynomial \prod_{i=0}^{\ell-1}(1 + c_i X^{n/2^(i+1)})
        // build the polynomial coefficient vector
        let mut poly_coeffs: Vec<E::Fr> = Vec::new();
        for i in 0..n {
            let mut j = i;
            let mut coeff = E::Fr::one();
            for idx in 0..self.k_domain_size {
                let bit = j % 2;
                if bit == 1 {
                    coeff.mul_assign(ch_vec[self.k_domain_size - 1 - idx]);
                }
                j = j >> 1;
            }
            poly_coeffs.push(coeff);
        }

        let ck_poly: DensePolynomial<E::Fr> = DensePolynomial::from_coefficients_vec(poly_coeffs.clone());
        let ck_poly_com = KZGCommit::<E>::commit_g2(&afg_pp.ck, &ck_poly);
        assert_eq!(ck_vec[0], ck_poly_com, "Folded commitment does not match");

        // check that the folded linear form key is correct.
        // evaluate the folded polynomial (1 + X_0(c_{l-1}-1))(1+X_1(c_{l-2}-1))..(1 + X_{l-1}(c_0-1))
        // on the boolean hypercube, take the inverse FFT and evaluate the resulting polynomial at x
        // This should lf[0].
        let poly_coeffs_monomial = domain.ifft(&poly_coeffs);
        let poly_monomial = DensePolynomial::from_coefficients_vec(poly_coeffs_monomial);
        assert_eq!(poly_monomial.evaluate(&x), lf[0], "Folded inner product does not match");

        // lf_proof = SumCheckArgument(rounds = 2*l,

        PartialOpenProof::<E> {
            uni_com: uni_com,
            round_comms: vec![],
            round_ip: vec![],
            lf_proof: vec![],
        }

    }

}

impl<F: PrimeField> LagrangeFoldingArgument<F> {
    pub fn new(k_domain_size: usize, ch_vec: &Vec<F>, z: F, seed: F) -> Self {
        let n = 1usize << k_domain_size;
        let domain: GeneralEvaluationDomain<F> = GeneralEvaluationDomain::new(n).unwrap();
        Self {
            k_domain_size,
            domain,
            ch_vec: ch_vec.clone(),
            z,
            seed
        }

    }

    pub fn proof(&self) -> LagrangianFoldingProof<F> {
        // initialize pre-computed tables
        let n = self.domain.size();
        let mut A_f: Vec<F> = vec![];
        let mut A_g: Vec<Vec<F>> = vec![];
        A_f.resize(n, F::zero());
        for i in 0..self.k_domain_size {
            let mut g_vec: Vec<F> = vec![];
            g_vec.resize(n, F::zero());
            A_g.push(g_vec);
        }

        // populate the initial vectors in O(n) time for each.
        // compute A_f = [1 c_{l-1}] X [1 c_{l-2}] X ... X [1 c_0]
        let mut psize: usize = 1;
        let mut shift = 0usize;
        A_f[0] = F::one();

        while psize < n {
            for i in 0..psize {
                A_f[psize + i] = self.ch_vec[self.k_domain_size - 1 - shift] * A_f[i];
            }
            psize += psize;
            shift +=1;
        }

        // Populate g_i tables: Note g_i(b) = phi^{2^i}^b - 1 where phi = w^{-1}
        for i in 0..self.k_domain_size {
            for b in 0..n {
                A_g[i][b] = self.domain.element((n-1) - (b << i % n)) - F::one();
            }
        }

        // Powers of z vector
        let mut powers_of_z: Vec<F> = Vec::new();
        let mut z_power = self.z;
        for i in 0..self.k_domain_size {
            powers_of_z.push(z_power);
            z_power = z_power.square();
        }

        // Start rounds by sending polynomials
        let mut transcript = CaulkTranscript::<F>::new();
        transcript.append_element(b"seed", &self.seed);

        let two_ff = F::from(2 as u128);
        // Prover starts by sending the first polynomial g_0(X_0) by sending values at 0,1,2


        LagrangianFoldingProof::<F> {
            round_polynomials: vec![],
        }
    }


}

#[cfg(test)]
mod tests {
    use ark_bls12_381::Bls12_381;
    use ark_ec::PairingEngine;
    use ark_std::test_rng;
    use crate::afgo::AFGSetup;
    use crate::PublicParameters;
    use super::*;

    #[test]
    pub fn test_folding_argument()
    {
        test_folding_argument_helper::<Bls12_381>();
    }

    fn test_folding_argument_helper<E: PairingEngine>()
    {
        let k_domain_size: usize = 3;
        let h_domain_size: usize = 10;

        let m: usize = 1usize << h_domain_size;
        let n = 1usize << k_domain_size;
        let max_degree = m;
        let pp: PublicParameters<E> = PublicParameters::setup(&max_degree, &m, &n, &h_domain_size);
        let mut rng = test_rng();
        let afg_pp: AFGSetup<E> = AFGSetup::<E>::new(k_domain_size, &mut rng);
        let mut uni_poly_coeffs = vec![vec![E::Fr::zero(); m]; n];
        // polynomials to pack

        let uni_poly_coeffs = vec![
            [E::Fr::zero(), E::Fr::zero(), E::Fr::zero()],
            [E::Fr::zero(), E::Fr::zero(), E::Fr::one()],
            [E::Fr::zero(), E::Fr::one(), E::Fr::zero()],
            [E::Fr::zero(), E::Fr::one(), E::Fr::one()],
            [E::Fr::one(), E::Fr::zero(), E::Fr::zero()],
            [E::Fr::one(), E::Fr::zero(), E::Fr::one()],
            [E::Fr::one(), E::Fr::one(), E::Fr::zero()],
            [E::Fr::one(), E::Fr::one(), E::Fr::one()],
        ];

        let mut uni_poly_vec: Vec<DensePolynomial<E::Fr>> = Vec::new();
        for i in 0..uni_poly_coeffs.len() {
            uni_poly_vec.push(DensePolynomial::from_coefficients_slice(&uni_poly_coeffs[i]));
        }

        let packed_P = PackedPolynomial::<E>::new(
            k_domain_size,
            &uni_poly_vec,
            &afg_pp,
            &pp
        );

        let x = E::Fr::rand(&mut rng);
        let pi = packed_P.partial_open(x, &afg_pp);
    }
}
