// This file contains implementation of the Caulk+ scheme

use std::collections::HashSet;
use std::ops::Neg;
use ark_ec::{AffineCurve, PairingEngine, ProjectiveCurve};
use ark_ff::{One, PrimeField, Zero};
use ark_poly::{EvaluationDomain, GeneralEvaluationDomain, Polynomial, UVPolynomial};
use ark_poly::univariate::DensePolynomial;
use ark_std::UniformRand;
use crate::{compute_vanishing_poly, fast_poly_interpolate, group_dft, KZGCommit, PublicParameters};
use rand::{Rng, RngCore};
use crate::multi::TableInput;

#[allow(non_snake_case)]
pub struct CaulkPlusPublicParams<E: PairingEngine> {
    pub z_h_com: E::G1Affine,                         // commitment to vanishing poly
    pub log_poly_com: E::G1Affine,                    // commitment to log polynomial
    pub log_poly: DensePolynomial<E::Fr>,           // log polynomial on h_domain
    pub openings_z_h_poly: Vec<E::G2Affine>,        // opening proofs for polynomial X^N - 1
    pub openings_log_poly: Vec<E::G2Affine>,        // opening proofs for log polynomial
}

pub struct CaulkPlusProverInput<E: PairingEngine> {
    pub t_com: E::G1Affine,                          // commitment to table
    pub t_poly: DensePolynomial<E::Fr>,             // polynomial interpolating the table on h_domain
    pub openings_t_poly: Vec<E::G2Affine>,          // opening proofs of the t-polynomial
}

pub struct CaulkPlusLookupInstance<E: PairingEngine> {
    pub t_com: E::G1Affine,                         // commitment of the table
    pub a_com: E::G1Affine,                         // commitment of the a-vector (addresses)
    pub v_com: E::G1Affine,                         // commitment of v=t[a] vector
    pub m_domain_size: usize,                       // domain size of a vector
    pub h_domain_size: usize,                       // domain size of table
}

pub struct CiLookupProverInput<E: PairingEngine> {
    pub a_poly: DensePolynomial<E::Fr>,             // a polynomial
    pub v_poly: DensePolynomial<E::Fr>,             // v polynomial
    pub t_i_poly: DensePolynomial<E::Fr>,           // t_I polynomial
    pub l_i_poly: DensePolynomial<E::Fr>,           // l_I polynomial
    pub z_i_poly: DensePolynomial<E::Fr>,           // z_I polynomial
    pub h_poly: DensePolynomial<E::Fr>,             // h polynomial mapping
}

// Generated with respect to a pre-processed table.
pub struct CaulkPlusExample {
    pub a_vec: Vec<usize>,                          // lookup indices
    pub v_vec: Vec<usize>,                          // value vector v = t[a]
}

impl<E: PairingEngine> CaulkPlusProverInput<E> {
    // store the prover input in a file
    pub fn store(&self, path: &str) {
        let table: TableInput<E> = TableInput {
            c_poly: self.t_poly.clone(),
            c_com: self.t_com.clone(),
            openings: self.openings_t_poly.clone()
        };
        table.store(path);

    }

    // load prover input from a file
    pub fn load(path: &str) -> CaulkPlusProverInput<E> {
        let table = TableInput::<E>::load(&path);

        CaulkPlusProverInput {
            t_com: table.c_com,
            t_poly: table.c_poly,
            openings_t_poly: table.openings
        }
    }
}

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

        table_z_h.store(&path_z_h);
        table_log_poly.store(&path_log_poly);
        
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

        let table_z_h: TableInput<E> = TableInput::load(&path_z_h);
        let table_log_poly: TableInput<E> = TableInput::load(&path_log_poly);

        CaulkPlusPublicParams::<E> {
            z_h_com: table_z_h.c_com,
            log_poly_com: table_log_poly.c_com,
            log_poly: table_log_poly.c_poly,
            openings_z_h_poly: table_z_h.openings,
            openings_log_poly: table_log_poly.openings
        }
    }

    pub fn new(
        pp: &PublicParameters<E>,
        h_domain_size: usize
    ) -> CaulkPlusPublicParams<E> {
        let h_domain: GeneralEvaluationDomain<E::Fr> = GeneralEvaluationDomain::new(1 << h_domain_size).unwrap();
        //let z_h_poly = h_domain.vanishing_polynomial();

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

        let openings_log_poly = KZGCommit::<E>::multiple_open::<E::G2Affine>(
            &log_poly,
            &pp.g2_powers,
            h_domain_size
        );

        CaulkPlusPublicParams::<E> {
            z_h_com: z_h_com,
            log_poly_com: log_poly_com,
            log_poly: log_poly,
            openings_z_h_poly: openings_z_h_poly,
            openings_log_poly: openings_log_poly,
        }

    }
}
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
    let openings_t_poly = KZGCommit::<E>::multiple_open::<E::G2Affine>(
        &t_poly,
        &pp.g2_powers,
        h_domain_size
    );


    CaulkPlusProverInput {
        t_com: t_com,
        t_poly: t_poly,
        openings_t_poly: openings_t_poly,
    }
}
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

    let z_i_poly = compute_vanishing_poly(&i_ff_vec, 1);
    let t_i_poly = fast_poly_interpolate(&h_i_vec, &t_i_vec);
    let l_i_poly = fast_poly_interpolate(&h_i_vec, &l_i_vec);
    let h_poly = DensePolynomial::from_coefficients_vec(m_domain.ifft(&h_val_vec));
    let a_poly = DensePolynomial::from_coefficients_vec(m_domain.ifft(&a_ff_vec));
    let v_poly = DensePolynomial::from_coefficients_vec(m_domain.ifft(&v_ff_vec));

    CiLookupProverInput {
        a_poly: a_poly,
        v_poly: v_poly,
        t_i_poly: t_i_poly,
        l_i_poly: l_i_poly,
        z_i_poly: z_i_poly,
        h_poly: h_poly,
    }

}


#[cfg(test)]
mod tests {
    use std::ops::Neg;
    use super::*;
    use ark_bls12_381::Bls12_381;
    use ark_ff::PrimeField;
    use ark_bls12_381::Fr;
    use ark_ec::{AffineCurve, ProjectiveCurve};
    use ark_poly::{GeneralEvaluationDomain, Polynomial};
    use crate::multi::generate_lookup_input;

    const h_domain_size: usize = 10;
    const m_domain_size: usize = 4;


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

        let cp_prover_input = generate_caulkplus_prover_input(
            &t_vec,
            &pp,
            h_domain_size
        );

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
        //let caulk_pp = CaulkPlusPublicParams::<E>::new(&pp, h_domain_size);
        //caulk_pp.store();
        let caulk_pp: CaulkPlusPublicParams<E> = CaulkPlusPublicParams::load(h_domain_size);

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
        }




    }
}






