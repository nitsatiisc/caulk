// This file contains artifacts for AFG commitment scheme

use ark_ec::PairingEngine;
use ark_poly::{EvaluationDomain, GeneralEvaluationDomain};
use ark_poly::univariate::DensePolynomial;
use ark_std::UniformRand;
use rand::RngCore;
use crate::PublicParameters;

pub struct AFGSetup<E: PairingEngine> {
    pub k_domain_size: usize,
    pub domain: GeneralEvaluationDomain<E::Fr>,
    pub ck: Vec<E::G2Affine>
}

impl<E: PairingEngine> AFGSetup<E> {
    pub fn new(k_domain_size: usize, rng: &mut RngCore) -> Self {
        let K:usize = 1usize << k_domain_size;
        let domain = GeneralEvaluationDomain::<E::Fr>::new(K).unwrap();
        let afg_pp = PublicParameters::<E>::setup(&K, &K, &k_domain_size, &k_domain_size);
        let mut ck: Vec<E::G2Affine> = Vec::new();
        ck.push(afg_pp.g2_powers[0]);
        for i in 0..K {
            ck.push(afg_pp.g2_powers[i]);
        }

        Self {
            k_domain_size,
            domain,
            ck
        }

    }
}

pub struct PackedPolynomial<E: PairingEngine> {
    pub h_domain_size: usize,
    pub domain: GeneralEvaluationDomain<E::Fr>,
    pub coeffs: Vec<DensePolynomial<E::Fr>>,
    pub com: E::Fqk,
}

impl<E: PairingEngine> PackedPolynomial<E> {
    pub fn new(h_domain_size: usize, coeffs: &Vec<DensePolynomial<E::Fr>>, afg_pp: &AFGSetup<E>) -> Self {

    }
}