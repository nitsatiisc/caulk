use std::time::Instant;
use ark_ff::PrimeField;
use ark_poly::{EvaluationDomain, GeneralEvaluationDomain, Polynomial, UVPolynomial};
use ark_poly::univariate::DensePolynomial;
use crate::{compute_vanishing_poly, compute_vanishing_poly_with_subproducts, fast_poly_evaluate, fast_poly_evaluate_with_pp, fast_poly_interpolate, fast_poly_interpolate_with_pp, InvertPolyCache};

#[allow(non_snake_case)]
pub struct UpdateParamsSetK<F: PrimeField> {
    pub set_k: Vec<usize>,                  // indices of set K
    pub set_hk: Vec<F>,                     // set H_K = w^i for i in K
    pub zk_poly: DensePolynomial<F>,        // vanishing polynomial Z_K of H_K
    pub zk_dvt_poly: DensePolynomial<F>,    // derivative of Z_K
    pub Fk_poly: DensePolynomial<F>,        // polynomial F_K
    pub zk_dvt_poly_evals: Vec<F>,          // evaluations of zk_dvt_poly
    pub sub_products: Vec<DensePolynomial<F>>, // sub-products needed for evaluation & interpolation
}

#[allow(non_snake_case)]
impl<F: PrimeField> UpdateParamsSetK<F> {
    pub fn new(set_k: &Vec<usize>, h_domain_size: usize, cache: &mut InvertPolyCache<F>) -> Self {
        let h_domain: GeneralEvaluationDomain<F> = GeneralEvaluationDomain::new(1 << h_domain_size).unwrap();
        let mut set_hk: Vec<F> = Vec::new();
        for i in 0..set_k.len() {
            set_hk.push(h_domain.element( set_k[i]));
        }
        let (zk_poly, sub_products) = compute_vanishing_poly_with_subproducts::<F>(&set_hk, 1);
        let mut zk_dvt_vec: Vec<F> = Vec::new();
        for i in 1..=zk_poly.degree() {
            zk_dvt_vec.push(F::from(i as u128) * zk_poly.coeffs[i]);
        }
        let zk_dvt_poly = DensePolynomial::<F>::from_coefficients_vec(zk_dvt_vec);
        let zk_dvt_evals:Vec<F> = fast_poly_evaluate_with_pp(&zk_dvt_poly.coeffs, &set_hk, &sub_products, cache);

        let mut fk_poly_vec: Vec<F> = Vec::new();
        for i in 2..=zk_poly.degree() {
            fk_poly_vec.push(F::from(((i*(i-1)) as u128)/2) * zk_poly.coeffs[i]);
        }
        let Fk_poly = DensePolynomial::<F>::from_coefficients_vec(fk_poly_vec);

        UpdateParamsSetK {
            set_k: set_k.clone(),
            set_hk: set_hk,
            zk_poly: zk_poly,
            zk_dvt_poly: zk_dvt_poly,
            Fk_poly: Fk_poly,
            zk_dvt_poly_evals: zk_dvt_evals,
            sub_products: sub_products,
        }
    }
}

pub struct ZkHatOracle<F: PrimeField> {
    pub zk_hat_eval: Vec<F>,                    // evaulations of zk_hat polynomial at set H_I
    pub zk_hat_dvt_eval: Vec<F>,                // evaulations of zk_hat derivative at set H_I
}

impl<F: PrimeField> ZkHatOracle<F> {
    pub fn new(
        set_i: &Vec<usize>,
        update_params: &UpdateParamsSetK<F>,
        h_domain_size: usize,
    ) -> ZkHatOracle<F>
    {
        // for efficiency, we assume set_i is a subset of update_params.set_k, and set_k is sequenced so that set_i appears first
        let h_domain: GeneralEvaluationDomain::<F> = GeneralEvaluationDomain::new(1 << h_domain_size).unwrap();
        let N = 1usize << h_domain_size;
        let field_N = F::from(N as u128);
        let field_N1 = F::from( ((N*(N-1))/2) as u128);

        let mut h_i_vec: Vec<F> = Vec::new();
        for i in 0..set_i.len() {
            h_i_vec.push(h_domain.element(set_i[i]));
        }

        let zk_dvt_eval:Vec<F> = update_params.zk_dvt_poly_evals.clone();
        //fast_poly_evaluate(&update_params.zk_dvt_poly.coeffs, &update_params.set_hk);
        let mut zk_hat_eval:Vec<F> = Vec::new();
        for i in 0..update_params.set_k.len() {
            zk_hat_eval.push(field_N.div(
                h_domain.element(update_params.set_k[i]).mul(zk_dvt_eval[update_params.set_k[i]])
            ));
        }

        let fk_eval: Vec<F> = fast_poly_evaluate(&update_params.Fk_poly, &h_i_vec);
        let mut psi_eval: Vec<F> = Vec::new();
        for i in 0..h_i_vec.len() {
            psi_eval.push(fk_eval[i].div(zk_dvt_eval[i].square()).neg());
        }

        let mut zk_hat_dvt_eval: Vec<F> = Vec::new();
        for i in 0..h_i_vec.len() {
            let idx = set_i[i];
            let term1 = (field_N * h_domain.element((2*N - idx) % N)) * psi_eval[i];
            let term2 = (field_N1 * h_domain.element((2*N - 2*idx) % N)).div(zk_dvt_eval[i]);
            zk_hat_dvt_eval.push(term1 + term2);
        }

        ZkHatOracle {
            zk_hat_eval: zk_hat_eval,
            zk_hat_dvt_eval: zk_hat_dvt_eval,
        }

    }
}

pub fn compute_reciprocal_sum<F: PrimeField>(
    t_j_vec: &Vec<usize>,                           // vector defined for j\in K
    set_k: &Vec<usize>,                             // set K over which summation runs for individual multipliers
    set_i: &Vec<usize>,                             // the set I over which we need sums
    domain: &GeneralEvaluationDomain<F>,            // domain from which the roots come
    domain_size: usize,
) -> Vec<F> {
    let N = domain.size();
    assert_eq!(N, 1 << domain_size, "Domain size mismatch");

    // Get set K params
    let mut start = Instant::now();
    let mut cache = InvertPolyCache::<F>::new();
    let update_params: UpdateParamsSetK<F> = UpdateParamsSetK::new(set_k, domain_size, &mut cache);
    println!("Computed update params in {} secs", start.elapsed().as_secs());

    // Get oracles for ZKHat and derivative
    start = Instant::now();
    let zk_hat_oracle: ZkHatOracle<F> = ZkHatOracle::new(set_i, &update_params, domain_size);
    println!("Computed oracles on set I in {} secs", start.elapsed().as_secs());

    // Step 1: Interpolate the polynomial q, such that p(X) = \hat{Z_K}(X).q(X)
    let mut q_evals_K: Vec<F> = Vec::new();

    for i in 0..update_params.set_k.len() {
        let t_j: F = F::from(t_j_vec[i] as u128);
        q_evals_K.push(t_j.div(zk_hat_oracle.zk_hat_eval[i]));
    }

    start = Instant::now();
    let q_poly: DensePolynomial<F> = fast_poly_interpolate_with_pp(
        update_params.set_hk.as_slice(),
        q_evals_K.as_slice(),
        &update_params.zk_dvt_poly_evals,
            &update_params.sub_products
    );
    println!("Interpolated q polynomial in {} secs", start.elapsed().as_secs());

    let q0 = q_poly.coeffs[0];
    let mut q_poly_dvt_coeffs: Vec<F> = Vec::new();
    for i in 1..=q_poly.degree() {
        q_poly_dvt_coeffs.push(F::from(i as u128) * q_poly.coeffs[i]);
    }

    let mut h_i_vec: Vec<F> = Vec::new();
    for i in 0..set_i.len() {
        h_i_vec.push(domain.element(set_i[i]));
    }

    start = Instant::now();
    let q_dvt_evals_K = fast_poly_evaluate(q_poly_dvt_coeffs.as_slice(), h_i_vec.as_slice());
    println!("Evaluated q_dvt on I in {} secs", start.elapsed().as_secs());
    // what we have: q(X), q'(X), \hat{Z_K}(X) and \hat{Z'_K(X)} all available over set I
    // we compute p'(w^i) = q'(w^i)\hat{Z_K}(w^i) + q(w^i)\hat{Z'K}(w^i)
    let mut p_dvt_evals_I: Vec<F> = Vec::new();
    for i in 0..set_i.len() {
        let term = q_evals_K[i].mul(zk_hat_oracle.zk_hat_dvt_eval[i]) + q_dvt_evals_K[i].mul(zk_hat_oracle.zk_hat_eval[i]);
        p_dvt_evals_I.push(term);
    }

    let neg_p0 = q0 * update_params.zk_poly.coeffs[0].inverse().unwrap();
    let fN = F::from(N as u128);
    let fN1 = F::from((N-1) as u128).div(F::from(2u128));
    let mut e_evals_I: Vec<F> = Vec::new();
    for i in 0..set_i.len() {
        let idx = set_i[i];
        let r_term = fN.mul(domain.element((2 * N - idx) % N)).mul(F::from(t_j_vec[i] as u128) + neg_p0);
        let g_term = fN1.mul(domain.element((2*N - idx) % N)).mul(F::from(t_j_vec[i] as u128));
        e_evals_I.push(g_term.add(p_dvt_evals_I[i]) + r_term.neg());
    }

    start = Instant::now();
    let z_I = compute_vanishing_poly::<F>(&h_i_vec, 1);
    let mut zi_dvt_coeffs: Vec<F> = Vec::new();
    for i in 1..=z_I.degree() {
        zi_dvt_coeffs.push(F::from(i as u128) * z_I.coeffs[i]);
    }

    let z_I_evals_K = fast_poly_evaluate_with_pp(zi_dvt_coeffs.as_slice(),
                                                 &update_params.set_hk,
                                                 &update_params.sub_products,
                                                 &mut cache);
    println!("Evaluated z_I_dvt on set H_K in {} secs", start.elapsed().as_secs());
    e_evals_I
}

pub fn compute_reciprocal_sum_naive<F: PrimeField>(
    t_j_vec: &Vec<usize>,                           // vector defined for j\in K
    set_k: &Vec<usize>,                             // set K over which summation runs for individual multipliers
    set_i: &Vec<usize>,                             // the set I over which we need sums
    domain: &GeneralEvaluationDomain<F>,            // domain from which the roots come
    domain_size: usize,
) -> Vec<F> {

    let mut e_evals_I: Vec<F> = Vec::new();
    for i in 0..set_i.len() {
        let mut sum = F::zero();
        for j in 0..set_k.len() {
            if i.eq(&j) {
                continue;
            }
            let denom = domain.element(set_i[i]) - domain.element(set_k[j]);
            let num = F::from(t_j_vec[j] as u128);
            sum.add_assign(num.div(denom));

        }
        e_evals_I.push(sum);
    }

    e_evals_I
}

mod tests {
    use ark_bls12_381::Bls12_381;
    use ark_ec::PairingEngine;
    use super::*;

    #[test]
    pub fn test_reciprocal_sum()
    {
        test_reciprocal_sum_helper::<Bls12_381>();
    }


    fn test_reciprocal_sum_helper<E: PairingEngine>()
    {
        let h_domain_size = 22usize;
        let i_set_size = 1usize << 7;
        let k_set_size = 1usize << 14;

        let i_set = (0..i_set_size).into_iter().collect::<Vec<_>>();
        let k_set = (0..k_set_size).into_iter().collect::<Vec<_>>();
        let h_domain: GeneralEvaluationDomain<E::Fr> = GeneralEvaluationDomain::new(1 << h_domain_size).unwrap();

        let t_j_vec = k_set.clone();
        let mut start = Instant::now();
        let evals_I = compute_reciprocal_sum(&t_j_vec, &k_set, &i_set, &h_domain, h_domain_size);
        println!("Efficient computation took {} secs", start.elapsed().as_millis());

        let mut start = Instant::now();
        let evals_I_naive = compute_reciprocal_sum_naive(&t_j_vec, &k_set, &i_set, &h_domain, h_domain_size);
        println!("Naive computation took {} secs", start.elapsed().as_secs());

        for i in 0..evals_I.len() {
            assert_eq!(evals_I[i], evals_I_naive[i], "Vectors don't match at {}", i);
        }
    }


}