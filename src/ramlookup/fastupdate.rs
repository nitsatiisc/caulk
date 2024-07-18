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
                h_domain.element(update_params.set_k[i]).mul(zk_dvt_eval[i])
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

pub fn compute_scalar_coefficients_naive<F: PrimeField>(
    t_j_vec: &Vec<F>,
    c_i_vec: &Vec<F>,
    set_k: &Vec<usize>,
    set_i: &Vec<usize>,
    domain_size: usize
) -> (Vec<F>, Vec<F>)
{
    let h_domain: GeneralEvaluationDomain<F> = GeneralEvaluationDomain::new(1usize << domain_size).unwrap();
    let mut adj_t_j_vec: Vec<F> = Vec::new();
    for j in 0..t_j_vec.len() {
        adj_t_j_vec.push(t_j_vec[j] * h_domain.element(set_k[j]));
    }

    let a_vec = compute_reciprocal_sum_naive::<F>(
        &adj_t_j_vec,
        &set_k,
        &set_i,
        &h_domain,
        domain_size
    );

    let b_vec = compute_reciprocal_sum_naive::<F>(
        &c_i_vec,
        &set_i,
        &set_k,
        &h_domain,
        domain_size
    );

    (a_vec, b_vec)

}

pub fn compute_scalar_coefficients<F: PrimeField>(
    t_j_vec: &Vec<F>,                           // Delta t_j vector for j\in K
    c_i_vec: &Vec<F>,                               // c_i for all i \in I
    set_k: &Vec<usize>,                             // set K
    set_i: &Vec<usize>,                             // set I\subseteq K
    domain_size: usize,                             // size of subgroup of roots of unity
    cache: &mut InvertPolyCache<F>,
) -> (Vec<F>, Vec<F>) {

    // broad steps:
    // to compute a_i, i\in K, define adj_t_j_vec[j] = xi^j t_j_vec[j] for all j\in K
    // compute a_i's using the reciprocal sum routine.

    // to compute b_i, i\in I, call reciprocal sum routine with c_i_vec, and set_k=set_i
    // to compute b_i, K\minus I,
    // interpolate C(X) such that C(\xi^j) = Z_I'(\xi^j).c_i_vec[j] for j\in I
    // evaluate C(\xi^j) for j\in K
    // compute b_j, for j\in K\minus I as C(\xi^j)/Z_I(\xi^j).

    let h_domain: GeneralEvaluationDomain<F> = GeneralEvaluationDomain::new(1usize << domain_size).unwrap();
    let mut adj_t_j_vec: Vec<F> = Vec::new();
    for j in 0..t_j_vec.len() {
        adj_t_j_vec.push(t_j_vec[j] * h_domain.element(set_k[j]));
    }

    let mut start = Instant::now();
    let (mut b_vec, _) = compute_reciprocal_sum::<F>(
        c_i_vec,
        set_i,
        set_i,
        &h_domain,
        domain_size,
        cache
    );
    println!("Computing b_vec over I took {} msec", start.elapsed().as_millis());



    start = Instant::now();
    let (a_vec, update_params) = compute_reciprocal_sum::<F>(
        &adj_t_j_vec,
        set_k,
        set_i,
        &h_domain,
        domain_size,
        cache
    );
    println!("Computing a_vec over K took {} msec", start.elapsed().as_millis());

    let mut h_i_vec: Vec<F> = Vec::new();
    for i in 0..set_i.len() {
        h_i_vec.push(h_domain.element(set_i[i]));
    }

    let z_I = compute_vanishing_poly::<F>(&h_i_vec, 1);
    let mut zi_dvt_coeffs: Vec<F> = Vec::new();
    for i in 1..=z_I.degree() {
        zi_dvt_coeffs.push(F::from(i as u128) * z_I.coeffs[i]);
    }

    start = Instant::now();
    let z_I_dvt_evals_I = fast_poly_evaluate(zi_dvt_coeffs.as_slice(), &h_i_vec);
    println!("Evaluating Z_I'(X) over I took {} msec", start.elapsed().as_millis());

    start = Instant::now();
    let z_I_evals_K = fast_poly_evaluate_with_pp(
        &z_I.coeffs,
        &update_params.set_hk,
        &update_params.sub_products,
        cache
    );
    println!("Evaluating Z_I(X) over K took {} msec", start.elapsed().as_millis());

    let mut c_poly_lagrange_coeffs: Vec<F> = Vec::new();
    for i in 0..set_i.len() {
        c_poly_lagrange_coeffs.push(c_i_vec[i] * z_I_dvt_evals_I[i]);
    }

    // interpolate polynomial C(X)
    start = Instant::now();
    let c_poly = fast_poly_interpolate(&h_i_vec, &c_poly_lagrange_coeffs);
    println!("Interpolating C(X) took {} msec", start.elapsed().as_millis());

    // check that C(X) is correctly interpolated
    for i in 0..set_i.len() {
        let lhs = c_poly.evaluate(&h_i_vec[i]);
        let rhs = c_i_vec[i] * z_I_dvt_evals_I[i];
        assert_eq!(lhs, rhs, "lhs != rhs at i={}",i);
    }

    // evaluate C(X) on set K
    start = Instant::now();
    let c_evals_K = fast_poly_evaluate_with_pp(
        &c_poly.coeffs,
        &update_params.set_hk,
        &update_params.sub_products,
        cache
    );


    println!("Evaluating C(X) over K took {} msec", start.elapsed().as_millis());

    // check that C(X) is correctly evaluated
    for i in 0..update_params.set_hk.len() {
        let lhs = c_poly.evaluate(&update_params.set_hk[i]);
        let rhs = c_evals_K[i];
        assert_eq!(lhs, rhs, "lhs != rhs at i={}",i);
    }



    // extend the b vector
    for i in set_i.len()..set_k.len() {
        b_vec.push(c_evals_K[i].div(z_I_evals_K[i]));
    }

    (a_vec, b_vec)
}


// consider taking cache from the caller.
pub fn compute_reciprocal_sum<F: PrimeField>(
    t_j_vec: &Vec<F>,                           // vector defined for j\in K
    set_k: &Vec<usize>,                             // set K over which summation runs for individual multipliers
    set_i: &Vec<usize>,                             // the set I over which we need sums
    domain: &GeneralEvaluationDomain<F>,            // domain from which the roots come
    domain_size: usize,
    cache: &mut InvertPolyCache<F>,
) -> (Vec<F>, UpdateParamsSetK<F>) {
    let N = domain.size();
    assert_eq!(N, 1 << domain_size, "Domain size mismatch");

    // Get set K params
    let mut start = Instant::now();
    //let mut cache = InvertPolyCache::<F>::new();
    let update_params: UpdateParamsSetK<F> = UpdateParamsSetK::new(set_k, domain_size, cache);
    println!("Computed update params in {} secs", start.elapsed().as_secs());

    // Get oracles for ZKHat and derivative
    start = Instant::now();
    let zk_hat_oracle: ZkHatOracle<F> = ZkHatOracle::new(set_i, &update_params, domain_size);
    println!("Computed oracles on set I in {} secs", start.elapsed().as_secs());

    // Step 1: Interpolate the polynomial q, such that p(X) = \hat{Z_K}(X).q(X)
    let mut q_evals_K: Vec<F> = Vec::new();

    for i in 0..update_params.set_k.len() {
        q_evals_K.push(t_j_vec[i].div(zk_hat_oracle.zk_hat_eval[i]));
    }

    start = Instant::now();
    let q_poly: DensePolynomial<F> = fast_poly_interpolate_with_pp(
        update_params.set_hk.as_slice(),
        q_evals_K.as_slice(),
        &update_params.zk_dvt_poly_evals,
        &update_params.sub_products
    );
    println!("Interpolated q polynomial in {} secs", start.elapsed().as_secs());
    let mut q0 = F::zero();
    if q_poly.coeffs.len() > 0 {
        q0 = q_poly.coeffs[0];
    }

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
        let r_term = fN.mul(domain.element((2 * N - idx) % N)).mul(t_j_vec[i] + neg_p0);
        let g_term = fN1.mul(domain.element((2*N - idx) % N)).mul(t_j_vec[i]);
        e_evals_I.push(g_term.add(p_dvt_evals_I[i]) + r_term.neg());
    }

    //start = Instant::now();
    //let z_I = compute_vanishing_poly::<F>(&h_i_vec, 1);
    //let mut zi_dvt_coeffs: Vec<F> = Vec::new();
    //for i in 1..=z_I.degree() {
    //    zi_dvt_coeffs.push(F::from(i as u128) * z_I.coeffs[i]);
    //}

    //let z_I_evals_K = fast_poly_evaluate_with_pp(zi_dvt_coeffs.as_slice(),
    //                                             &update_params.set_hk,
    //                                             &update_params.sub_products,
    //                                             cache);
    // println!("Evaluated z_I_dvt on set H_K in {} secs", start.elapsed().as_secs());
    (e_evals_I, update_params)
}

pub fn compute_reciprocal_sum_naive<F: PrimeField>(
    t_j_vec: &Vec<F>,                           // vector defined for j\in K
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
            let num = t_j_vec[j];
            sum.add_assign(num.div(denom));

        }
        e_evals_I.push(sum);
    }

    e_evals_I
}

mod tests {
    use ark_bls12_381::Bls12_381;
    use ark_ec::PairingEngine;
    use ark_ff::One;
    use ark_std::UniformRand;
    use super::*;

    #[test]
    pub fn test_reciprocal_sum()
    {
        test_reciprocal_sum_helper::<Bls12_381>();
    }

    #[test]
    pub fn test_scalar_coefficients()
    {
        test_scalar_coefficients_benchmark::<Bls12_381>();
    }


    fn test_scalar_coefficients_benchmark<E: PairingEngine>()
    {
        let h_domain_size = 20usize;
        let i_set_size = 1usize << 6;
        let k_set_size = 1usize << 7;
        let mut rng = ark_std::test_rng();

        let i_set = (0..i_set_size).into_iter().collect::<Vec<_>>();
        let k_set = (0..k_set_size).into_iter().collect::<Vec<_>>();

        let mut c_i_vec: Vec<E::Fr> = Vec::new();
        let mut t_j_vec: Vec<E::Fr> = Vec::new();

        for i in 0..i_set.len() {
            c_i_vec.push(E::Fr::rand(&mut rng));
        }

        for i in 0..k_set.len() {
            t_j_vec.push(E::Fr::rand(&mut rng));
        }

        let mut cache = InvertPolyCache::<E::Fr>::new();

        let mut start = Instant::now();
        let (a_vec, b_vec) = compute_scalar_coefficients(
            &t_j_vec,
            &c_i_vec,
            &k_set,
            &i_set,
            h_domain_size,
            &mut cache
        );
        println!("Efficient computation took {} msec", start.elapsed().as_millis());

        start = Instant::now();
        let (a_vec_naive, b_vec_naive) = compute_scalar_coefficients_naive(
            &t_j_vec,
            &c_i_vec,
            &k_set,
            &i_set,
            h_domain_size,
        );
        println!("Naive computation took {} msec", start.elapsed().as_millis());

        for i in 0..a_vec.len() {
            assert_eq!(a_vec[i], a_vec_naive[i], "a_vec mismatch");
        }

        for i in 0..b_vec.len() {
            assert_eq!(b_vec[i], b_vec_naive[i], "b_vec mismatch at i = {}", i);
        }

    }


    fn test_reciprocal_sum_helper<E: PairingEngine>()
    {
        let h_domain_size = 22usize;
        let i_set_size = 1usize << 10;
        let k_set_size = 1usize << 18;

        let i_set = (0..i_set_size).into_iter().collect::<Vec<_>>();
        let k_set = (0..k_set_size).into_iter().collect::<Vec<_>>();
        let h_domain: GeneralEvaluationDomain<E::Fr> = GeneralEvaluationDomain::new(1 << h_domain_size).unwrap();

        let t_j_vec = k_set.clone().into_iter().map(|x| E::Fr::from(x as u128)).collect::<Vec<_>>();
        let mut start = Instant::now();
        let mut cache: InvertPolyCache<E::Fr> = InvertPolyCache::new();
        let evals_I = compute_reciprocal_sum(&t_j_vec, &k_set, &i_set, &h_domain, h_domain_size, &mut cache);
        println!("Efficient computation took {} secs", start.elapsed().as_millis());

        let mut start = Instant::now();
        let evals_I_naive = compute_reciprocal_sum_naive(&t_j_vec, &k_set, &i_set, &h_domain, h_domain_size);
        println!("Naive computation took {} secs", start.elapsed().as_secs());


    }


}