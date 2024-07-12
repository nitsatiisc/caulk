// This file includes an algorithm for calculating n openings of a KZG vector
// commitment of size n in n log(n) time. The algorithm is by Feist and
// khovratovich. It is useful for preprocessing.
// The full algorithm is described here https://github.com/khovratovich/Kate/blob/master/Kate_amortized.pdf

use std::collections::HashMap;
use std::fmt::DebugMap;
use std::ops::{Add, Div, Mul, Neg, Sub};
use ark_ec::{PairingEngine, ProjectiveCurve};
use ark_ff::{PrimeField, Zero};
use ark_ec::msm::VariableBaseMSM;
use ark_poly::{univariate::DensePolynomial, EvaluationDomain, GeneralEvaluationDomain, UVPolynomial, Polynomial};
use ark_std::{end_timer, start_timer};
use std::vec::Vec;
use ark_serialize::CanonicalSerialize;
use std::time::{Instant};
use ark_poly::univariate::DenseOrSparsePolynomial;

pub struct InvertPolyCache<F: PrimeField> {
    pub invert_poly_map: HashMap<(usize, usize), DensePolynomial<F>>,
    pub cache_hits: usize,
    pub cache_miss: usize
}

impl<F: PrimeField> InvertPolyCache<F> {
    pub fn new() -> Self {
        let invert_poly_map: HashMap<(usize, usize), DensePolynomial<F>> = HashMap::new();
        InvertPolyCache {
            invert_poly_map,
            cache_hits: 0usize,
            cache_miss: 0usize,

        }
    }
}

// We assume the size of set roots is a power of 2
pub fn compute_vanishing_poly<F>(
    roots: &[F],    // roots of vanishing polynomial
    p: usize,       // log of domain size
) -> DensePolynomial<F>
where
    F: PrimeField
{
    let roots: Vec<F> = roots.to_vec();
    let nroots: usize = roots.len();
    let mut result: DensePolynomial<F> = DensePolynomial::zero();
    let start = Instant::now();

    // compute initial polynomials as products of consecutive monomials
    let mut poly_vec: Vec<DensePolynomial<F>> = Vec::new();
    for i in 0..nroots {
        poly_vec.push(DensePolynomial::from_coefficients_vec(vec![ roots[i].neg(), F::from(1u128)]));

    }

    let mut chunk_size: usize = nroots/2;
    while chunk_size > 0 {
        for i in 0..chunk_size {
            poly_vec[i] = &poly_vec[i] * &poly_vec[i+chunk_size];
        }
        chunk_size = chunk_size/2;
    }

    result = poly_vec[0].clone();
    println!("Time taken: {}", start.elapsed().as_secs());
    result
}

pub fn compute_vanishing_poly_with_subproducts<F: PrimeField>(
    points: &[F],
    p: usize,               // log of degree
) -> (DensePolynomial<F>, Vec<DensePolynomial<F> >) {

    let r = points.len();
    let mut sub_products: Vec<DensePolynomial<F>> = Vec::new();
    sub_products.resize(2*r-1, DensePolynomial::<F>::zero());
    // initialize the final layer of monomials
    for i in 0usize..r {
        sub_products[r-1+i] = DensePolynomial::from_coefficients_vec(vec![points[i].neg(), F::from(1u128)]);
    }

    // compute sub-products, we skip computing the final subproduct which is the full vanishing polynomial
    for i in (0usize..(r-1)).rev() {
        let j = 2*i+1;
        sub_products[i] = &sub_products[j] * &sub_products[j+1];
    }

    (sub_products[0].clone(), sub_products)
}
pub fn fast_invert_poly<F>(
    coeffs: &[F],               // coefficients of the polynomial
    l: usize                    // l denoting the numerator X^l
) -> DensePolynomial<F>
where F : PrimeField
{
    let mut result: DensePolynomial<F> = DensePolynomial::zero();
    let mut g: DensePolynomial<F> = DensePolynomial::from_coefficients_vec(vec![coeffs[0].inverse().unwrap()]);
    let mut degree_bound:usize = 2;

    for i  in 0usize..(ark_std::log2(l) as usize)  {
        let eval_domain: GeneralEvaluationDomain<F> = GeneralEvaluationDomain::new(2*degree_bound).unwrap();
        let g_eval = g.evaluate_over_domain_by_ref(eval_domain);
        let g_sq_eval = g_eval.mul(&g_eval);

        // reduce f mod x^{degree bound} if deg(f) >= degree_bound.
        let mut f_coeffs = coeffs.to_vec();
        f_coeffs.resize(degree_bound, F::zero());
        let mut fred: DensePolynomial<F> = DensePolynomial::from_coefficients_vec(f_coeffs);

        let f_eval = fred.evaluate_over_domain_by_ref(eval_domain);
        let f_sq_eval = f_eval.mul(&g_sq_eval);
        let res_eval = g_eval.add(&g_eval).sub(&f_sq_eval);
        let res = res_eval.interpolate_by_ref();
        let mut g_coeffs = res.coeffs;
        g_coeffs.resize(degree_bound, F::zero());
        g = DensePolynomial::from_coefficients_vec(g_coeffs);
        degree_bound *= 2;
    }

    let mut g_coeffs = g.coeffs;
    g_coeffs.resize(l, F::zero());
    result = DensePolynomial::from_coefficients_vec(g_coeffs);
    //println!("Polynomial g(X): {:?}", result.to_vec().into_iter().map(|x| x.to_string()).collect::<Vec<String>>());
    result
}

pub fn fast_div_poly<F>(
    poly_f_coeffs: &[F],
    poly_g_coeffs: &[F],
) -> (DensePolynomial<F>, DensePolynomial<F>)
where
    F: PrimeField
{
    let mut quotient: DensePolynomial<F> = DensePolynomial::zero();
    let mut remainder: DensePolynomial<F> = DensePolynomial::zero();

    let poly_f:DensePolynomial<F> = DensePolynomial::from_coefficients_vec(poly_f_coeffs.to_vec());
    let poly_g:DensePolynomial<F> = DensePolynomial::from_coefficients_vec(poly_g_coeffs.to_vec());

    if poly_f.degree() < poly_g.degree() {
        return (DensePolynomial::<F>::zero(), poly_f);
    }

    // for small degree polynomials, it is faster to do
    // the naive division.
    if poly_f.degree() < 1000 {
        return DenseOrSparsePolynomial::divide_with_q_and_r(
            &(&poly_f).into(),
            &(&poly_g).into()
        ).unwrap();
    }

    let l = poly_f.degree() - poly_g.degree() + 1;

    let poly_f_rev_coeffs: Vec<F> = poly_f_coeffs.iter().copied().rev().collect::<Vec<F>>();
    let poly_g_rev_coeffs: Vec<F> = poly_g_coeffs.iter().copied().rev().collect::<Vec<F>>();

    let poly_inv_rev_g = fast_invert_poly(&poly_g_rev_coeffs, l);
    let poly_f_rev: DensePolynomial<F> = DensePolynomial::from_coefficients_vec(poly_f_rev_coeffs);
    quotient = &poly_f_rev * &poly_inv_rev_g;

    let mut quotient_coeffs: Vec<F> = quotient.coeffs;
    quotient_coeffs.resize(l,F::zero());

    // ensure that polynomial (reversed quotient) has the correct size
    quotient_coeffs.reverse();
    quotient = DensePolynomial::from_coefficients_vec(quotient_coeffs);
    remainder = &poly_f + &(&poly_g * &quotient).neg();

    (quotient, remainder)
}

pub fn fast_div_poly_cache<F>(
    poly_f_coeffs: &[F],
    poly_g_index: usize,
    sub_products: &Vec<DensePolynomial<F>>,
    cache: &mut InvertPolyCache<F>
) -> (DensePolynomial<F>, DensePolynomial<F>)
    where
        F: PrimeField
{
    let mut quotient: DensePolynomial<F> = DensePolynomial::zero();
    let mut remainder: DensePolynomial<F> = DensePolynomial::zero();

    let poly_f:DensePolynomial<F> = DensePolynomial::from_coefficients_vec(poly_f_coeffs.to_vec());
    //let poly_g:DensePolynomial<F> = DensePolynomial::from_coefficients_vec(poly_g_coeffs.to_vec());
    let poly_g = &sub_products[poly_g_index];
    if poly_f.degree() < poly_g.degree() {
        return (DensePolynomial::<F>::zero(), poly_f);
    }


    let l = poly_f.degree() - poly_g.degree() + 1;
    //@todo Disable the cache for now, as cache handling is incorrect. We only need reciprocal of X^l/g in cache. Fix later
    cache.invert_poly_map.clear();
    match cache.invert_poly_map.contains_key(&(poly_g_index, l)) {
        true => { quotient = cache.invert_poly_map.get(&(poly_g_index, l)).unwrap().clone(); cache.cache_hits += 1; }
        false => {
            // for small degree polynomials, it is faster to do
            // the naive division.
            cache.cache_miss += 1;
            if poly_f.degree() < 1000 {
                (quotient, remainder) = DenseOrSparsePolynomial::divide_with_q_and_r(
                    &(&poly_f).into(),
                    &(poly_g).into()
                ).unwrap();
                cache.invert_poly_map.insert((poly_g_index, l), quotient.clone());
                return (quotient, remainder);
            }

            let poly_g_coeffs = &poly_g.coeffs;
            let poly_f_rev_coeffs: Vec<F> = poly_f_coeffs.iter().copied().rev().collect::<Vec<F>>();
            let poly_g_rev_coeffs: Vec<F> = poly_g_coeffs.iter().copied().rev().collect::<Vec<F>>();

            let poly_inv_rev_g = fast_invert_poly(&poly_g_rev_coeffs, l);
            let poly_f_rev: DensePolynomial<F> = DensePolynomial::from_coefficients_vec(poly_f_rev_coeffs);
            quotient = &poly_f_rev * &poly_inv_rev_g;

            let mut quotient_coeffs: Vec<F> = quotient.coeffs;
            quotient_coeffs.resize(l,F::zero());
            quotient_coeffs.reverse();
            quotient = DensePolynomial::from_coefficients_vec(quotient_coeffs);
            cache.invert_poly_map.insert((poly_g_index, l), quotient.clone());
        }
    }

    // ensure that polynomial (reversed quotient) has the correct size
    remainder = &poly_f + &(poly_g * &quotient).neg();

    (quotient, remainder)
}





pub fn fast_poly_evaluate<F>(
    coeffs: &[F],
    points: &[F]
) -> Vec<F> where
    F: PrimeField
{
    let mut evaluations: Vec<F> = Vec::new();
    let coeffs = coeffs.to_vec();
    let points = points.to_vec();

    let r = points.len();

    let mut start = Instant::now();
    let mut sub_products: Vec<DensePolynomial<F>> = Vec::new();
    sub_products.resize(2*r-1, DensePolynomial::<F>::zero());
    // initialize the final layer of monomials
    for i in 0usize..r {
        sub_products[r-1+i] = DensePolynomial::from_coefficients_vec(vec![points[i].neg(), F::from(1u128)]);
    }

    // compute sub-products, we skip computing the final subproduct which is the full vanishing polynomial
    for i in (1usize..(r-1)).rev() {
        let j = 2*i+1;
        sub_products[i] = &sub_products[j] * &sub_products[j+1];
    }
    println!("Time for sub-products = {}", start.elapsed().as_secs());

    let mut evaluation_polys: Vec<DensePolynomial<F>> = Vec::new();
    evaluation_polys.resize(2*r-1, DensePolynomial::<F>::zero());
    evaluation_polys[0] = DensePolynomial::from_coefficients_vec(coeffs);

    start = Instant::now();
    for i in 1usize..(2*r-1) {
        let (_, rem) = fast_div_poly(&evaluation_polys[(i-1)/2].coeffs, &sub_products[i].coeffs );
        evaluation_polys[i] = rem;
    }
    println!("Time for divisions = {}", start.elapsed().as_secs());

    for i in 0..r {
        if evaluation_polys[r-1+i].coeffs.len() > 0 {
            evaluations.push(evaluation_polys[r - 1 + i].coeffs[0]);
        } else {
            evaluations.push(F::zero());
        }
    }

    evaluations
}

pub fn fast_poly_evaluate_with_pp<F>(
    coeffs: &[F],
    points: &[F],
    sub_products: &Vec<DensePolynomial<F>>,
    cache: &mut InvertPolyCache<F>,

) -> Vec<F> where
    F: PrimeField
{
    let mut evaluations: Vec<F> = Vec::new();
    let coeffs = coeffs.to_vec();
    let points = points.to_vec();

    let r = points.len();
    assert_eq!(sub_products.len(), 2*r-1, "Wrong length of sub_products");

    let mut evaluation_polys: Vec<DensePolynomial<F>> = Vec::new();
    evaluation_polys.resize(2*r-1, DensePolynomial::<F>::zero());
    evaluation_polys[0] = DensePolynomial::from_coefficients_vec(coeffs);

    let mut start = Instant::now();
    for i in 1usize..(2*r-1) {
        let (_, rem) = fast_div_poly_cache(&evaluation_polys[(i-1)/2].coeffs, i, sub_products, cache);
        evaluation_polys[i] = rem;
    }
    println!("Time for divisions = {}", start.elapsed().as_secs());

    for i in 0..r {
        if evaluation_polys[r-1+i].coeffs.len() > 0 {
            evaluations.push(evaluation_polys[r - 1 + i].coeffs[0]);
        } else {
            evaluations.push(F::zero());
        }
    }

    evaluations
}



pub fn fast_poly_interpolate<F>(
    points: &[F],
    values: &[F]
) -> DensePolynomial<F>
where
    F: PrimeField
{
    //let mut int_poly: DensePolynomial<F> = DensePolynomial::zero();
    let z_poly = compute_vanishing_poly(points, 1);
    let mut z_poly_dv_coeffs: Vec<F> = Vec::new();
    for i in 0usize..z_poly.degree() {
        z_poly_dv_coeffs.push(F::from((i+1) as u128)*z_poly.coeffs[i+1]);
    }
    let z_dv_poly = DensePolynomial::from_coefficients_vec(z_poly_dv_coeffs);
    let evaluations = fast_poly_evaluate(&z_dv_poly.coeffs, points);

    // compute sub-products
    let r= z_poly.degree();
    let mut sub_products: Vec<DensePolynomial<F>> = Vec::new();
    sub_products.resize(2*r-1, DensePolynomial::<F>::zero());

    let mut c_vec: Vec<DensePolynomial<F>> = Vec::new();
    c_vec.resize(2*r-1, DensePolynomial::zero());

    // initialize the final layer of monomials
    for i in 0usize..r {
        sub_products[r-1+i] = DensePolynomial::from_coefficients_vec(vec![points[i].neg(), F::from(1u128)]);
        c_vec[r-1+i] = DensePolynomial::from_coefficients_vec(vec![values[i] * evaluations[i].inverse().unwrap()]);
    }

    // compute sub-products, we skip computing the final subproduct which is the full vanishing polynomial
    for i in (1usize..(r-1)).rev() {
        let j = 2*i+1;
        sub_products[i] = &sub_products[j] * &sub_products[j+1];
    }

    for i in (0..(r-1)).rev() {
        let j = 2*i + 1;
        let prod1 = &c_vec[j] * &sub_products[j+1];
        let prod2 = &c_vec[j+1] * &sub_products[j];
        c_vec[i] = &prod1 + &prod2;
    }

    c_vec[0].clone()
}

pub fn fast_poly_interpolate_with_pp<F>(
    points: &[F],
    values: &[F],
    evaluations: &[F],          // pre-computed evaluations
    sub_products: &Vec<DensePolynomial<F>>,         // pre-computed sub-products
) -> DensePolynomial<F>
    where
        F: PrimeField
{
    let r = points.len();
    let mut c_vec: Vec<DensePolynomial<F>> = Vec::new();
    c_vec.resize(2*r-1, DensePolynomial::zero());

    // initialize the final layer of monomials
    for i in 0usize..r {
        c_vec[r-1+i] = DensePolynomial::from_coefficients_vec(vec![values[i] * evaluations[i].inverse().unwrap()]);
    }

    for i in (0..(r-1)).rev() {
        let j = 2*i + 1;
        let prod1 = &c_vec[j] * &sub_products[j+1];
        let prod2 = &c_vec[j+1] * &sub_products[j];
        c_vec[i] = &prod1 + &prod2;
    }

    c_vec[0].clone()
}



pub fn compute_polynomial_composition<F: PrimeField>(
    a_poly: &DensePolynomial<F>,
    b_poly: &DensePolynomial<F>,
) -> DensePolynomial<F> {

    DensePolynomial::<F>::from_coefficients_vec(vec![F::zero()])

}

pub fn field_fft_domain<F: PrimeField>(h: &[F], p: usize, input_domain: &GeneralEvaluationDomain<F>) -> Vec<F> {
    let dom_size = 1 << p;
    let timer = start_timer!(|| format!("size {} field dft", dom_size));
    let mut h = h.to_vec();
    h.resize(dom_size, F::zero());

    //assert_eq!(h.len(), dom_size); // we do not support inputs of size not power of 2
    //let input_domain: GeneralEvaluationDomain<F> = EvaluationDomain::new(dom_size).unwrap();
    let mut l = dom_size / 2;
    let mut m: usize = 1;
    // Stockham FFT
    let mut xvec = h.to_vec();
    for _ in 0..p {
        let mut xt = xvec.clone();
        for j in 0..l {
            for k in 0..m {
                let c0 = xvec[k + j * m];
                let c1 = xvec[k + j * m + l * m];
                xt[k + 2 * j * m] = c0 + c1;
                let wj_2l = input_domain.element((j * dom_size / (2 * l)) % dom_size);
                xt[k + 2 * j * m + m] = (c0 - c1) * (wj_2l);
            }
        }
        l /= 2;
        m *= 2;
        xvec = xt;
    }
    end_timer!(timer);
    xvec
}

pub fn field_ifft_domain<F: PrimeField>(h: &[F], p: usize, input_domain: &GeneralEvaluationDomain<F>) -> Vec<F> {
    let dom_size = 1 << p;
    let timer = start_timer!(|| format!("size {} field inverse dft", dom_size));
    let mut h = h.to_vec();
    h.resize(dom_size, F::zero());
    //assert_eq!(h.len(), dom_size); // we do not support inputs of size not power of 2
    //let input_domain: GeneralEvaluationDomain<F> = EvaluationDomain::new(dom_size).unwrap();
    let mut l = dom_size / 2;
    let mut m: usize = 1;
    // Stockham FFT
    let mut xvec = h.to_vec();
    for _ in 0..p {
        let mut xt = xvec.clone();
        for j in 0..l {
            for k in 0..m {
                let c0 = xvec[k + j * m];
                let c1 = xvec[k + j * m + l * m];
                xt[k + 2 * j * m] = c0 + c1;
                let wj_2l = input_domain
                    .element((dom_size - (j * dom_size / (2 * l)) % dom_size) % dom_size);
                xt[k + 2 * j * m + m] = (c0 - c1) * wj_2l; // Difference #1 to
                // forward DFT
            }
        }
        l /= 2;
        m *= 2;
        xvec = xt;
    }

    let domain_inverse = F::from((1u64 << p) as u128).inverse().unwrap();
    let res = xvec.iter().map(|&x| x * domain_inverse).collect();

    end_timer!(timer);
    res
}


// compute all pre-proofs using DFT
// h_i= c_d[x^{d-i-1}]+c_{d-1}[x^{d-i-2}]+c_{d-2}[x^{d-i-3}]+\cdots +
// c_{i+2}[x]+c_{i+1}[1]
pub fn compute_h<F, G>(
    c_poly: &DensePolynomial<F>, /* c(X) degree up to d<2^p , i.e. c_poly has at most d+1 coeffs
                                  * non-zero */
    powers: &[G], // SRS
    p: usize,
) -> Vec<G>
where
    F: PrimeField,
    G: ProjectiveCurve,
{
    let timer = start_timer!(|| "compute h");
    let mut coeffs = c_poly.coeffs().to_vec();
    let dom_size = 1 << p;
    let fpzero = F::zero();
    coeffs.resize(dom_size, fpzero);

    // 1. x_ext = [[x^(d-1)], [x^{d-2},...,[x],[1], d+2 [0]'s]
    let step1_timer = start_timer!(|| "step 1");
    let mut x_ext: Vec<G> = powers.iter().take(dom_size - 1).rev().copied().collect();
    x_ext.resize(2 * dom_size, G::zero()); // filling 2d+2 neutral elements
    let mut start = Instant::now();
    let y = group_dft::<F, G>(&x_ext, p + 1);
    println!("Group FFT for {} took {}", p+1, start.elapsed().as_secs());
    end_timer!(step1_timer);

    // 2. c_ext = [c_d, d zeroes, c_d,c_{0},c_1,...,c_{d-2},c_{d-1}]
    let step2_timer = start_timer!(|| "step 2");

    let mut c_ext = vec![coeffs[coeffs.len() - 1]];
    c_ext.resize(dom_size, fpzero);
    c_ext.push(coeffs[coeffs.len() - 1]);
    for &e in coeffs.iter().take(coeffs.len() - 1) {
        c_ext.push(e);
    }
    assert_eq!(c_ext.len(), 2 * dom_size);
    start = Instant::now();
    let v = field_dft::<F>(&c_ext, p + 1);
    println!("Field FFT for {} took {}", p+1, start.elapsed().as_secs());
    end_timer!(step2_timer);

    // 3. u = y o v
    let step3_timer = start_timer!(|| "step 3");
    let u: Vec<_> = y
        .into_iter()
        .zip(v.into_iter())
        .map(|(a, b)| a.mul(b.into_repr()))
        .collect();
    end_timer!(step3_timer);

    // 4. h_ext = idft_{2d+2}(u)
    let step4_timer = start_timer!(|| "step 4");
    start = Instant::now();
    let h_ext = group_inv_dft::<F, G>(&u, p + 1);
    println!("Group INV FFT for {} took {}", p+1, start.elapsed().as_secs());
    end_timer!(step4_timer);

    end_timer!(timer);
    h_ext[0..dom_size].to_vec()
}


// compute all pre-proofs using DFT
// h_i= c_d[x^{d-i-1}]+c_{d-1}[x^{d-i-2}]+c_{d-2}[x^{d-i-3}]+\cdots +
// c_{i+2}[x]+c_{i+1}[1]
pub fn compute_h_fake<F>(
    c_poly: &DensePolynomial<F>, /* c(X) degree up to d<2^p , i.e. c_poly has at most d+1 coeffs
                                  * non-zero */
    powers: &[F], // SRS
    p: usize,
) -> Vec<F>
    where
        F: PrimeField,
        //G: ProjectiveCurve,
{
    let timer = start_timer!(|| "compute h");
    let mut coeffs = c_poly.coeffs().to_vec();
    let dom_size = 1 << p;
    let fpzero = F::zero();
    coeffs.resize(dom_size, fpzero);

    // 1. x_ext = [[x^(d-1)], [x^{d-2},...,[x],[1], d+2 [0]'s]
    let step1_timer = start_timer!(|| "step 1");
    let mut x_ext: Vec<F> = powers.iter().take(dom_size - 1).rev().copied().collect();
    x_ext.resize(2 * dom_size, F::zero()); // filling 2d+2 neutral elements
    let mut start = Instant::now();
    let y = field_dft::<F>(&x_ext, p + 1);
    println!("Field FFT for {} took {}", p+1, start.elapsed().as_secs());
    end_timer!(step1_timer);

    // 2. c_ext = [c_d, d zeroes, c_d,c_{0},c_1,...,c_{d-2},c_{d-1}]
    let step2_timer = start_timer!(|| "step 2");

    let mut c_ext = vec![coeffs[coeffs.len() - 1]];
    c_ext.resize(dom_size, fpzero);
    c_ext.push(coeffs[coeffs.len() - 1]);
    for &e in coeffs.iter().take(coeffs.len() - 1) {
        c_ext.push(e);
    }
    assert_eq!(c_ext.len(), 2 * dom_size);
    start = Instant::now();
    let v = field_dft::<F>(&c_ext, p + 1);
    println!("Field FFT for {} took {}", p+1, start.elapsed().as_secs());
    end_timer!(step2_timer);

    // 3. u = y o v
    let step3_timer = start_timer!(|| "step 3");
    let u: Vec<_> = y
        .into_iter()
        .zip(v.into_iter())
        .map(|(a, b)| a.mul(&b))
        .collect();
    end_timer!(step3_timer);

    // 4. h_ext = idft_{2d+2}(u)
    let step4_timer = start_timer!(|| "step 4");
    start = Instant::now();
    let h_ext = field_inv_dft::<F>(&u, p + 1);
    println!("Field INV FFT for {} took {}", p+1, start.elapsed().as_secs());
    end_timer!(step4_timer);

    end_timer!(timer);
    h_ext[0..dom_size].to_vec()
}




// compute DFT of size @dom_size over vector of Fr elements
// q_i = h_0 + h_1w^i + h_2w^{2i}+\cdots + h_{dom_size-1}w^{(dom_size-1)i} for
// 0<= i< dom_size=2^p
pub fn group_dft<F, G>(h: &[G], p: usize) -> Vec<G>
where
    F: PrimeField,
    G: ProjectiveCurve,
{
    let dom_size = 1 << p;
    let timer = start_timer!(|| format!("size {} group dft", dom_size));
    assert_eq!(h.len(), dom_size); // we do not support inputs of size not power of 2
    let input_domain: GeneralEvaluationDomain<F> = EvaluationDomain::new(dom_size).unwrap();
    let mut l = dom_size / 2;
    let mut m: usize = 1;
    // Stockham FFT
    let mut xvec = h.to_vec();
    for _ in 0..p {
        let mut xt = xvec.clone();
        for j in 0..l {
            for k in 0..m {
                let c0 = xvec[k + j * m];
                let c1 = xvec[k + j * m + l * m];
                xt[k + 2 * j * m] = c0 + c1;
                let wj_2l = input_domain.element((j * dom_size / (2 * l)) % dom_size);
                xt[k + 2 * j * m + m] = (c0 - c1).mul(wj_2l.into_repr());
            }
        }
        l /= 2;
        m *= 2;
        xvec = xt;
    }
    end_timer!(timer);
    xvec
}

// compute DFT of size @dom_size over vector of Fr elements
// q_i = h_0 + h_1w^i + h_2w^{2i}+\cdots + h_{dom_size-1}w^{(dom_size-1)i} for
// 0<= i< dom_size=2^p
pub fn field_dft<F: PrimeField>(h: &[F], p: usize) -> Vec<F> {
    let dom_size = 1 << p;
    let timer = start_timer!(|| format!("size {} field dft", dom_size));
    assert_eq!(h.len(), dom_size); // we do not support inputs of size not power of 2
    let input_domain: GeneralEvaluationDomain<F> = EvaluationDomain::new(dom_size).unwrap();
    let mut l = dom_size / 2;
    let mut m: usize = 1;
    // Stockham FFT
    let mut xvec = h.to_vec();
    for _ in 0..p {
        let mut xt = xvec.clone();
        for j in 0..l {
            for k in 0..m {
                let c0 = xvec[k + j * m];
                let c1 = xvec[k + j * m + l * m];
                xt[k + 2 * j * m] = c0 + c1;
                let wj_2l = input_domain.element((j * dom_size / (2 * l)) % dom_size);
                xt[k + 2 * j * m + m] = (c0 - c1) * (wj_2l);
            }
        }
        l /= 2;
        m *= 2;
        xvec = xt;
    }
    end_timer!(timer);
    xvec
}

// compute idft of size @dom_size over vector of G1 elements
// q_i = (h_0 + h_1w^-i + h_2w^{-2i}+\cdots +
// h_{dom_size-1}w^{-(dom_size-1)i})/dom_size for 0<= i< dom_size=2^p
pub fn group_inv_dft<F, G>(h: &[G], p: usize) -> Vec<G>
where
    F: PrimeField,
    G: ProjectiveCurve,
{
    let dom_size = 1 << p;
    let timer = start_timer!(|| format!("size {} group inverse dft", dom_size));
    assert_eq!(h.len(), dom_size); // we do not support inputs of size not power of 2
    let input_domain: GeneralEvaluationDomain<F> = EvaluationDomain::new(dom_size).unwrap();
    let mut l = dom_size / 2;
    let mut m: usize = 1;
    // Stockham FFT
    let mut xvec = h.to_vec();
    for _ in 0..p {
        let mut xt = xvec.clone();
        for j in 0..l {
            for k in 0..m {
                let c0 = xvec[k + j * m];
                let c1 = xvec[k + j * m + l * m];
                xt[k + 2 * j * m] = c0 + c1;
                let wj_2l = input_domain
                    .element((dom_size - (j * dom_size / (2 * l)) % dom_size) % dom_size);
                xt[k + 2 * j * m + m] = (c0 - c1).mul(wj_2l.into_repr()); // Difference #1 to forward DFT
            }
        }
        l /= 2;
        m *= 2;
        xvec = xt;
    }

    let domain_inverse = F::from((1u64 << p) as u128).inverse().unwrap().into_repr();
    let res = xvec.iter().map(|x| x.mul(domain_inverse)).collect();

    end_timer!(timer);
    res
}

// compute idft of size @dom_size over vector of G1 elements
// q_i = (h_0 + h_1w^-i + h_2w^{-2i}+\cdots +
// h_{dom_size-1}w^{-(dom_size-1)i})/dom_size for 0<= i< dom_size=2^p
pub fn field_inv_dft<F: PrimeField>(h: &[F], p: usize) -> Vec<F> {
    let dom_size = 1 << p;
    let timer = start_timer!(|| format!("size {} field inverse dft", dom_size));
    assert_eq!(h.len(), dom_size); // we do not support inputs of size not power of 2
    let input_domain: GeneralEvaluationDomain<F> = EvaluationDomain::new(dom_size).unwrap();
    let mut l = dom_size / 2;
    let mut m: usize = 1;
    // Stockham FFT
    let mut xvec = h.to_vec();
    for _ in 0..p {
        let mut xt = xvec.clone();
        for j in 0..l {
            for k in 0..m {
                let c0 = xvec[k + j * m];
                let c1 = xvec[k + j * m + l * m];
                xt[k + 2 * j * m] = c0 + c1;
                let wj_2l = input_domain
                    .element((dom_size - (j * dom_size / (2 * l)) % dom_size) % dom_size);
                xt[k + 2 * j * m + m] = (c0 - c1) * wj_2l; // Difference #1 to
                                                           // forward DFT
            }
        }
        l /= 2;
        m *= 2;
        xvec = xt;
    }

    let domain_inverse = F::from((1u64 << p) as u128).inverse().unwrap();
    let res = xvec.iter().map(|&x| x * domain_inverse).collect();

    end_timer!(timer);
    res
}

#[cfg(test)]
pub mod tests {
    use std::ops::Neg;
    use super::*;
    use ark_bls12_377::Bls12_377;
    use ark_bls12_381::Bls12_381;
    use ark_ec::mnt4::G1Projective;
    use ark_ec::{AffineCurve, PairingEngine};
    use ark_std::{test_rng, UniformRand};

    #[test]
    fn test_vanishing_poly() {
        test_vanishing_poly_helper::<Bls12_381>();
    }

    #[test]
    fn test_msm() {
        test_msm_helper::<Bls12_381>();
    }

    #[test]
    fn test_fast_invert_poly()
    {
        test_invert_poly_helper::<Bls12_381>();
    }

    #[test]
    fn test_fast_polynomial_division()
    {
        test_fast_polynomial_division_helper::<Bls12_381>();
    }

    #[test]
    fn test_fast_polynomial_evaluation()
    {
        test_fast_poly_evaluate_helper::<Bls12_381>();
    }

    #[test]
    fn test_fast_polynomial_interpolation()
    {
        test_poly_interpolate_helper::<Bls12_381>();
    }

    #[test]
    fn test_fast_poly_mult()
    {
        test_poly_mult_helper::<Bls12_381>();
    }

    #[test]
    fn test_dft() {
        test_dft_helper::<Bls12_381>();
        test_dft_helper::<Bls12_377>();
    }

    fn test_vanishing_poly_helper<E: PairingEngine>() {
        let mut coeffs: Vec<E::Fr> = Vec::new();
        let mut rng = test_rng();
        let npolys:usize = 1024*256;
        for i in 1..npolys {
            coeffs.push(E::Fr::rand(&mut rng))
        }
            /*
            vec![
            E::Fr::from(1u128),
            E::Fr::from(2u128),
            E::Fr::from(3u128),
            E::Fr::from(4u128),
            E::Fr::from(5u128),
            E::Fr::from(6u128),
            E::Fr::from(7u128),
            E::Fr::from(8u128)
        ];
        */

        compute_vanishing_poly(coeffs.as_slice(), 1);
    }

    fn test_msm_helper<E: PairingEngine>() {
        let mut rng = test_rng();
        //use ark_test_curves::bls12_381:
        //use E::G1Projective as GProjective;
        //use E::G1Affine as GAffine;
        let k_domain_size: usize = 19;
        let vec_size: usize = 1024 + (1 << k_domain_size);
        let mut grp_vec: Vec<E::G1Affine> = Vec::new();
        let mut scalar_vec: Vec<<E::Fr as PrimeField>::BigInt> = Vec::new();

        for _ in 0..vec_size {
            grp_vec.push(E::G1Projective::rand(&mut rng).into_affine());
            scalar_vec.push(<E::Fr as PrimeField>::BigInt::rand(&mut rng));
        }

        let mut start = Instant::now();
        let prod = VariableBaseMSM::multi_scalar_mul(grp_vec.as_slice(), scalar_vec.as_slice());
        println!("MSM took {} secs", start.elapsed().as_millis());
        //println!("Product: {:?}", prod);

        let mut prod = E::G1Affine::zero();
        start = Instant::now();
        for i in 0..vec_size {
            prod = prod + (grp_vec[i].mul(scalar_vec[i])).into();
        }

        println!("Naive sum took {} secs", start.elapsed().as_secs());
    }

    fn test_invert_poly_helper<E: PairingEngine>() {
        let mut rng = test_rng();
        let f: Vec<E::Fr> = vec![
            E::Fr::from(1u128),
            E::Fr::from(1u128)
        ];

        fast_invert_poly(&f, 3);
    }

    fn test_fast_polynomial_division_helper<E: PairingEngine>() {
        let mut rng = test_rng();
        let f: Vec<E::Fr> = vec![
            E::Fr::from(1u128),
            E::Fr::zero(), E::Fr::zero(), E::Fr::zero(), E::Fr::zero(),
            E::Fr::from(1u128)
        ];

        let g: Vec<E::Fr> = vec![E::Fr::from(1u128), E::Fr::from(0u128), E::Fr::from(1u128)];

        let (q, r) = fast_div_poly(&f, &g);
        let f: DensePolynomial<E::Fr> = DensePolynomial::from_coefficients_vec(f);
        let g: DensePolynomial<E::Fr> = DensePolynomial::from_coefficients_vec(g);

        let f1 = &r + &(&g * &q);
        println!("q: {:?}, r: {:?}", q.to_vec().iter().map(|x| x.to_string()).collect::<Vec<String>>(), r);
        assert_eq!(f, f1);
    }

    fn test_fast_poly_evaluate_helper<E: PairingEngine>() {
        let mut rng = test_rng();
        let degree: usize = 1usize << 18;
        let npoints:usize = 1usize << 11;

        let coeffs: Vec<E::Fr> = vec![E::Fr::from(1u128), E::Fr::from(1u128), E::Fr::from(1u128)];
        let points: Vec<E::Fr> = vec![
            E::Fr::from(0u128),
            E::Fr::from(1u128),
            E::Fr::from(2u128),
            E::Fr::from(3u128),
        ];

        let rand_poly: DensePolynomial<E::Fr> = DensePolynomial::rand(degree, &mut rng);
        let points: Vec<E::Fr> = (1..=npoints).into_iter().map(|x| E::Fr::from(x as u128)).collect::<Vec<E::Fr>>();

        let mut start = Instant::now();
        let evaluations = fast_poly_evaluate(&rand_poly.coeffs, &points);
        println!("Evaluations took {} time", start.elapsed().as_secs());

        start = Instant::now();
        for i in 1..=npoints {
            let eval = rand_poly.evaluate(&E::Fr::from(i as u128));
            assert_eq!(eval, evaluations[i-1]);
        }
        println!("Naive evaluations took {} time", start.elapsed().as_secs());
        //println!("evaluations: {:?}", evaluations.iter().map(|x| x.to_string()).collect::<Vec<String>>());
    }

    fn test_poly_interpolate_helper<E: PairingEngine>() {
        let mut rng = test_rng();
        let npoints = 1usize << 10;
        let mut points: Vec<E::Fr> = Vec::new();
        let mut values: Vec<E::Fr> = Vec::new();

        for _ in 0usize..npoints {
            points.push(E::Fr::rand(&mut rng));
            values.push(E::Fr::rand(&mut rng));
        }

        let mut start = Instant::now();
        let poly_interpolate:DensePolynomial<E::Fr> = fast_poly_interpolate(&points, &values);
        println!("Polynomial Interpolation time {}", start.elapsed().as_secs());

        for i in 0usize..npoints {
            assert_eq!(values[i], poly_interpolate.evaluate(&points[i]));
        }
    }

    fn test_poly_mult_helper<E: PairingEngine>() {
        let mut rng = test_rng();

        let degree: usize = 1usize << 16;
        let npolys: usize = 100;
        let mut rand_A_polys: Vec<DensePolynomial<E::Fr>> = Vec::new();
        let mut rand_B_polys: Vec<DensePolynomial<E::Fr>> = Vec::new();
        let mut rand_C_polys: Vec<DensePolynomial<E::Fr>> = Vec::new();

        for i in 0..npolys {
            rand_A_polys.push(DensePolynomial::rand(degree, &mut rng));
            rand_B_polys.push(DensePolynomial::rand(degree, &mut rng));
        }

        let mut start = Instant::now();
        for i in 0..npolys {
            rand_C_polys.push(&rand_A_polys[i] * &rand_B_polys[i]);
        }
        println!("FFT multiplication took {} secs", start.elapsed().as_secs());

        rand_C_polys.clear();
        let mut start = Instant::now();
        let eval_domain: GeneralEvaluationDomain<E::Fr> = GeneralEvaluationDomain::new(2*degree).unwrap();
        for i in 0..npolys {
            let eval_a = rand_A_polys[i].evaluate_over_domain_by_ref(eval_domain);
            let eval_b = rand_B_polys[i].evaluate_over_domain_by_ref(eval_domain);
            let eval_c = eval_a.mul(&eval_b);
            let res = eval_c.interpolate_by_ref();
            rand_C_polys.push(res);
        }
        println!("FFT multiplication with eval domain took {} secs", start.elapsed().as_secs());
        rand_C_polys.clear();

        let input_domain: GeneralEvaluationDomain<E::Fr> = GeneralEvaluationDomain::new(1usize << 17).unwrap();

        start = Instant::now();
        let mut fft_C: Vec<E::Fr> = Vec::with_capacity(1usize << 17);
        fft_C.resize(1usize << 17, E::Fr::zero());

        for i in 0..npolys {
            let fft_A: Vec<E::Fr> = field_fft_domain(&rand_A_polys[i].coeffs, 17, &input_domain);
            let fft_B: Vec<E::Fr> = field_fft_domain(&rand_B_polys[i].coeffs, 17, &input_domain);
            for j in 0..fft_A.len() {
                fft_C[j] = fft_A[j] * fft_B[j];
            }
            let fft_res: Vec<E::Fr> = field_ifft_domain(&fft_C, 17, &input_domain);
            rand_C_polys.push(DensePolynomial::from_coefficients_vec(fft_res));
        }

        println!("FFT multiplication with eval domain took {} secs", start.elapsed().as_secs());
    }

    fn test_dft_helper<E: PairingEngine>() {
        let mut rng = test_rng();
        for i in 2..6 {
            let size = 1 << i;

            let h: Vec<E::Fr> = (0..size).map(|_| E::Fr::rand(&mut rng)).collect();

            let c_dft = field_dft::<E::Fr>(&h, i);
            let c_back = field_inv_dft::<E::Fr>(&c_dft, i);
            assert_eq!(h, c_back);

            let h: Vec<E::G1Projective> =
                (0..size).map(|_| E::G1Projective::rand(&mut rng)).collect();

            let c_dft = group_dft::<E::Fr, E::G1Projective>(&h, i);
            let c_back = group_inv_dft::<E::Fr, E::G1Projective>(&c_dft, i);
            assert_eq!(h, c_back);

            let h: Vec<E::G2Projective> =
                (0..size).map(|_| E::G2Projective::rand(&mut rng)).collect();

            let c_dft = group_dft::<E::Fr, E::G2Projective>(&h, i);
            let c_back = group_inv_dft::<E::Fr, E::G2Projective>(&c_dft, i);
            assert_eq!(h, c_back);
        }
    }
}
