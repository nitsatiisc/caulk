use ark_ff::PrimeField;
use ark_poly::{EvaluationDomain, GeneralEvaluationDomain, Polynomial, UVPolynomial};
use ark_poly::univariate::DensePolynomial;
use crate::compute_vanishing_poly;

#[allow(non_snake_case)]
pub struct UpdateParamsSetK<F: PrimeField> {
    pub set_k: Vec<usize>,                  // indices of set K
    pub set_hk: Vec<F>,                     // set H_K = \xi^i for i in K
    pub zk_poly: DensePolynomial<F>,        // vanishing polynomial Z_K of H_K
    pub zk_dvt_poly: DensePolynomial<F>,    // derivative of Z_K
    pub Fk_poly: DensePolynomial<F>,        // polynomial F_K
}

#[allow(non_snake_case)]
impl<F: PrimeField> UpdateParamsSetK<F> {
    pub fn new(set_k: &Vec<usize>, h_domain_size: usize) -> Self {
        let h_domain: GeneralEvaluationDomain<F> = GeneralEvaluationDomain::new(h_domain_size).unwrap();
        let mut set_hk: Vec<F> = Vec::new();
        for i in 0..set_k.len() {
            set_hk.push(h_domain.element( set_k[i]));
        }
        let zk_poly = compute_vanishing_poly::<F>(&set_hk, 1);
        let mut zk_dvt_vec: Vec<F> = Vec::new();
        for i in 1..=zk_poly.degree() {
            zk_dvt_vec.push(F::from(i as u128) * zk_poly.coeffs[i]);
        }
        let zk_dvt_poly = DensePolynomial::<F>::from_coefficients_vec(zk_dvt_vec);

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
        }
    }
}

