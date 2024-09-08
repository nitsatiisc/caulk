// This file contains implementation of PLONK proof aggregation

use std::iter::zip;
use std::ops::{Add, Mul, Sub};
use std::time::Instant;
use ark_ec::PairingEngine;
use ark_ff::{Field, One, PrimeField, Zero};
use ark_poly::univariate::DensePolynomial;
use ark_poly::{EvaluationDomain, GeneralEvaluationDomain, Polynomial, UVPolynomial};
use ark_poly_commit::Evaluations;
//use rayon::prelude::{IntoParallelIterator, IntoParallelRefIterator}
use rayon::iter::{IntoParallelRefIterator, ParallelIterator};
use rayon::iter::IntoParallelIterator;
use crate::plonk::{compute_witness_polynomials, compute_z_polynomial, PlonkCircuitKeys, PlonkCircuitPolynomials, PlonkProof, PlonkSetup};
use crate::{CaulkTranscript, KZGCommit, PublicParameters};
use crate::afgo::{AFGSetup, PackedPolynomial};
use crate::ramlookup::{compute_aggregate_poly, compute_scaled_polynomial, compute_shifted_difference, compute_sum_poly};

// The multivariate form corresponding to plonk polynomial protocol aggregation
pub fn compute_g_plonk<E: PairingEngine>(
    q_M: &DensePolynomial<E::Fr>,
    q_L: &DensePolynomial<E::Fr>,
    q_R: &DensePolynomial<E::Fr>,
    q_O: &DensePolynomial<E::Fr>,
    q_C: &DensePolynomial<E::Fr>,
    S_a: &DensePolynomial<E::Fr>,
    S_b: &DensePolynomial<E::Fr>,
    S_c: &DensePolynomial<E::Fr>,
    l0_poly: &DensePolynomial<E::Fr>,
    w_A: &DensePolynomial<E::Fr>,
    w_B: &DensePolynomial<E::Fr>,
    w_C: &DensePolynomial<E::Fr>,
    z_poly: &DensePolynomial<E::Fr>,
    zw_poly: &DensePolynomial<E::Fr>,
    alpha: E::Fr,
    beta: E::Fr,
    gamma: E::Fr,
    plonk_setup: &PlonkSetup<E::Fr>,
    pp: &PublicParameters<E>,
    with_com: bool,
) -> (DensePolynomial<E::Fr>, E::G1Affine)
{
    //let zw_poly = &compute_shifted_difference::<E>(&z_poly, plonk_setup.h_domain_size) + z_poly;
    let gamma_poly = DensePolynomial::from_coefficients_vec(vec![gamma]);
    let w_AB = w_A * w_B;
    let p_1 = w_A + &DensePolynomial::from_coefficients_vec(vec![gamma, beta]);
    let p_2 = w_B + &DensePolynomial::from_coefficients_vec(vec![gamma,beta*plonk_setup.k1]);
    let p_3 = w_C + &DensePolynomial::from_coefficients_vec(vec![gamma,beta*plonk_setup.k2]);
    let q_1 = w_A + &(&compute_scaled_polynomial::<E>(&S_a, beta) + &gamma_poly);
    let q_2 = w_B + &(&compute_scaled_polynomial::<E>(&S_b, beta) + &gamma_poly);
    let q_3 = w_C + &(&compute_scaled_polynomial::<E>(&S_c, beta) + &gamma_poly);
    let mut poly = DensePolynomial::<E::Fr>::zero();
    poly = &poly + &(q_M * &w_AB);
    poly = &poly + &(q_L * w_A);
    poly = &poly + &(q_R * w_B);
    poly = &poly + &(q_O * w_C);
    poly = &poly + q_C;
   // (poly, _) = poly.divide_by_vanishing_poly(plonk_setup.domain).unwrap();

    let P = &(&p_1 * &p_2) * &(&p_3 * z_poly);
    let Q = &(&q_1 * &q_2) * &(&q_3 * zw_poly);

    //let (PQ_reduced, _) = (&P - &Q).divide_by_vanishing_poly(plonk_setup.domain).unwrap();
    poly = &poly + &compute_scaled_polynomial::<E>(&(&P - &Q), alpha);

    let R = l0_poly * &(z_poly - &DensePolynomial::from_coefficients_vec(vec![E::Fr::one()]));
    poly = &poly + &compute_scaled_polynomial::<E>(&R, alpha*alpha);
    (poly, _) = poly.divide_by_vanishing_poly(plonk_setup.domain).unwrap();

    let pcom = if with_com {
        KZGCommit::commit_g1(&pp.poly_ck, &poly)
    } else {
        E::G1Affine::zero()
    };

    (poly, pcom)
}

// The multivariate form corresponding to plonk polynomial protocol aggregation
pub fn compute_g_plonk_optimized<E: PairingEngine>(
    q_M: &Vec<E::Fr>,
    q_L: &Vec<E::Fr>,
    q_R: &Vec<E::Fr>,
    q_O: &Vec<E::Fr>,
    q_C: &Vec<E::Fr>,
    S_a: &Vec<E::Fr>,
    S_b: &Vec<E::Fr>,
    S_c: &Vec<E::Fr>,
    l0_poly: &Vec<E::Fr>,
    w_A: &DensePolynomial<E::Fr>,
    w_B: &DensePolynomial<E::Fr>,
    w_C: &DensePolynomial<E::Fr>,
    z_poly: &DensePolynomial<E::Fr>,
    zw_poly: &DensePolynomial<E::Fr>,
    alpha: E::Fr,
    beta: E::Fr,
    gamma: E::Fr,
    plonk_setup: &PlonkSetup<E::Fr>,
    pp: &PublicParameters<E>,
    with_com: bool,
) -> (DensePolynomial<E::Fr>, E::G1Affine)
{
    //let zw_poly = &compute_shifted_difference::<E>(&z_poly, plonk_setup.h_domain_size) + z_poly;
    let eval_domain: GeneralEvaluationDomain<E::Fr> = GeneralEvaluationDomain::new(plonk_setup.domain.size() * 4).unwrap();
    let w_A = w_A.evaluate_over_domain_by_ref(eval_domain).evals;
    let w_B = w_B.evaluate_over_domain_by_ref(eval_domain).evals;
    let w_C = w_C.evaluate_over_domain_by_ref(eval_domain).evals;
    let z_poly = z_poly.evaluate_over_domain_by_ref(eval_domain).evals;
    let zw_poly = zw_poly.evaluate_over_domain_by_ref(eval_domain).evals;
    let k1 = plonk_setup.k1;
    let k2 = plonk_setup.k2;

    let poly_evals = (0..eval_domain.size()).into_iter().map(|i| {
        (q_M[i]*w_A[i]*w_B[i] + q_L[i]*w_A[i] + q_R[i]*w_B[i] + q_O[i]*w_C[i] + q_C[i])
        +((w_A[i] + beta*eval_domain.element(i) + gamma)*(w_B[i] + beta*k1*eval_domain.element(i) + gamma)*(w_C[i] + beta*k2*eval_domain.element(i))*z_poly[i])*alpha
        -((w_A[i] + beta*S_a[i] + gamma)*(w_B[i] + beta*S_b[i] + gamma)*(w_C[i] + beta*S_c[i]+gamma)*zw_poly[i])*alpha
        +l0_poly[i]*(z_poly[i] - E::Fr::one())*alpha*alpha
    }).collect::<Vec<_>>();

    let mut poly = DensePolynomial::<E::Fr>::from_coefficients_vec(eval_domain.ifft(&poly_evals));
    (poly, _) = poly.divide_by_vanishing_poly(plonk_setup.domain).unwrap();

    let pcom = if with_com {
        KZGCommit::commit_g1(&pp.poly_ck, &poly)
    } else {
        E::G1Affine::zero()
    };

    (poly, pcom)
}





pub fn compute_g_plonk_y<E: PairingEngine>(
    q_M: &DensePolynomial<E::Fr>,
    q_L: &DensePolynomial<E::Fr>,
    q_R: &DensePolynomial<E::Fr>,
    q_O: &DensePolynomial<E::Fr>,
    q_C: &DensePolynomial<E::Fr>,
    S_a: &DensePolynomial<E::Fr>,
    S_b: &DensePolynomial<E::Fr>,
    S_c: &DensePolynomial<E::Fr>,
    l0_poly: &DensePolynomial<E::Fr>,
    w_A: &DensePolynomial<E::Fr>,
    w_B: &DensePolynomial<E::Fr>,
    w_C: &DensePolynomial<E::Fr>,
    z_poly: &DensePolynomial<E::Fr>,
    zw_poly: &DensePolynomial<E::Fr>,
    alpha: E::Fr,
    beta: E::Fr,
    gamma: E::Fr,
    y: E::Fr,
    plonk_setup: &PlonkSetup<E::Fr>,
    pp: &PublicParameters<E>,
    with_com: bool,
) -> (DensePolynomial<E::Fr>, E::G1Affine)
{
    //let zw_poly = &compute_shifted_difference::<E>(&z_poly, plonk_setup.h_domain_size) + z_poly;
    let gamma_poly = DensePolynomial::from_coefficients_vec(vec![gamma]);
    let w_AB = w_A * w_B;
    let p_1 = w_A + &DensePolynomial::from_coefficients_vec(vec![gamma + y*beta]);
    let p_2 = w_B + &DensePolynomial::from_coefficients_vec(vec![gamma + y*beta*plonk_setup.k1]);
    let p_3 = w_C + &DensePolynomial::from_coefficients_vec(vec![gamma + y*beta*plonk_setup.k2]);
    let q_1 = w_A + &(&compute_scaled_polynomial::<E>(&S_a, beta) + &gamma_poly);
    let q_2 = w_B + &(&compute_scaled_polynomial::<E>(&S_b, beta) + &gamma_poly);
    let q_3 = w_C + &(&compute_scaled_polynomial::<E>(&S_c, beta) + &gamma_poly);
    let mut poly = DensePolynomial::<E::Fr>::zero();
    poly = &poly + &(q_M * &w_AB);
    poly = &poly + &(q_L * w_A);
    poly = &poly + &(q_R * w_B);
    poly = &poly + &(q_O * w_C);
    poly = &poly + q_C;

    let P = &(&p_1 * &p_2) * &(&p_3 * z_poly);
    let Q = &(&q_1 * &q_2) * &(&q_3 * zw_poly);

    poly = &poly + &compute_scaled_polynomial::<E>(&(&P - &Q), alpha);

    let R = l0_poly * &(z_poly - &DensePolynomial::from_coefficients_vec(vec![E::Fr::one()]));
    poly = &poly + &compute_scaled_polynomial::<E>(&R, alpha*alpha);
    let pcom = if with_com {
        KZGCommit::commit_g1(&pp.poly_ck, &poly)
    } else {
        E::G1Affine::zero()
    };

    (poly, pcom)
}




pub fn compute_aplonk_proof<E: PairingEngine>(
    k_domain_size: usize,
    instance: &PlonkCircuitKeys<E>,
    circuit: &PlonkCircuitPolynomials<E::Fr>,
    witness: &Vec<Vec<E::Fr>>,
    plonk_setup: &PlonkSetup<E::Fr>,
    pp: &PublicParameters<E>,
    afg_pp: &AFGSetup<E>,
) {

    let n = 1usize << plonk_setup.h_domain_size;
    let K = 1usize << k_domain_size;
    let k_domain: GeneralEvaluationDomain<E::Fr> = GeneralEvaluationDomain::new(K).unwrap();

    println!("Computing circuit specific evaluations");
    let eval_domain = GeneralEvaluationDomain::<E::Fr>::new(plonk_setup.domain.size()*4).unwrap();
    let q_M = circuit.q_M.evaluate_over_domain_by_ref(eval_domain);
    let q_L = circuit.q_L.evaluate_over_domain_by_ref(eval_domain);
    let q_R = circuit.q_R.evaluate_over_domain_by_ref(eval_domain);
    let q_O = circuit.q_O.evaluate_over_domain_by_ref(eval_domain);
    let q_C = circuit.q_C.evaluate_over_domain_by_ref(eval_domain);
    let S_a = circuit.S_a.evaluate_over_domain_by_ref(eval_domain);
    let S_b = circuit.S_b.evaluate_over_domain_by_ref(eval_domain);
    let S_c = circuit.S_c.evaluate_over_domain_by_ref(eval_domain);
    let l0_poly = plonk_setup.l0_poly.evaluate_over_domain_by_ref(eval_domain);
    println!("Finished circuit specific evaluations");


    let mut transcript = CaulkTranscript::<E::Fr>::new();
    //let mut start = Instant::now();
    //let mut begin = Instant::now();
    // add the initial commitments to the transcript
    transcript.append_element(b"qm_com", &instance.qm_com);
    transcript.append_element(b"ql_com", &instance.ql_com);
    transcript.append_element(b"qr_com", &instance.qr_com);
    transcript.append_element(b"qo_com", &instance.qo_com);
    transcript.append_element(b"qc_com", &instance.qc_com);
    transcript.append_element(b"sa_com", &instance.Sa_com);
    transcript.append_element(b"sb_com", &instance.Sb_com);
    transcript.append_element(b"sc_com", &instance.Sc_com);

    // compute witness polynomials
    println!("Starting to compute witness polynomials");
    let mut start = Instant::now();
    let all_w_polys = witness.into_par_iter().map(|w| {
        compute_witness_polynomials(w, plonk_setup, pp)
    }).collect::<Vec<_>>();
    println!("Computed witness in {} secs", start.elapsed().as_secs());
    start = Instant::now();
    //let (wa_poly, wb_poly, wc_poly, wa_com, wb_com, wc_com) =
    //    compute_witness_polynomials(
    //        witness,
    //        plonk_setup,
    //        pp
    //    );

    //let (wa_polys, wb_polys, wc_polys, wa_coms, wb_coms, wc_coms): (Vec<_>, Vec<_>, Vec<_>, Vec<_>, Vec<_>, Vec<_>) =
    //    all_w_polys.into_iter().unzip();

    let wa_polys = all_w_polys.iter().map(|p| p.0.clone()).collect::<Vec<_>>();
    let wb_polys = all_w_polys.iter().map(|p| p.1.clone()).collect::<Vec<_>>();
    let wc_polys = all_w_polys.iter().map(|p| p.2.clone()).collect::<Vec<_>>();
    let wa_coms = all_w_polys.iter().map(|p| p.3).collect::<Vec<_>>();
    let wb_coms = all_w_polys.iter().map(|p| p.4).collect::<Vec<_>>();
    let wc_coms = all_w_polys.iter().map(|p| p.5).collect::<Vec<_>>();

    // Commit to packed polynomials
    let w_packed = [(&wa_polys, wa_coms), (&wb_polys, wb_coms), (&wc_polys, wc_coms)].into_par_iter().map(|x|
        PackedPolynomial::new_with_comms(k_domain_size, x.0, &x.1, afg_pp, pp)).collect::<Vec<_>>();

    //let w_A = PackedPolynomial::new_with_comms(k_domain_size, &wa_polys, &wa_coms, afg_pp, pp);
    //let w_B = PackedPolynomial::new_with_comms(k_domain_size, &wb_polys, &wb_coms, afg_pp, pp);
    //let w_C = PackedPolynomial::new_with_comms(k_domain_size, &wc_polys, &wc_coms, afg_pp, pp);

    println!("Committed witness in {} secs", start.elapsed().as_secs());

    transcript.append_element(b"a_com", &w_packed[0].com);
    transcript.append_element(b"b_com", &w_packed[1].com);
    transcript.append_element(b"c_com", &w_packed[2].com);

    // get challenges beta, gamma for computing z polynomial
    let beta = transcript.get_and_append_challenge(b"beta");
    let gamma = transcript.get_and_append_challenge(b"gamma");

    println!("Computing z polynomials");
    start = Instant::now();

    let all_z_polys = witness.into_par_iter().map(|w| {
        compute_z_polynomial(w, beta, gamma, circuit, plonk_setup, pp)
    }).collect::<Vec<_>>();

    let (z_polys, z_coms): (Vec<_>, Vec<_>) = all_z_polys.into_iter().unzip();

    let zw_polys = z_polys.par_iter().map(|p|
                &compute_shifted_difference::<E>(p, plonk_setup.h_domain_size) + p).collect::<Vec<_>>();

    let z_poly = PackedPolynomial::new_with_comms(k_domain_size, &z_polys, &z_coms, afg_pp, pp);
    println!("Computed z polynomial in {} secs", start.elapsed().as_secs());

    // append commitment to z polynomial to transcript
    transcript.append_element(b"z_com", &z_poly.com);
    let alpha = transcript.get_and_append_challenge(b"alpha");

    println!("Computing H polynomial");
    start = Instant::now();
    // Compute H(X,Y) with component polynomials as G(A_i,B_i,...)
    let (h_polys, h_coms) = (0..K).into_par_iter().map(|i| {
        compute_g_plonk_optimized::<E>(
            &q_M.evals,
            &q_L.evals,
            &q_R.evals,
            &q_O.evals,
            &q_C.evals,
            &S_a.evals,
            &S_b.evals,
            &S_c.evals,
            &l0_poly.evals,
            &wa_polys[i],
            &wb_polys[i],
            &wc_polys[i],
            &z_polys[i],
            &zw_polys[i],
            alpha,
            beta,
            gamma,
            plonk_setup,
            pp,
            true
        )
    }).collect::<Vec<(_,_)>>().into_iter().unzip();

    let packed_H = PackedPolynomial::new_with_comms(k_domain_size, &h_polys, &h_coms, afg_pp, pp);
    println!("Computed H polynomial in {} secs", start.elapsed().as_secs());

    // Sanity check (H(X,Y) = 0 over H\times V).
    //assert_eq!(h_polys[1].evaluate(&plonk_setup.domain.element(1)), E::Fr::zero(), "H does not vanish over H x V");

    start = Instant::now();
    // Compute polynomials Q(X,y) and H(X,y) for random y
    let y = transcript.get_and_append_challenge(b"ch_y");

    // evaluate q_M, q_L, q_R, q_O, q_C, S_a, S_b, S_c at y
    let univariate_evals_y =
        [&circuit.q_M, &circuit.q_L, &circuit.q_R, &circuit.q_O, &circuit.q_C, &circuit.S_a, &circuit.S_b, &circuit.S_c, &plonk_setup.l0_poly].into_par_iter()
            .map(|p| p.evaluate(&y)).collect::<Vec<_>>();
    let bivariate_evals_y =
        [&w_packed[0], &w_packed[1], &w_packed[2], &z_poly].into_par_iter()
            .map(|p| p.partial_eval_y(y)).collect::<Vec<_>>();

    let zw_poly_evals_y = z_poly.partial_eval_y(plonk_setup.domain.element(1)*y);
    // compute polynomial G(P_0(X,y),...P_l(X,y))
    let g_poly_y = compute_g_plonk_y(
        &DensePolynomial::from_coefficients_slice(&[univariate_evals_y[0]]),
        &DensePolynomial::from_coefficients_slice(&[univariate_evals_y[1]]),
        &DensePolynomial::from_coefficients_slice(&[univariate_evals_y[2]]),
        &DensePolynomial::from_coefficients_slice(&[univariate_evals_y[3]]),
        &DensePolynomial::from_coefficients_slice(&[univariate_evals_y[4]]),
        &DensePolynomial::from_coefficients_slice(&[univariate_evals_y[5]]),
        &DensePolynomial::from_coefficients_slice(&[univariate_evals_y[6]]),
        &DensePolynomial::from_coefficients_slice(&[univariate_evals_y[7]]),
        &DensePolynomial::from_coefficients_slice(&[univariate_evals_y[8]]),
        &bivariate_evals_y[0],
        &bivariate_evals_y[1],
        &bivariate_evals_y[2],
        &bivariate_evals_y[3],
        &zw_poly_evals_y,
        alpha,
        beta,
        gamma,
        y,
        plonk_setup,
        pp,
        false
    );

    let h_poly_y = packed_H.partial_eval_y(y);
    //let (q_poly_y, rem_poly) = (&g_poly_y.0 - &h_poly_y).divide_by_vanishing_poly(k_domain).unwrap();
    //assert_eq!(rem_poly, DensePolynomial::zero(), "Q(X,y) != H(X,y) mod Z_H(X)");
    //println!("Computing Q(X,y) - H(X,y) / Z_H(X) took {} secs", start.elapsed().as_secs());
}
