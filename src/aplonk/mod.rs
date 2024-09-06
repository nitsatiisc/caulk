// This file contains implementation of PLONK proof aggregation

use std::ops::{Add, Sub};
use std::time::Instant;
use ark_ec::PairingEngine;
use ark_ff::{Field, One, PrimeField, Zero};
use ark_poly::univariate::DensePolynomial;
use ark_poly::{EvaluationDomain, GeneralEvaluationDomain, Polynomial, UVPolynomial};
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

    let P = &(&p_1 * &p_2) * &(&p_3 * z_poly);
    let Q = &(&q_1 * &q_2) * &(&q_3 * zw_poly);

    poly = &poly + &compute_scaled_polynomial::<E>(&(&P - &Q), alpha);

    let R = &plonk_setup.l0_poly * &(z_poly - &DensePolynomial::from_coefficients_vec(vec![E::Fr::one()]));
    poly = &poly + &compute_scaled_polynomial::<E>(&R, alpha*alpha);
    let pcom = KZGCommit::commit_g1(&pp.poly_ck, &poly);
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
    let beta = E::Fr::one(); //transcript.get_and_append_challenge(b"beta");
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
        compute_g_plonk::<E>(
            &circuit.q_M,
            &circuit.q_L,
            &circuit.q_R,
            &circuit.q_O,
            &circuit.q_C,
            &circuit.S_a,
            &circuit.S_b,
            &circuit.S_c,
            &wa_polys[i],
            &wb_polys[i],
            &wc_polys[i],
            &z_polys[i],
            &zw_polys[i],
            alpha,
            beta,
            gamma,
            plonk_setup,
            pp
        )
    }).collect::<Vec<(_,_)>>().into_iter().unzip();

    let packed_H = PackedPolynomial::new_with_comms(k_domain_size, &h_polys, &h_coms, afg_pp, pp);
    println!("Computed H polynomial in {} secs", start.elapsed().as_secs());

    // Sanity check (H(X,Y) = 0 over H\times V).
    assert_eq!(h_polys[1].evaluate(&plonk_setup.domain.element(1)), E::Fr::zero(), "H does not vanish over H x V");
}
