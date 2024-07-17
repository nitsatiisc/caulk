use std::collections::{HashMap, HashSet};
use std::convert::TryInto;
use std::fs::File;
use std::io::{Read, Write};
use std::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg};
use std::time::Instant;
use ark_ec::{AffineCurve, PairingEngine, ProjectiveCurve};
use ark_ec::msm::VariableBaseMSM;
use ark_ff::{Field, One, PrimeField, Zero};
use ark_poly::{EvaluationDomain, GeneralEvaluationDomain, Polynomial, UVPolynomial};
use ark_poly::univariate::DensePolynomial;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::{cfg_into_iter, UniformRand};
use colored;
use elements_frequency::interface::frequency_finder;
use crate::multi::TableInput;
use crate::{CaulkTranscript, field_dft, group_dft, InvertPolyCache, KZGCommit, PublicParameters};
use crate::ramlookup::caulkplus::{CaulkPlusProverInput, CaulkPlusPublicParams};
use crate::ramlookup::fastupdate::{compute_scalar_coefficients, compute_scalar_coefficients_naive};

/**
 * This file implements the non-ZK CQ lookup argument from the paper:
 * "CQ: cached quotients for fast lookups" (https://eprint.iacr.org/2022/1763.pdf)
 * In addition, we also present adaptation of CQ for updatable tables as described in
 * in the paper "Batching Efficient RAM using Updatable Lookup Arguments" (https://eprint.iacr.org/2024/840.pdf)
 * We re-use several components such as table-specific pre-processed material
 * from Caulk implementation available at https://github.com/caulk-crypto/caulk
 */


/**
Public Parameters for CQ lookup argument
 * z_h_com: commitment to the vanishing polynomial of H, the subgroup of N roots of unity used to interpolate the table.
 * log_poly_com: commitment to the polynomial mapping \omega^i -> i over H
 * log_poly: the polynomial L such that L(\omega^i)=i for i\in [N]
 * openings_z_h_poly: quotients (Z_H(x)/(x-\omega^i)).g1
 * openings_log_poly: quotients ((L(x)-L(\omega^i))/(X-\omega^i)).g1
 * openings_mu_poly: quotients ((\mu_i(X)-1)/(X-\omega^i)).g1 where \mu_i(X) is the i^th lagrange polynomial for set H
 */
#[allow(non_snake_case)]
pub struct CqPublicParams<E: PairingEngine> {
    pub z_h_com: E::G2Affine,                       // commitment to vanishing poly
    pub log_poly_com: E::G2Affine,                  // commitment to log polynomial
    pub log_poly: DensePolynomial<E::Fr>,           // log polynomial on h_domain
    pub openings_z_h_poly: Vec<E::G1Affine>,        // opening proofs for polynomial X^N - 1
    pub openings_log_poly: Vec<E::G1Affine>,        // opening proofs for log polynomial
    pub openings_mu_polys: Vec<E::G1Affine>,        // these are proofs for i^th lagrange poly at xi^i.
}

/**
 * Pre-computed table parameters for CQ lookup argument
 * t_com: KZG commitment to the table polynomial in G2
 * t_poly: the table polynomial
 * openings_t_poly: encoded quotients ((T(X)-T(\omega^i))/(X-\omega^i)).g1
 */
pub struct CqProverInput<E: PairingEngine> {
    pub t_com: E::G2Affine,                             // commitment to table
    pub t_poly: DensePolynomial<E::Fr>,                 // polynomial interpolating the table on h_domain
    pub openings_t_poly: Vec<E::G1Affine>,              // opening proofs of the t-polynomial
}

impl<E: PairingEngine> CqProverInput<E> {
    // serialize the Cq prover inputs in a file
    pub fn store(&self, h_domain_size: usize) {
        let path = format!(
            "polys_cq/poly_{}_openings_{}_{}.setup",
            "tbl",
            1usize << h_domain_size,
            E::Fq::size_in_bits()
        );


        let table: TableInputCq<E> = TableInputCq {
            c_poly: self.t_poly.clone(),
            c_com: self.t_com.clone(),
            openings: self.openings_t_poly.clone()
        };
        table.store(&path);

    }

    // load Cq prover input from a file
    pub fn load(h_domain_size: usize) -> CqProverInput<E> {
        let path = format!(
            "polys_cq/poly_{}_openings_{}_{}.setup",
            "tbl",
            1usize << h_domain_size,
            E::Fq::size_in_bits()
        );

        println!("path: {}", path);
        let table = TableInputCq::<E>::load(&path);

        CqProverInput {
            t_com: table.c_com,
            t_poly: table.c_poly,
            openings_t_poly: table.openings
        }
    }
}


/**
 * Sub-vector lookup instance parameterized by commitments of two vectors and their respective sizes
 */
pub struct CqLookupInstance<E: PairingEngine> {
    pub t_com: E::G2Affine,                         // commitment of the table
    pub f_com: E::G1Affine,                         // commitment of the a-vector (addresses)
    pub m_domain_size: usize,                       // domain size of a vector
    pub h_domain_size: usize,                       // domain size of table
}

/**
 * CQ proof: refer to the CQ paper for components of the proof
 */
pub struct CqProof<E: PairingEngine> {
    pub phi_com: E::G1Affine,                           // commitment to phi
    pub a_com: E::G1Affine,                             // commitment to A polynomial
    pub qa_com: E::G1Affine,                            // commitment to qA polynomial
    pub b0_com: E::G1Affine,                            // commitment to B0 polynomial
    pub qb_com: E::G1Affine,                            // commitment to Q_B polynomial
    pub p_com: E::G1Affine,                             // commitment to p polynomial
    pub b0_gamma: E::Fr,                                // evaluation of B0 at gamma
    pub f_gamma: E::Fr,                                 // evaluation of f at gamma
    pub a0: E::Fr,                                      // A(0)
    pub h_gamma: E::Fr,                                 // evaluation of h at gamma
    pub a0_com:E::G1Affine,                             // commitment to polynomial A0
    pub pi_h: E::G1Affine,                              // evaluation proof for h(\gamma).
}

/**
 * Input to the algorithm for computing CQ proof from "approximate setup"
 * The vectors c_i_vec and t_j_vec contain coefficients c_i and \delta_t_j
 * in the computational procedure described in Section 7, "Fast Lookups from Approximate Pre-processing"
 * in the paperhttps://eprint.iacr.org/2024/840.pdf
 */
pub struct CqDeltaInput<E: PairingEngine> {
    pub set_k: Vec<usize>,                              // set K in the update protocol
    pub set_i: Vec<usize>,                              // set I in the protocol. We assume I appears in K at the start.
    pub c_i_vec: Vec<E::Fr>,                            // coefficients c_i
    pub t_j_vec: Vec<E::Fr>,                            // t_j for each j in K
}

/**
 * A CQ example structure for testing/benchmarking
 */
pub struct CqExample<F: PrimeField> {
    pub table: Vec<usize>,                          // table t
    pub f_vec: Vec<usize>,                          // a sub-vector of t
    pub f_poly: DensePolynomial<F>,                 // f as a polynomial
    pub m_vec: HashMap<usize, F>,                   // multiplicities vector
    pub i_set: Vec<usize>,                          // set I
    pub k_set: Vec<usize>,                          // set K
    pub t_j_vec: Vec<F>,                            // delta t_j vector
    pub t_poly: DensePolynomial<F>,                 // table polynomial
}

impl<F: PrimeField> CqExample<F> {
    // Generate a new example for updatable CQ lookup argument
    // table denotes the base table for which pre-processed parameters are available.
    // m_domain_size denotes the size of the batch for each update. This denotes the size of set I in Section 7, https://eprint.iacr.org/2024/840.pdf
    // k_domain_size denotes the size of changes between current table and base table. This denotes size of set K in Section 7, https://eprint.iacr.org/2024/840.pdf
    pub fn new(table: &Vec<usize>, m_domain_size: usize, k_domain_size: usize) -> CqExample<F> {
        let mut rng = ark_std::test_rng();
        let m = 1usize << m_domain_size;
        let k: usize = 1usize << k_domain_size;

        // Generate a table slightly different from the input table to test
        // CQ proof generation from slightly updated table
        let mut upd_table = table.clone();

        // Remember, we assume K contains I (the set of indices corresponding to sub-vector)
        // and the positions where the updated table differs from the base (pre-processed) table.
        // We first generate k-m positions meant to be outside "I", and change the table by 1 at those positions
        // We may not sample k-m distinct positions here but we will adjust it later by adjusting the set K to consist
        // of exactly 1 << k_domain_size positions, some with possibly delta = 0.
        let mut upd_pos: HashSet<usize> = HashSet::new();
        for i in 0..(k-m) {
            let pos = usize::rand(&mut rng) % upd_table.len();
            upd_pos.insert(pos);
            upd_table[pos] += 1;
        }

        // Now we randomly sample a sub-vector of size m of the updated table
        let mut m_vec: HashMap<usize, F> = HashMap::new();
        let mut f_vec: Vec<usize> = Vec::new();
        for i in 0..m {
            f_vec.push(upd_table[ usize::rand(&mut rng) % upd_table.len()]);
        }

        // Calculate multiplicities vector: The CQ lookup argument requires the prover to commit to multiplicity vector m=(m_0,...,m_{N-1})
        // However, the vector is sparse with at most m non-zero entries. The multiplicity vector is chosen to satisfy the equality of rational functions
        // in the log-up protocol. In the routine below, for all f\in f_vec, we calculate frequency x_f of f in f_vec. Then for first occurrence of f in table,
        // we set m_f = x_f, and for subsequent occurrences of f in the table, we simply set m_f = 0.

        let m_f = frequency_finder(&f_vec);
        let mut m_set: HashSet<usize> = HashSet::new();                                             // set of positions where m_i\neq 0
        let mut m_seen: HashSet<usize> = HashSet::new();                                            // set of elements already assigned multiplicities. Repetitions are assigned multiplicity 0.
        for i in 0..upd_table.len() {
            if m_f.contains_key(&upd_table[i]) && !m_seen.contains(&upd_table[i]) {
                let x_f = *m_f.get(&upd_table[i]).unwrap();
                m_vec.insert(i, F::from(x_f as u128));
                m_set.insert(i);
                m_seen.insert(upd_table[i]);
            }
        }

        // extend the m_set to length m, add new positions i with m_i = 0
        // We can do this, as all elements of f_vec have already been accounted for by
        // existing multiplicities.
        while m_vec.len() < m {
            let pos = usize::rand(&mut rng) % upd_table.len();
            if !m_vec.contains_key(&pos) {
                m_vec.insert(pos, F::zero());
                m_set.insert(pos);
            }
        }

        let mut i_set_vec: Vec<usize> = m_set.clone().into_iter().collect::<Vec<_>>();
        assert_eq!(i_set_vec.len(), m, "i_set size is not m");
        let mut k_set_vec = i_set_vec.clone();
        let mut k_set = m_set.clone();
        // insert the updated positions in k_set
        for pos in upd_pos.iter() {
            if !m_set.contains(pos) {
                k_set.insert(*pos);
                k_set_vec.push(*pos);
            }
        }

        // if the size of k_set is less than k_domain.size(), extend with dummy positions.
        // This does not affect correctness, as \delta_t_j will simply be 0 for the positions
        // which do not actually correspond to updated locations.
        while k_set.len() < k {
            let new_pos = usize::rand(&mut rng) % upd_table.len();
            if !k_set.contains(&new_pos) {
                k_set.insert(new_pos);
                k_set_vec.push(new_pos);
            }
        }
        assert_eq!(k_set_vec.len(), k, "k_set size is not k");

        // Compute delta_t_j vector. The difference between the updated and base tables.
        let mut t_j_vec: Vec<F> = Vec::new();
        for i in 0..k_set_vec.len() {
            t_j_vec.push(F::from((upd_table[k_set_vec[i]] - table[k_set_vec[i]]) as u128));
        }

        // Convert vectors from integers to field vectors.
        let f_vec_ff = f_vec.iter().map(|x| F::from(*x as u128)).collect::<Vec<_>>();
        let t_vec_ff = upd_table.iter().map(|x| F::from(*x as u128)).collect::<Vec<_>>();

        // Compute polynomials f(X) and t(X) interpolating the vectors f and t.
        let m_domain: GeneralEvaluationDomain<F> = GeneralEvaluationDomain::new(1 << m_domain_size).unwrap();
        let h_domain: GeneralEvaluationDomain<F> = GeneralEvaluationDomain::new(table.len()).unwrap();
        let f_poly = DensePolynomial::from_coefficients_vec(m_domain.ifft(&f_vec_ff));
        let t_poly = DensePolynomial::from_coefficients_vec(h_domain.ifft(&t_vec_ff));

        CqExample {
            t_poly: t_poly,
            table: upd_table,
            f_vec,
            f_poly,
            m_vec,
            i_set: i_set_vec,
            k_set: k_set_vec,
            t_j_vec,
        }

    }

    // This function generates an example for a fixed table, using a pre-specified sub-vector
    // f_vec of the table. As a hack, we have re-used the code of previous function, setting updates to 0.
    pub fn new_fixed_subvec(table: &Vec<usize>, f_vec: &Vec<usize>, m_domain_size: usize, k_domain_size: usize) -> CqExample<F> {
        let mut rng = ark_std::test_rng();
        let m = 1usize << m_domain_size;
        let k: usize = 1usize << k_domain_size;

        let mut upd_table = table.clone();
        let mut upd_pos: HashSet<usize> = HashSet::new();
        for i in 0..(k-m) {
            let pos = usize::rand(&mut rng) % upd_table.len();
            upd_pos.insert(pos);
            upd_table[pos] += 0;
        }

        let mut m_vec: HashMap<usize, F> = HashMap::new();

        let m_f = frequency_finder(&f_vec);
        let mut m_set: HashSet<usize> = HashSet::new();
        let mut m_seen: HashSet<usize> = HashSet::new();
        for i in 0..upd_table.len() {
            if m_f.contains_key(&upd_table[i]) && !m_seen.contains(&upd_table[i]) {
                let x_f = *m_f.get(&upd_table[i]).unwrap();
                m_vec.insert(i, F::from(x_f as u128));
                m_set.insert(i);
                m_seen.insert(upd_table[i]);
            }
        }

        // extend the m_set to length m, add with m_i = 0
        while m_vec.len() < m {
            let pos = usize::rand(&mut rng) % upd_table.len();
            if !m_vec.contains_key(&pos) {
                m_vec.insert(pos, F::zero());
                m_set.insert(pos);
            }
        }

        let mut i_set_vec: Vec<usize> = m_set.clone().into_iter().collect::<Vec<_>>();
        assert_eq!(i_set_vec.len(), m, "i_set size not m");
        let mut k_set_vec = i_set_vec.clone();
        let mut k_set = m_set.clone();
        // insert the updated positions in k_set
        for pos in upd_pos.iter() {
            if !m_set.contains(pos) {
                k_set.insert(*pos);
                k_set_vec.push(*pos);
            }
        }
        // if the size of k_set is less than k_domain.size(), extend with dummy
        while k_set.len() < k {
            let new_pos = usize::rand(&mut rng) % upd_table.len();
            if !k_set.contains(&new_pos) {
                k_set.insert(new_pos);
                k_set_vec.push(new_pos);
            }
        }

        assert_eq!(k_set_vec.len(), k, "k_set size not k");

        let mut t_j_vec: Vec<F> = Vec::new();
        for i in 0..k_set_vec.len() {
            t_j_vec.push(F::from((upd_table[k_set_vec[i]] - table[k_set_vec[i]]) as u128));
        }


        let f_vec_ff = f_vec.iter().map(|x| F::from(*x as u128)).collect::<Vec<_>>();
        let t_vec_ff = upd_table.iter().map(|x| F::from(*x as u128)).collect::<Vec<_>>();

        let m_domain: GeneralEvaluationDomain<F> = GeneralEvaluationDomain::new(1 << m_domain_size).unwrap();
        let h_domain: GeneralEvaluationDomain<F> = GeneralEvaluationDomain::new(table.len()).unwrap();
        let f_poly = DensePolynomial::from_coefficients_vec(m_domain.ifft(&f_vec_ff));
        let t_poly = DensePolynomial::from_coefficients_vec(h_domain.ifft(&t_vec_ff));

        CqExample {
            t_poly: t_poly,
            table: upd_table,
            f_vec: f_vec.clone(),
            f_poly,
            m_vec,
            i_set: i_set_vec,
            k_set: k_set_vec,
            t_j_vec,
        }

    }

    pub fn new_base_cache_example(
        base_table: &Vec<usize>,
        current_table: &Vec<usize>,
        f_vec: &Vec<usize>,
        h_domain_size: usize,
        m_domain_size: usize,
    ) -> CqExample<F> {
        assert_eq!(base_table.len(), 1usize << h_domain_size, "base_table size mismatch");
        assert_eq!(current_table.len(), 1usize << h_domain_size, "current_table size mismatch");
        assert_eq!(f_vec.len(), 1usize << m_domain_size, "sub-vector size mismatch");

        let mut rng = ark_std::test_rng();
        let m:usize  = 1usize << m_domain_size;

        // ensure f_vec is sub-vector of current_table
        let mut c_set: HashSet<usize> = HashSet::new();
        for i in 0..current_table.len() {
            c_set.insert(current_table[i]);
        }

        for i in 0..f_vec.len() {
            assert_eq!(c_set.contains(&f_vec[i]), true, "incorrect sub-vector");
        }

        // compute the multiplicities vector
        let mut m_vec: HashMap<usize, F> = HashMap::new();
        let m_f = frequency_finder(&f_vec);
        let mut m_set: HashSet<usize> = HashSet::new();
        let mut m_seen: HashSet<usize> = HashSet::new();
        for i in 0..current_table.len() {
            if m_f.contains_key(&current_table[i]) && !m_seen.contains(&current_table[i]) {
                let x_f = *m_f.get(&current_table[i]).unwrap();
                m_vec.insert(i, F::from(x_f as u128));
                m_set.insert(i);
                m_seen.insert(current_table[i]);
            }
        }

        // extend the m_set to length m, add with m_i = 0
        while m_vec.len() < m {
            let pos = usize::rand(&mut rng) % current_table.len();
            if !m_vec.contains_key(&pos) {
                m_vec.insert(pos, F::zero());
                m_set.insert(pos);
            }
        }

        let mut i_set_vec: Vec<usize> = m_set.clone().into_iter().collect::<Vec<_>>();
        assert_eq!(i_set_vec.len(), m, "i_set size not m");
        let mut k_set_vec = i_set_vec.clone();
        let mut k_set = m_set.clone();

        // add positions to k_set where the current table differs from base table
        for i in 0..current_table.len() {
            if base_table[i] != current_table[i] && !k_set.contains(&i) {
                k_set.insert(i);
                k_set_vec.push(i);
            }
        }

        let k_set_size: usize = usize::next_power_of_two(k_set_vec.len());
        let k_domain_size: usize = usize::ilog2(k_set_size) as usize;
        assert_eq!(k_set_size, 1usize << k_domain_size, "k_set_size != 1 << k_domain_size");

        // append the k_set and k_vec to make size a power of two
        while k_set_vec.len() < k_set_size {
            let pos: usize = usize::rand(&mut rng) % current_table.len();
            if !k_set.contains(&pos) {
                k_set.insert(pos);
                k_set_vec.push(pos);
            }
        }

        let mut t_j_vec: Vec<F> = Vec::new();
        for i in 0..k_set_vec.len() {
            t_j_vec.push(F::from((current_table[k_set_vec[i]] - base_table[k_set_vec[i]]) as u128));
        }


        let f_vec_ff = f_vec.iter().map(|x| F::from(*x as u128)).collect::<Vec<_>>();
        let t_vec_ff = current_table.iter().map(|x| F::from(*x as u128)).collect::<Vec<_>>();

        let m_domain: GeneralEvaluationDomain<F> = GeneralEvaluationDomain::new(1 << m_domain_size).unwrap();
        let h_domain: GeneralEvaluationDomain<F> = GeneralEvaluationDomain::new(current_table.len()).unwrap();
        let f_poly = DensePolynomial::from_coefficients_vec(m_domain.ifft(&f_vec_ff));
        let t_poly = DensePolynomial::from_coefficients_vec(h_domain.ifft(&t_vec_ff));



        CqExample::<F> {
            table: current_table.to_vec(),
            f_vec: f_vec.to_vec(),
            f_poly: f_poly,
            m_vec: m_vec,
            i_set: i_set_vec,
            k_set: k_set_vec,
            t_j_vec: t_j_vec,
            t_poly: t_poly,
        }

    }
}

/**
 * CQ proof generation algorithm with support for approximate setup.
 * Setting the parameter update=false is equivalent to the CQ argument
 * presented in the paper "CQ: Cached quotients for fast lookups" in Section 4
 * The variable names adhere to similar variable names as in the paper.
 * The function expects following parameters:
 * instance - denotes the lookup instance consisting of vector commitments
 * input - table specific inputs for the CQ prover.
 * example - sub-vector lookup example, with multiplicities etc.
 * cq_pp - openings of polynomials helpful for CQ proof generation.
 * pp - Generic public parameters (KZG srs, etc.).
 * update - boolean flag indicating if approximate setup (1) or exact setup (0) is being used to compute the proof
 */
#[allow(non_snake_case)]
pub fn compute_cq_proof<E: PairingEngine>(
    instance: &CqLookupInstance<E>,
    input: &CqProverInput<E>,
    example: &CqExample<E::Fr>,
    cq_pp: &CqPublicParams<E>,
    pp: &PublicParameters<E>,
    update: bool
) -> CqProof<E> {
    let N = 1usize << instance.h_domain_size;
    let m = 1usize << instance.m_domain_size;
    let Ninv = E::Fr::from(N as u128).inverse().unwrap();

    let mut transcript = CaulkTranscript::<E::Fr>::new();
    // add instance to the transcript
    transcript.append_element(b"t_com", &instance.t_com);
    transcript.append_element(b"f_com", &instance.f_com);

    let round1  = compute_prover_round1(example, instance.h_domain_size, cq_pp);
    // phi_com commits to multiplicity polynomial (polynomial m(X) in the CQ paper).
    transcript.append_element(b"phi_com", &round1.phi_com);
    let beta = transcript.get_and_append_challenge(b"ch_beta");

    // in round two, prover computes:
    // (i) the A polynomial that interpolates m_i/(\beta + t_i) at i^{th} N^th root of unity, and commitment to it.
    // (ii) Computes commitment to quotient polynomial Q_A satisfying A(X)(\beta + t(X)) - m(X) = Q_A(X).Z_H(X). Note the commitment is directly computed
    // from pre-computed quotients, without computing the polynomial itself.
    // (iii) Computes polynomial B(X) interpolating 1/(\beta + f_i) at i^{th} m^th root of unity.
    // (iv) Computes and commits to polynomial B_0(X) = (B(X) - B(0))/X
    // (v) Computes and commits to Q_B polynomial satisfying B(X)(\beta + f(X))-1 = Q_B(X).Z_V(X)
    // (vi) Computes and commits to polynomial P(X) = B_0(X).X^{N-1-(n-2)}. This polynomial is used to upper-bound the degree of B_0.
    let round2 = compute_prover_round2(beta, instance, input, example, cq_pp, pp);

    // Commitment to the polynomial Q_A(X) needs to be altered if we are using approximate setup.
    let mut qa_delta_com = E::G1Affine::zero();
    if update {
        let mut c_i_vec: Vec<E::Fr> = Vec::new();
        for i in 0..round2.sparse_A_vec.len() {
            c_i_vec.push(round2.sparse_A_vec[i].1.mul(Ninv));
        }

        let delta_input = CqDeltaInput::<E> {
            set_k: example.k_set.clone(),
            set_i: example.i_set.clone(),
            c_i_vec: c_i_vec,
            t_j_vec: example.t_j_vec.clone()
        };

        qa_delta_com = compute_encoded_quotient_delta(&delta_input, cq_pp, instance.h_domain_size);
    }

    let qa_com_upd = round2.qa_com.add(qa_delta_com);

    // add elements to transcript
    transcript.append_element(b"a_com", &round2.a_com);
    transcript.append_element(b"qa_com", &qa_com_upd);
    transcript.append_element(b"b0_com", &round2.b0_com);
    transcript.append_element(b"qb_com", &round2.qb_com);
    transcript.append_element(b"p_com", &round2.p_com);
    transcript.append_element(b"a0_com", &round2.a0_com);

    // sanity check
    assert_eq!(E::pairing(round2.b0_com, pp.g2_powers[(N-1)-(m-2)]), E::pairing(round2.p_com, pp.g2_powers[0]),
               "pairing check failed");
    assert_eq!(E::pairing(round2.a_com, instance.t_com),
               E::pairing(qa_com_upd, cq_pp.z_h_com).mul(
                   E::pairing(round1.phi_com.add(round2.a_com.mul(beta).into_affine().neg()), pp.g2_powers[0])), "pairing failed for a_com");

    let gamma = transcript.get_and_append_challenge(b"ch_gamma");

    // prover sends evaluations: A(0), f(\gamma), B_0(\gamma)
    let f_gamma = round2.f_poly.evaluate(&gamma);
    let b0_gamma = round2.b0_poly.evaluate(&gamma);

    // add the evaluations to the transcript
    transcript.append_element(b"a0", &round2.a0);
    transcript.append_element(b"f_gamma", &f_gamma);
    transcript.append_element(b"b0_gamma", &b0_gamma);

    // sanity check
    assert_eq!(E::pairing(round2.a_com.add(pp.poly_ck.powers_of_g[0].mul(round2.a0).into_affine().neg()), pp.g2_powers[0]),
               E::pairing(round2.a0_com, pp.g2_powers[1]), "Pairing check on a0 failed");

    let eta = transcript.get_and_append_challenge(b"ch_eta");
    let round3 = compute_prover_round3(gamma, eta, &round2, &pp);

    CqProof::<E> {
        phi_com: round1.phi_com,
        a_com: round2.a_com,
        qa_com: qa_com_upd,
        b0_com: round2.b0_com,
        qb_com: round2.qb_com,
        p_com: round2.p_com,
        b0_gamma: b0_gamma,
        f_gamma: f_gamma,
        a0: round2.a0,
        h_gamma: round3.h_gamma,
        a0_com: round2.a0_com,
        pi_h: round3.pi_h,
    }

}

pub fn verify_cq_proof<E: PairingEngine>(
    instance: &CqLookupInstance<E>,
    proof: &CqProof<E>,
    cq_pp: &CqPublicParams<E>,
    pp: &PublicParameters<E>,
) -> bool {
    let m_domain_size = instance.m_domain_size;
    let h_domain_size = instance.h_domain_size;
    let m = 1usize << m_domain_size;
    let N: usize = 1usize << h_domain_size;
    let m_domain: GeneralEvaluationDomain<E::Fr> = GeneralEvaluationDomain::new(m).unwrap();

    let mut transcript: CaulkTranscript<E::Fr> = CaulkTranscript::new();
    // add instance to the transcript
    transcript.append_element(b"t_com", &instance.t_com);
    transcript.append_element(b"f_com", &instance.f_com);
    // add commitment to phi polynomial (m(X) in CQ paper).
    transcript.append_element(b"phi_com", &proof.phi_com);
    let beta = transcript.get_and_append_challenge(b"ch_beta");
    // add round2 prover messages
    transcript.append_element(b"a_com", &proof.a_com);
    transcript.append_element(b"qa_com", &proof.qa_com);
    transcript.append_element(b"b0_com", &proof.b0_com);
    transcript.append_element(b"qb_com", &proof.qb_com);
    transcript.append_element(b"p_com", &proof.p_com);
    transcript.append_element(b"a0_com", &proof.a0_com);

    let gamma = transcript.get_and_append_challenge(b"ch_gamma");
    // add the evaluations to the transcript
    transcript.append_element(b"a0", &proof.a0);
    transcript.append_element(b"f_gamma", &proof.f_gamma);
    transcript.append_element(b"b0_gamma", &proof.b0_gamma);

    let eta = transcript.get_and_append_challenge(b"ch_eta");

    // verification checks
    let mut start = Instant::now();
    if E::pairing(proof.b0_com, pp.g2_powers[(N-1)-(m-2)]) != E::pairing(proof.p_com, pp.g2_powers[0]) {
        println!("Degree check on poly B0 failed");
        return false;
    }

    if E::pairing(proof.a_com, instance.t_com) != E::pairing(proof.qa_com, cq_pp.z_h_com).mul(
        E::pairing(proof.phi_com.add(proof.a_com.mul(beta).into_affine().neg()), pp.g2_powers[0])) {
        println!("The poly identity for Q_A(X) failed");
        return false;
    }

    if E::pairing(proof.a_com.add(pp.poly_ck.powers_of_g[0].mul(proof.a0).into_affine().neg()), pp.g2_powers[0]) !=
        E::pairing(proof.a0_com, pp.g2_powers[1]) {
        println!("The check A_0(X) = (A(X) - A(0))/X failed");
        return false;
    }

    let b0 = E::Fr::from(N as u128).mul(proof.a0).div(E::Fr::from(m as u128));
    let b_gamma: E::Fr = (proof.b0_gamma*gamma).add(b0);
    let qb_gamma:E::Fr = b_gamma.mul(proof.f_gamma + beta) - E::Fr::one();
    let zv_gamma = m_domain.evaluate_vanishing_polynomial(gamma);
    let qb_gamma = qb_gamma.mul(zv_gamma.inverse().unwrap());
    if proof.h_gamma != proof.b0_gamma + proof.f_gamma.mul(eta) + qb_gamma.mul(eta.square()) {
        println!("Evaluation for h(X) failed");
        return false;
    }

    println!("Verification took {} ms", start.elapsed().as_millis());
    true
}

pub struct CqLookupInputRound1<E: PairingEngine> {
    pub phi_com: E::G1Affine,
}

pub struct CqLookupInputRound2<E: PairingEngine> {
    pub sparse_A_vec: Vec<(usize, E::Fr)>,              // sparse A polynomial
    pub a_com: E::G1Affine,                             // commitment to A
    pub qa_com: E::G1Affine,                            // A.(T+beta)-phi = Z_H.Q_A
    pub b_poly: DensePolynomial<E::Fr>,                 // B polynomial interpolating 1/(beta + f_i)
    pub b0_poly: DensePolynomial<E::Fr>,                // B0 = (B - B(0))/X
    pub qb_poly: DensePolynomial<E::Fr>,                // B(f+\beta)-1 = Q_B.Z_V
    pub f_poly: DensePolynomial<E::Fr>,                 // B_0.X^{N-1-(m-2)}
    pub b0_com: E::G1Affine,                            // commitment to B0
    pub qb_com: E::G1Affine,                            // commitment to Q_B
    pub p_com: E::G1Affine,                             // commitment to p
    pub a0_com: E::G1Affine,                            // commitment to poly A(X)-A(0)/X
    pub a0: E::Fr
}

pub struct CqLookupInputRound3<E: PairingEngine> {
    pub h_poly: DensePolynomial<E::Fr>,                 // h = B0 + \eta f + \eta^2 Q_B
    pub h_gamma: E::Fr,                                 // evaluation of h at gamma
    pub pi_h: E::G1Affine,                              // kzg proof of evaluation of h at gamma
}


/**
 * Compute the update to the encoded quotient computed from the base table
 * using the difference between current and base table (the cache table)
 * This is accomplished via the algorithm described in Section 7,
 * "Fast Lookups from Approximate Pre-processing" in the paper https://eprint.iacr.org/2024/840.pdf
 */
pub fn compute_encoded_quotient_delta<E: PairingEngine>(
    delta_input: &CqDeltaInput<E>,
    cq_pp: &CqPublicParams<E>,
    domain_size: usize,
) -> E::G1Affine {
    let domain: GeneralEvaluationDomain<E::Fr> = GeneralEvaluationDomain::new(1usize << domain_size).unwrap();
    let N = domain.size();
    let mut cache = InvertPolyCache::<E::Fr>::new();

    let mut start = Instant::now();

    // compute the scalars a_i, i\in I and b_j,j \in K according to the paper.
    let (a_vec, b_vec) = compute_scalar_coefficients::<E::Fr>(
        &delta_input.t_j_vec,
        &delta_input.c_i_vec,
        &delta_input.set_k,
        &delta_input.set_i,
        domain_size,
        &mut cache,
    );

    println!("Scalar computation took {} msec", start.elapsed().as_millis());
    // prepare for MSM
    let mut vec_grp_msm: Vec<E::G1Affine> = Vec::new();
    let mut vec_scalar_msm: Vec<E::Fr> = Vec::new();
    for i in 0..delta_input.set_i.len() {
        vec_grp_msm.push(cq_pp.openings_z_h_poly[delta_input.set_i[i]]);
        vec_scalar_msm.push(a_vec[i].mul(delta_input.c_i_vec[i]));
    }

    for i in 0..delta_input.set_k.len() {
        vec_grp_msm.push(cq_pp.openings_z_h_poly[delta_input.set_k[i]]);
        vec_scalar_msm.push(b_vec[i].mul(delta_input.t_j_vec[i]).mul(domain.element(delta_input.set_k[i])));
    }

    start = Instant::now();
    let a_com = VariableBaseMSM::multi_scalar_mul(&vec_grp_msm,
                                                  &vec_scalar_msm.clone().into_iter().map(|x| x.into_repr()).collect::<Vec<_>>());
    let a_com = a_com.into_affine().mul(E::Fr::from(N as u128).inverse().unwrap()).into_affine();
    println!("MSM took {} msecs", start.elapsed().as_millis());
    // compute the MSM corresponding to lambda_poly_openings
    let mut vec_grp_msm: Vec<E::G1Affine> = Vec::new();
    let mut vec_scalar_msm: Vec<E::Fr> = Vec::new();

    for i in 0..delta_input.set_i.len() {
        let idx = delta_input.set_i[i];
        vec_grp_msm.push(cq_pp.openings_mu_polys[idx]);
        vec_scalar_msm.push(delta_input.t_j_vec[i].mul(delta_input.c_i_vec[i]));
    }
    let a1_com = VariableBaseMSM::multi_scalar_mul(&vec_grp_msm,
                                                  &vec_scalar_msm.clone().into_iter().map(|x| x.into_repr()).collect::<Vec<_>>());

    a_com.add(a1_com.into_affine())
}

/**
 * Prover computation for round 1 of the CQ protocol
 * This involves commitment to the sparse multiplicity polynomial
 * phi(X) which interpolates multiplicity m_i at \omega^i
 */
pub fn compute_prover_round1<E: PairingEngine>(
    example: &CqExample<E::Fr>,
    h_domain_size: usize,
    cq_pp: &CqPublicParams<E>,

) -> CqLookupInputRound1<E>
{
    // commitment to the phi poly is computed
    let h_domain: GeneralEvaluationDomain<E::Fr> = GeneralEvaluationDomain::new(1usize << h_domain_size).unwrap();
    let N = h_domain.size();
    let mut scalars = Vec::<E::Fr>::new();
    let mut gelems: Vec<E::G1Affine> = Vec::new();
    for iter in &example.m_vec {
        // we scale each m_i with \omega^i, as the precomputed parameters
        // contain quotients [Z_H(X)/X-\omega^i] and not [\lambda_i(X)]
        // These differ by scalar factor of \omega^i/N, the latter scaling by 1/N is applied
        // to the final scalar product.
        scalars.push(iter.1.mul(h_domain.element(*iter.0)));
        gelems.push(cq_pp.openings_z_h_poly[*iter.0])
    }

    let phi_com = VariableBaseMSM::multi_scalar_mul(&gelems,
                                                    &scalars.clone().into_iter().map(|x| x.into_repr()).collect::<Vec<_>>());

    let phi_com = phi_com.into_affine().mul(E::Fr::from(N as u128).inverse().unwrap()).into_affine();
    CqLookupInputRound1 { phi_com }
}

/**
 * in round two, prover computes:
 * (i) the A polynomial that interpolates m_i/(\beta + t_i) at i^{th} N^th root of unity, and commitment to it.
 * (ii) Computes commitment to quotient polynomial Q_A satisfying A(X)(\beta + t(X)) - m(X) = Q_A(X).Z_H(X). Note the commitment is directly computed
 *  from pre-computed quotients, without computing the polynomial itself.
 * (iii) Computes polynomial B(X) interpolating 1/(\beta + f_i) at i^{th} m^th root of unity.
 * (iv) Computes and commits to polynomial B_0(X) = (B(X) - B(0))/X
 * (v) Computes and commits to Q_B polynomial satisfying B(X)(\beta + f(X))-1 = Q_B(X).Z_V(X)
 * (vi) Computes and commits to polynomial P(X) = B_0(X).X^{N-1-(n-2)}. This polynomial is used to upper-bound the degree of B_0.
 */
#[allow(non_snake_case)]
fn compute_prover_round2<E: PairingEngine>(
    beta: E::Fr,
    instance: &CqLookupInstance<E>,
    input: &CqProverInput<E>,
    example: &CqExample<E::Fr>,
    cq_pp: &CqPublicParams<E>,
    pp: &PublicParameters<E>) -> CqLookupInputRound2<E> {

    let h_domain = GeneralEvaluationDomain::<E::Fr>::new(1 << instance.h_domain_size).unwrap();
    let m_domain: GeneralEvaluationDomain<E::Fr> = GeneralEvaluationDomain::new(1 << instance.m_domain_size).unwrap();

    let N = h_domain.size();
    // compute non-zero lagrange coefficients A_i = m_i/(t_i + \beta)
    // scalars_A will contain A_i.(w^i): This is because our openings are for [Z_H(X)/X-w^i] and not L_i(X)
    // scalars_A0 will simply contain A_i's
    // gens_A will contain respective openings [Z_H(X)/X-w^i]
    // gens_Q will contain table openings [(T(X) - T(w^i))/(X-w^i)]
    // sparse_A_vec simply stores tuples (i, A_i) for A_i\neq 0 for future use.
    let mut scalars_A: Vec<E::Fr> = Vec::new();
    let mut scalars_A0: Vec<E::Fr> = Vec::new();
    let mut gens_A: Vec<E::G1Affine> = Vec::new();
    let mut gens_Q: Vec<E::G1Affine> = Vec::new();
    let mut sparse_A_vec: Vec<(usize, E::Fr)> = Vec::new();

    for i in 0..example.i_set.len() {
        let idx = example.i_set[i];
        let m_i = *example.m_vec.get(&idx).unwrap();
        let t_i = E::Fr::from(example.table[idx] as u128);

        let coeff:E::Fr = m_i.div(t_i.add(beta)); // m_i/(t_i + \beta)
        scalars_A0.push(coeff);
        sparse_A_vec.push((idx, coeff.mul(h_domain.element(idx))));
        scalars_A.push(coeff.mul(h_domain.element(idx)));     // scale by w^i
        gens_A.push(cq_pp.openings_z_h_poly[idx]);
        gens_Q.push(input.openings_t_poly[idx]);         // [Z_H(X)/X-w]
    }
    // Compute commitment [A(X)] = \sum_{i}A_i[L_i(X)]. Scale by 1/N after the multi-exp
    let a_com = VariableBaseMSM::multi_scalar_mul(&gens_A,
                                                  &scalars_A.clone().into_iter().map(|x| x.into_repr()).collect::<Vec<_>>());
    let a_com = a_com.into_affine().mul(E::Fr::from(N as u128).inverse().unwrap()).into_affine();

    // Compute commitment [Q_A(X)] = \sum_{i}A_i[Q_i(X)] where Q_i(X)=(1/N)w^i(T(X)-T(w^i))/(X-w^i). Scale by 1/N as before.
    let qa_com = VariableBaseMSM::multi_scalar_mul(&gens_Q,
                                                   &scalars_A.clone().into_iter().map(|x| x.into_repr()).collect::<Vec<_>>());
    let qa_com = qa_com.into_affine().mul(E::Fr::from(N as u128).inverse().unwrap()).into_affine();

    // next we interpolate the B polynomial which evaluates to 1/(beta + f_i) on Z_V
    let mut evals_B: Vec<E::Fr> = Vec::new();
    let f_vec_ff = example.f_vec.clone().into_iter().map(|x| E::Fr::from(x as u128)).collect::<Vec<_>>();
    for i in 0usize..m_domain.size() {
        let val = E::Fr::one().div(beta + f_vec_ff[i]);
        evals_B.push(val);
    }
    let b_coeffs = m_domain.ifft(&evals_B);
    let b_poly = DensePolynomial::<E::Fr>::from_coefficients_vec(b_coeffs.clone());
    // Compute coefficients of polynomial B_0(X) = (B(X) - B(0))/X
    let mut b0_coeffs: Vec<E::Fr> = Vec::new();
    for i in 1..=b_poly.degree() {
        b0_coeffs.push(b_coeffs[i]);
    }
    let b0_poly = DensePolynomial::<E::Fr>::from_coefficients_vec(b0_coeffs);
    let b0_com = KZGCommit::<E>::commit_g1(&pp.poly_ck, &b0_poly);

    // Compute f(X) and Q_B(X)
    let f_poly = DensePolynomial::<E::Fr>::from_coefficients_vec(m_domain.ifft(&f_vec_ff));
    let d_poly = &b_poly * &(&f_poly + &DensePolynomial::from_coefficients_vec(vec![beta]));
    let (qb_poly, _) = d_poly.divide_by_vanishing_poly(m_domain).unwrap();
    let qb_com = KZGCommit::<E>::commit_g1(&pp.poly_ck, &qb_poly);

    // another MSM to compute [P(X)] for P(X)=B(X)X^{N-1-(n-2)}
    let scalars_P = b0_poly.coeffs.clone();
    let scalars_P = scalars_P.into_iter().map(|x| x.into_repr()).collect::<Vec<_>>();
    let mut gens_P: Vec<E::G1Affine> = Vec::new();
    let shift = N - 1 - (m_domain.size() - 2);
    for i in 0..scalars_P.len() {
        gens_P.push(pp.poly_ck.powers_of_g[shift + i]);
    }
    let p_com = VariableBaseMSM::multi_scalar_mul(&gens_P, &scalars_P).into_affine();

    // compute [A_0(X)] for A_0 = (A(X) - A(0))/X. See CQ paper for how this is done.
    let mut sum_A0 = E::Fr::zero();
    for i in 0..scalars_A0.len() {
        sum_A0.add_assign(scalars_A0[i]);
    }


    let a0_com_1 = VariableBaseMSM::multi_scalar_mul(&gens_A,
                                                     &scalars_A0.into_iter().map(|x| x.into_repr()).collect::<Vec<_>>());
    let a0_com_2 = pp.poly_ck.powers_of_g[N-1].mul(sum_A0);
    let a0_com: E::G1Affine = a0_com_1.into_affine() + a0_com_2.into_affine().neg();
    let a0_com = a0_com.mul(E::Fr::from(N as u128).inverse().unwrap()).into_affine();

    CqLookupInputRound2 {
        sparse_A_vec: sparse_A_vec,
        a_com: a_com,
        qa_com: qa_com,
        b_poly: b_poly,
        b0_poly: b0_poly,
        qb_poly: qb_poly,
        f_poly: f_poly,
        b0_com: b0_com,
        qb_com: qb_com,
        p_com: p_com,
        a0_com: a0_com,
        a0: sum_A0.mul(E::Fr::from(N as u128).inverse().unwrap())
    }
}

/**
 * In round 3, prover provides aggregated KZG proof for evaluations
 * of polynomials sent in earlier rounds
 */
fn compute_prover_round3<E: PairingEngine>(
    gamma: E::Fr,
    eta: E::Fr,
    round2: &CqLookupInputRound2<E>,
    pp: &PublicParameters<E>,
) -> CqLookupInputRound3<E> {
    // Compute aggregated poly H(X) = B_0(X) + eta f(X) + eta^2 Q_B(X)
    // and provide a KZG proof of evaluation of H(X) at X=gamma.
    let h_poly = &round2.b0_poly + &(&round2.f_poly.mul(eta) + &round2.qb_poly.mul(eta.square()));
    let (h_gamma, pi_h) = KZGCommit::<E>::open_g1_batch(
        &pp.poly_ck,
        &h_poly,
        None,
        &[gamma]
    );

    CqLookupInputRound3::<E> {
        h_poly: h_poly,
        h_gamma: h_gamma[0],
        pi_h: pi_h
    }
}



// Structures for reading/storing table parameters
#[derive(Debug, PartialEq)]
// Data structure to be stored in a file: polynomial, its commitment, and its
// openings (for certain SRS)
pub struct TableInputCq<E: PairingEngine> {
    pub c_poly: DensePolynomial<E::Fr>,
    pub c_com: E::G2Affine,
    pub openings: Vec<E::G1Affine>,
}


impl<E: PairingEngine> TableInputCq<E> {
    pub fn store(&self, path: &str) {
        // 1. Polynomial
        let mut o_bytes = vec![];
        let mut f = File::create(path).expect("Unable to create file");
        let len: u32 = self.c_poly.len().try_into().unwrap();
        let len_bytes = len.to_be_bytes();
        f.write_all(&len_bytes).expect("Unable to write data");
        let len32: usize = len.try_into().unwrap();
        for i in 0..len32 {
            self.c_poly.coeffs[i]
                .serialize_uncompressed(&mut o_bytes)
                .ok();
        }
        f.write_all(&o_bytes).expect("Unable to write data");

        // 2. Commitment
        o_bytes.clear();
        self.c_com.serialize_uncompressed(&mut o_bytes).ok();
        f.write_all(&o_bytes).expect("Unable to write data");

        // 3. Openings
        o_bytes.clear();
        let len: u32 = self.openings.len().try_into().unwrap();
        let len_bytes = len.to_be_bytes();
        f.write_all(&len_bytes).expect("Unable to write data");
        let len32: usize = len.try_into().unwrap();
        for i in 0..len32 {
            self.openings[i].serialize_uncompressed(&mut o_bytes).ok();
        }
        f.write_all(&o_bytes).expect("Unable to write data");
    }

    pub fn load(path: &str) -> TableInputCq<E> {
        const FR_UNCOMPR_SIZE: usize = 32;
        const G1_UNCOMPR_SIZE: usize = 96;
        const G2_UNCOMPR_SIZE: usize = 192;
        let mut data = Vec::new();
        let mut f = File::open(path).expect("Unable to open file");
        f.read_to_end(&mut data).expect("Unable to read data");

        // 1. reading  c_poly
        let mut cur_counter: usize = 0;
        let len_bytes: [u8; 4] = (&data[0..4]).try_into().unwrap();
        let len: u32 = u32::from_be_bytes(len_bytes);
        let mut coeffs = vec![];
        let len32: usize = len.try_into().unwrap();
        cur_counter += 4;
        for i in 0..len32 {
            let buf_bytes =
                &data[cur_counter + i * FR_UNCOMPR_SIZE..cur_counter + (i + 1) * FR_UNCOMPR_SIZE];
            let tmp = E::Fr::deserialize_unchecked(buf_bytes).unwrap();
            coeffs.push(tmp);
        }
        cur_counter += len32 * FR_UNCOMPR_SIZE;

        // 2. c_com
        let buf_bytes = &data[cur_counter..cur_counter + G2_UNCOMPR_SIZE];
        let c_com = E::G2Affine::deserialize_unchecked(buf_bytes).unwrap();
        cur_counter += G2_UNCOMPR_SIZE;

        // 3 openings
        let len_bytes: [u8; 4] = (&data[cur_counter..cur_counter + 4]).try_into().unwrap();
        let len: u32 = u32::from_be_bytes(len_bytes);
        let mut openings = vec![];
        let len32: usize = len.try_into().unwrap();
        cur_counter += 4;
        for _ in 0..len32 {
            let buf_bytes = &data[cur_counter..cur_counter + G1_UNCOMPR_SIZE];
            let tmp = E::G1Affine::deserialize_unchecked(buf_bytes).unwrap();
            openings.push(tmp);
            cur_counter += G1_UNCOMPR_SIZE;
        }

        TableInputCq {
            c_poly: DensePolynomial { coeffs },
            c_com,
            openings,
        }
    }
}

// helpful functions for storing/generating caulkplus public parameters
impl<E: PairingEngine> CqPublicParams<E> {
    pub fn store(&self) {
        let path_z_h = format!(
            "polys_cq/poly_{}_openings_{}_{}.setup",
            "z_h",
            self.log_poly.degree() + 1,
            E::Fq::size_in_bits()
        );

        let path_log_poly = format!(
            "polys_cq/poly_{}_openings_{}_{}.setup",
            "log_poly",
            self.log_poly.degree() + 1,
            E::Fq::size_in_bits()
        );

        let path_mu_polys = format!(
            "polys_cq/poly_{}_openings_{}_{}.setup",
            "mu_poly",
            self.log_poly.degree() + 1,
            E::Fq::size_in_bits()
        );


        let table_z_h: TableInputCq<E> = TableInputCq {
            c_com: self.z_h_com.clone(),
            c_poly: Default::default(),
            openings: self.openings_z_h_poly.clone()
        };

        let table_log_poly: TableInputCq<E> = TableInputCq {
            c_com: self.log_poly_com.clone(),
            c_poly: self.log_poly.clone(),
            openings: self.openings_log_poly.clone()
        };

        let table_mu_poly: TableInputCq<E> = TableInputCq {
            c_com: E::G2Affine::zero(),
            c_poly: Default::default(),
            openings: self.openings_mu_polys.clone(),
        };

        table_z_h.store(&path_z_h);
        table_log_poly.store(&path_log_poly);
        table_mu_poly.store(&path_mu_polys);
    }

    pub fn load(domain_size_bits: usize) -> CqPublicParams<E> {
        let domain_size: usize = 1 << domain_size_bits;
        let path_z_h = format!(
            "polys_cq/poly_{}_openings_{}_{}.setup",
            "z_h",
            domain_size,
            E::Fq::size_in_bits()
        );

        let path_log_poly = format!(
            "polys_cq/poly_{}_openings_{}_{}.setup",
            "log_poly",
            domain_size,
            E::Fq::size_in_bits()
        );

        let path_mu_polys = format!(
            "polys_cq/poly_{}_openings_{}_{}.setup",
            "mu_poly",
            domain_size,
            E::Fq::size_in_bits()
        );


        let table_z_h: TableInputCq<E> = TableInputCq::load(&path_z_h);
        let table_log_poly: TableInputCq<E> = TableInputCq::load(&path_log_poly);
        let table_mu_poly: TableInputCq<E> = TableInputCq::load(&path_mu_polys);

        CqPublicParams::<E> {
            z_h_com: table_z_h.c_com,
            log_poly_com: table_log_poly.c_com,
            log_poly: table_log_poly.c_poly,
            openings_z_h_poly: table_z_h.openings,
            openings_log_poly: table_log_poly.openings,
            openings_mu_polys: table_mu_poly.openings,
        }
    }

    pub fn new(
        pp: &PublicParameters<E>,
        h_domain_size: usize
    ) -> CqPublicParams<E> {
        let h_domain: GeneralEvaluationDomain<E::Fr> = GeneralEvaluationDomain::new(1 << h_domain_size).unwrap();
        // commit to the vanishing polynomial
        let z_h_com: E::G2Affine = pp.g2_powers[h_domain.size()] + pp.g2_powers[0].neg();
        let mut l_i_vec: Vec<E::Fr> = Vec::new();
        for i in 0..h_domain.size() {
            l_i_vec.push(E::Fr::from(i as u128));
        }
        let log_poly = DensePolynomial::from_coefficients_vec(h_domain.ifft(&l_i_vec));
        let log_poly_com = KZGCommit::<E>::commit_g2(&pp.g2_powers, &log_poly);

        // above does not work for Z_H openings as Z_H has degree = domain size.
        // Z_H/(X-w) = X^{N-1} + wX^{N-2}+...+w^{N-1}
        // Define h(X) = [s_{N-1}] + [s_{N-2}].X + ... + [1].X^{N-1}
        let mut h_vec_g: Vec<E::G1Projective> = Vec::new();
        for i in (0..h_domain.size()).rev() {
            h_vec_g.push(pp.poly_ck.powers_of_g[i].into_projective());
        }
        let openings_z_h_projective = group_dft::<E::Fr, _>(&h_vec_g, h_domain_size);
        let openings_z_h_poly: Vec<E::G1Affine> =
            openings_z_h_projective.iter().map(|x| x.into_affine()).collect();

        // compute openings of poly mu_i(X) at xi^i.
        let mut p_vec: Vec<E::G1Projective> = Vec::new();

        for i in (0..h_domain.size()).rev() {
            let scalar = E::Fr::from((h_domain.size() - 1 - i) as u128);
            p_vec.push(pp.poly_ck.powers_of_g[i].mul(scalar));
        }


        let openings_mu_polys_projective = group_dft::<E::Fr, _>(&p_vec, h_domain_size);
        let N_inv = E::Fr::from(h_domain.size() as u128).inverse().unwrap();
        let openings_mu_polys: Vec<E::G1Affine> =
            openings_mu_polys_projective.iter().map(|x| x.into_affine().mul(N_inv).into_affine()).collect();


        let openings_log_poly = KZGCommit::<E>::multiple_open::<E::G1Affine>(
            &log_poly,
            &pp.poly_ck.powers_of_g,
            h_domain_size
        );

        CqPublicParams::<E> {
            z_h_com,
            log_poly_com,
            log_poly,
            openings_z_h_poly,
            openings_log_poly,
            openings_mu_polys,
        }
    }

    pub fn new_fake(
        pp: &PublicParameters<E>,
        h_domain_size: usize
    ) -> CqPublicParams<E> {
        let h_domain: GeneralEvaluationDomain<E::Fr> = GeneralEvaluationDomain::new(1 << h_domain_size).unwrap();
        // commit to the vanishing polynomial
        let z_h_com: E::G2Affine = pp.g2_powers[h_domain.size()] + pp.g2_powers[0].neg();

        let mut l_i_vec: Vec<E::Fr> = Vec::new();
        for i in 0..h_domain.size() {
            l_i_vec.push(E::Fr::from(i as u128));
        }
        let log_poly = DensePolynomial::from_coefficients_vec(h_domain.ifft(&l_i_vec));
        let log_poly_com = KZGCommit::<E>::commit_g2(&pp.g2_powers, &log_poly);

        // compute powers of beta for fake parameters generation
        let mut rng = ark_std::test_rng();
        let beta = E::Fr::rand(&mut rng);
        let mut powers: Vec<E::Fr> = Vec::new();
        let mut power = E::Fr::one();
        for i in 0..pp.poly_ck.powers_of_g.len() {
            powers.push(power);
            power.mul_assign(beta);
        }
        let g2 = pp.g2_powers[0];
        let g1 = pp.poly_ck.powers_of_g[0];
        // -------------- Created powers of beta in srs for fake (faster) setup ------------

        // (1). Compute openings for Z_H
        // Z_H/(X-w) = X^{N-1} + wX^{N-2}+...+w^{N-1}
        // Define h(X) = s_{N-1} + s_{N-2}.X + ... + 1.X^{N-1} for s=beta
        let mut h_vec_g: Vec<E::Fr> = Vec::new();
        for i in (0..h_domain.size()).rev() {
            h_vec_g.push(powers[i]);
        }
        let openings_z_h_vec = field_dft::<E::Fr>(&h_vec_g, h_domain_size);
        // G2 encode the powers of beta and batch normalize to affine
        let mut q3: Vec<E::G1Projective> = Vec::new();
        for i in 0..openings_z_h_vec.len() {
            q3.push(g1.mul(openings_z_h_vec[i]));
        }
        let openings_z_h_poly = E::G1Projective::batch_normalization_into_affine(q3.as_ref());

        // (2) compute openings of poly mu_i(X) at xi^i.
        let mut p_vec: Vec<E::Fr> = Vec::new();
        for i in (0..h_domain.size()).rev() {
            let scalar = E::Fr::from((h_domain.size() - 1 - i) as u128);
            p_vec.push(powers[i].mul(scalar));
        }
        let openings_mu_polys_ff = field_dft::<E::Fr>(&p_vec, h_domain_size);
        let N_inv = E::Fr::from(h_domain.size() as u128).inverse().unwrap();
        let openings_mu_polys: Vec<E::G1Affine> =
            openings_mu_polys_ff.iter().map(|x| g1.mul(x.mul(N_inv)).into_affine()).collect();

        let openings_log_poly = KZGCommit::<E>::multiple_open_fake::<E::G1Affine>(
            &log_poly,
            powers.as_slice(),
            g1,
            h_domain_size
        );

        CqPublicParams::<E> {
            z_h_com,
            log_poly_com,
            log_poly,
            openings_z_h_poly,
            openings_log_poly,
            openings_mu_polys,
        }
    }
}

// helper function to generate table specific parameters for the prover
// inputs:
// @t_vec: the table vector
// @pp: public parameters containing srs of sufficient size for the table
// @h_domain_size: Size of the table in power of two
// @use_fake: If true, generates table parameters faster using SRS trapdoor to avoid group FFTs. Use this only for benchmarking and testing.
pub fn generate_cq_table_input<E: PairingEngine>(
    t_vec: &Vec<usize>,
    pp: &PublicParameters<E>,
    h_domain_size: usize,
    use_fake: bool,
) -> CqProverInput<E> {
    let N: usize = t_vec.len();
    assert_eq!(N, 1usize << h_domain_size);

    let h_domain: GeneralEvaluationDomain<E::Fr> = GeneralEvaluationDomain::new(N).unwrap();
    let mut t_vec_ff: Vec<E::Fr> = Vec::new();
    for i in 0..t_vec.len() {
        t_vec_ff.push(E::Fr::from(t_vec[i] as u128));
    }
    let t_poly = DensePolynomial::from_coefficients_vec(h_domain.ifft(&t_vec_ff));
    let t_com = KZGCommit::<E>::commit_g2(&pp.g2_powers, &t_poly);

    // create powers of beta
    let mut rng = ark_std::test_rng();
    let beta = E::Fr::rand(&mut rng);
    let mut powers: Vec<E::Fr> = Vec::new();
    let mut power = E::Fr::one();
    for i in 0..pp.poly_ck.powers_of_g.len() {
        powers.push(power);
        power.mul_assign(beta);
    }

    let openings_t_poly = if use_fake {
        KZGCommit::<E>::multiple_open_fake::<E::G1Affine>(
            &t_poly,
            powers.as_slice(),
            pp.poly_ck.powers_of_g[0],
            h_domain_size
        )
    } else {
        KZGCommit::<E>::multiple_open::<E::G1Affine>(
            &t_poly,
            &pp.poly_ck.powers_of_g,
            h_domain_size
        )
    };

    CqProverInput {
        t_com,
        t_poly,
        openings_t_poly,
    }
}



mod tests {
    use std::time::Instant;
    use ark_bls12_381::Bls12_381;
    use colored::Colorize;
    use super::*;

    const h_domain_size: usize = 20;
    const m_domain_size: usize = 10;
    const k_domain_size: usize = 17;

    #[test]
    pub fn test_setup() {
        test_setup_helper::<Bls12_381>();
    }

    #[test]
    pub fn test_run_full_protocol() {
        test_run_full_protocol_helper::<Bls12_381>();
    }

    #[test]
    pub fn test_cq_public_params() {
        test_cq_public_params_helper::<Bls12_381>();
    }

    #[test]
    pub fn test_cq_table_params() {
        test_cq_table_params_helper::<Bls12_381>();
    }

    #[test]
    pub fn test_compute_cq_proof() {
        test_compute_cq_proof_helper::<Bls12_381>();
    }

    fn test_setup_helper<E: PairingEngine>() {
        // generate public parameters for the given h_domain_size

        let h_domain_sizes: Vec<usize> = vec![16, 17, 18, 19, 20];

        for i in 0..h_domain_sizes.len() {
            let N = 1usize << h_domain_sizes[i];
            let m = 1usize << m_domain_size;
            let max_degree = N;
            // Generate SRS for degree N
            let pp: PublicParameters<E> = PublicParameters::setup(&max_degree, &N, &m, &h_domain_sizes[i]);

            // generate CQ setup
            // The new_fake function generates setup faster, but uses SRS trapdoor.
            // This is only meant for testing and benchmarking
            // Replace new_fake function with new() for correct generation using SRS only.
            let cq_pp: CqPublicParams<E> = CqPublicParams::new_fake(&pp, h_domain_sizes[i]);
            cq_pp.store();

            // Generate table parameters for table of size N
            // These are generated using fake flag set to true to save time.
            let mut t_vec: Vec<usize> = Vec::new();
            for i in 0..N {
                t_vec.push(i);
            }

            let mut start = Instant::now();
            let cp_prover_input = generate_cq_table_input(
                &t_vec,
                &pp,
                h_domain_sizes[i],
                true,
            );
            println!("Time to generate table inputs for size {} =  {} secs", h_domain_sizes[i], start.elapsed().as_secs());
            cp_prover_input.store(h_domain_sizes[i]);
        }
    }

    fn test_run_full_protocol_helper<E: PairingEngine>()
    {
        let N: usize = 1usize << h_domain_size;
        let m: usize = 1usize << m_domain_size;
        let K: usize = 1usize << k_domain_size;

        let max_degree = N;

        let mut rng = ark_std::test_rng();


        // generate public parameters (SRS for KZG commitment scheme)
        // This function will look for a pre-existing setup under the srs sub-directory for the size N
        // and load the same if one exists
        let pp: PublicParameters<E> = PublicParameters::setup(&max_degree, &N, &m, &h_domain_size);

        // Generate/public parameters required for CQ
        // This contains additional pre-computed parameters such as openings of lagrange polynomials
        // Again, the function looks for existing setup for parameters of size N in the polys_cq sub-directory
        let cq_pp: CqPublicParams<E> = CqPublicParams::load(h_domain_size);

        // Uncomment this if the parameters do not exist for given h_domain_size.
        // The function CqPublicParams::new() will generate parameters only using the srs, while
        // the function new_fake() will generate parameters quicker (for testing) but using the srs trapdoor
        // The latter is only provided for testing and benchmarking
        // ----------------------------------------------------------------------------------------
        // let cq_pp = CqPublicParams::<E>::new_fake(&pp, h_domain_size);
        // cq_pp.store();
        // ----------------------------------------------------------------------------------------

        let mut base_table: Vec<usize> = Vec::new();
        for _ in 0..N {
            base_table.push(usize::rand(&mut rng) % 10000);
        }

        // Generate pre-processed parameters for the base table
        // This will take a while, when using the srs. The use_fake = true option can
        // be used for quicker generation
        let mut start = Instant::now();
        let table_pp: CqProverInput<E> = generate_cq_table_input(&base_table, &pp, h_domain_size, true);
        println!("Generated table specific parameters in {} secs", start.elapsed().as_secs());

        let mut current_table: Vec<usize> = base_table.clone();
        // introduce upto K changes in current_table from base_table
        for _ in 0..K {
            let pos = usize::rand(&mut rng) % N;
            current_table[pos] += usize::rand(&mut rng) % 1000;
        }

        // generate a sub-vector of current_table of size m
        let mut f_vec: Vec<usize> = Vec::new();
        for _ in 0..m {
            f_vec.push(current_table[usize::rand(&mut rng) % N]);
        }

        // generate the CQ example corresponding to base table, updated table and sub-vector
        start = Instant::now();
        let example: CqExample<E::Fr> = CqExample::new_base_cache_example(&base_table, &current_table, &f_vec, h_domain_size, m_domain_size);
        println!("Created example in {} msecs", start.elapsed().as_millis());

        // generate CQ lookup proof
        start = Instant::now();
        let t_com = KZGCommit::<E>::commit_g2(&pp.g2_powers, &example.t_poly);
        let f_com = KZGCommit::<E>::commit_g1(&pp.poly_ck, &example.f_poly);
        println!("Committed instance polynomials in {} secs", start.elapsed().as_millis());

        let instance: CqLookupInstance<E> = CqLookupInstance { t_com, f_com, m_domain_size, h_domain_size };
        start = Instant::now();
        let proof = compute_cq_proof::<E>(
            &instance,
            &table_pp,
            &example,
            &cq_pp,
            &pp,
            true
        );
        println!("{}: {} msecs", "Proof Generation Time".bold(), start.elapsed().as_millis());

        // verify the proof
        start = Instant::now();
        let result = verify_cq_proof::<E>(
            &instance,
            &proof,
            &cq_pp,
            &pp,
        );
        println!("{}  = {} msecs", "Proof Verification Time".bold(), start.elapsed().as_millis());

        println!("Verification Result [ {} ]", result.to_string().bold());
    }

    fn test_compute_cq_proof_helper<E: PairingEngine>()
    {
        let N = 1usize << h_domain_size;
        let m = 1usize << m_domain_size;
        let n = h_domain_size;
        let max_degree = N;

        let pp: PublicParameters<E> = PublicParameters::setup(&max_degree, &N, &m, &n);
        let cq_pp: CqPublicParams<E> = CqPublicParams::load(h_domain_size);
        let table_pp: CqProverInput<E> = CqProverInput::load(h_domain_size);

        // this should be the t_vec for which we have table_pp
        let mut t_vec: Vec<usize> = Vec::new();
        for i in 0..N {
            t_vec.push(i);
        }

        let mut start = Instant::now();
        let example: CqExample<E::Fr> = CqExample::new(&t_vec, m_domain_size, k_domain_size);
        println!("Created example in {} msecs", start.elapsed().as_millis());

        start = Instant::now();
        let t_com = KZGCommit::<E>::commit_g2(&pp.g2_powers, &example.t_poly);
        let f_com = KZGCommit::<E>::commit_g1(&pp.poly_ck, &example.f_poly);
        println!("Committed instance polynomials in {} secs", start.elapsed().as_millis());

        let instance: CqLookupInstance<E> = CqLookupInstance { t_com, f_com, m_domain_size, h_domain_size };
        start = Instant::now();
        let proof = compute_cq_proof::<E>(
            &instance,
            &table_pp,
            &example,
            &cq_pp,
            &pp,
            true
        );
        println!("{}: {} msecs", "Proof Generation Time".bold(), start.elapsed().as_millis());

        // verify the proof
        start = Instant::now();
        let result = verify_cq_proof::<E>(
            &instance,
            &proof,
            &cq_pp,
            &pp,
        );
        println!("{}: {} msecs", "Proof Verification Time".bold(), start.elapsed().as_millis());

        println!("Verification Result [ {} ]", result.to_string().bold());
    }

    fn test_cq_public_params_helper<E: PairingEngine>()
    {
        let N: usize = 1 << h_domain_size;
        let m = 1usize << m_domain_size;
        let n = h_domain_size;
        let max_degree = N;

        let pp: PublicParameters<E> = PublicParameters::setup(&max_degree, &N, &m, &n);
        let cq_pp = CqPublicParams::<E>::new_fake(&pp, h_domain_size);
        cq_pp.store();
        let cq_pp: CqPublicParams<E> = CqPublicParams::load(h_domain_size);

        // do sanity check on the correctness of openings
        let h_domain: GeneralEvaluationDomain<E::Fr> = GeneralEvaluationDomain::new(1 << h_domain_size).unwrap();
        let mut rng = ark_std::test_rng();
        let g1 = pp.poly_ck.powers_of_g[0];
        let g1x = pp.poly_ck.powers_of_g[1];
        let g2 = pp.g2_powers[0];
        let g2x = pp.g2_powers[1];

        for i in 0usize..1000 {
            let w = usize::rand(&mut rng) % N;
            // real check for Z_H(X)=(X-w).opening[w]
            assert_eq!(E::pairing(g1, cq_pp.z_h_com),
                       E::pairing(cq_pp.openings_z_h_poly[w], g2x + g2.mul(h_domain.element(w)).into_affine().neg()));
            // real check for log_poly
            assert_eq!(E::pairing(g1, cq_pp.log_poly_com + g2.mul(E::Fr::from(w as u128)).neg().into_affine()),
                       E::pairing(cq_pp.openings_log_poly[w], g2x + g2.mul(h_domain.element(w)).neg().into_affine()));

            // check openings for mu polys
            let N_inv = E::Fr::from(N as u128).inverse().unwrap();
            let factor = N_inv.mul(h_domain.element(w));
            let mu_poly_com = cq_pp.openings_z_h_poly[w].mul(factor).into_affine();
            assert_eq!(E::pairing(mu_poly_com + g1.neg(), g2),
                       E::pairing(cq_pp.openings_mu_polys[w], g2x + g2.mul(h_domain.element(w)).neg().into_affine()));
        }
    }

    fn test_cq_table_params_helper<E: PairingEngine>()
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

        let mut start = Instant::now();
        let cp_prover_input = generate_cq_table_input(
            &t_vec,
            &pp,
            h_domain_size,
            false,
        );
        println!("Time to generate table inputs = {}", start.elapsed().as_secs());
        cp_prover_input.store(h_domain_size);

        /*
        // check t_poly correctly interpolates t_vec
        let h_domain: GeneralEvaluationDomain<E::Fr> = GeneralEvaluationDomain::new(1usize << h_domain_size).unwrap();
        let mut t_evals: Vec<E::Fr> = Vec::new();
        for i in 0..t_vec.len() {
            t_evals.push(E::Fr::from(t_vec[i] as u128));
        }

        // check openings
        let t_com = cp_prover_input.t_com;
        let g1 = pp.poly_ck.powers_of_g[0];
        let g2x = pp.g2_powers[1];
        let g2 = pp.g2_powers[0];
        for i in 0..N {
            assert_eq!(E::pairing(g1, t_com + g2.mul(t_evals[i]).neg().into_affine()),
                       E::pairing(cp_prover_input.openings_t_poly[i],g2x + g2.mul(h_domain.element(i)).neg().into_affine()));
        }
        */
    }
}

