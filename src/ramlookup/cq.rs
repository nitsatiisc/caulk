use std::collections::{HashMap, HashSet};
use std::convert::TryInto;
use std::fs::File;
use std::io::{Read, Write};
use std::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg};
use ark_ec::{AffineCurve, PairingEngine, ProjectiveCurve};
use ark_ec::msm::VariableBaseMSM;
use ark_ff::{Field, One, PrimeField, Zero};
use ark_poly::{EvaluationDomain, GeneralEvaluationDomain, Polynomial, UVPolynomial};
use ark_poly::univariate::DensePolynomial;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::{cfg_into_iter, UniformRand};
use elements_frequency::interface::frequency_finder;
use crate::multi::TableInput;
use crate::{CaulkTranscript, field_dft, group_dft, KZGCommit, PublicParameters};
use crate::ramlookup::caulkplus::{CaulkPlusProverInput, CaulkPlusPublicParams};

// We can re-use Caulk+ public parameters for CQ too with minor scaling.

#[allow(non_snake_case)]
// CaulkPlus parameters on top of caulk Public Parameters
pub struct CqPublicParams<E: PairingEngine> {
    pub z_h_com: E::G2Affine,                       // commitment to vanishing poly
    pub log_poly_com: E::G2Affine,                  // commitment to log polynomial
    pub log_poly: DensePolynomial<E::Fr>,           // log polynomial on h_domain
    pub openings_z_h_poly: Vec<E::G1Affine>,        // opening proofs for polynomial X^N - 1
    pub openings_log_poly: Vec<E::G1Affine>,        // opening proofs for log polynomial
    pub openings_mu_polys: Vec<E::G1Affine>,        // these are proofs for i^th lagrange poly at xi^i.
}

// CaulkPlus table related inputs, also includes pre-computed KZG proofs
pub struct CqProverInput<E: PairingEngine> {
    pub t_com: E::G2Affine,                          // commitment to table
    pub t_poly: DensePolynomial<E::Fr>,             // polynomial interpolating the table on h_domain
    pub openings_t_poly: Vec<E::G1Affine>,          // opening proofs of the t-polynomial
}

impl<E: PairingEngine> CqProverInput<E> {
    // store the prover input in a file
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

    // load prover input from a file
    pub fn load(h_domain_size: usize) -> CqProverInput<E> {
        let path = format!(
            "polys_cq/poly_{}_openings_{}_{}.setup",
            "tbl",
            1usize << h_domain_size,
            E::Fq::size_in_bits()
        );


        let table = TableInputCq::<E>::load(&path);

        CqProverInput {
            t_com: table.c_com,
            t_poly: table.c_poly,
            openings_t_poly: table.openings
        }
    }
}


// Committed index lookup instance
pub struct CqLookupInstance<E: PairingEngine> {
    pub t_com: E::G2Affine,                         // commitment of the table
    pub f_com: E::G1Affine,                         // commitment of the a-vector (addresses)
    //pub v_com: E::G1Affine,                         // commitment of v=t[a] vector
    pub m_domain_size: usize,                       // domain size of a vector
    pub h_domain_size: usize,                       // domain size of table
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
    pub b0_gamma: E::Fr,                                // evaluation of B0 at gamma
    pub f_gamma: E::Fr,                                 // evaluation of f at gamma
    pub a0: E::Fr,                                      // a0 = A(0)
    pub h_poly: DensePolynomial<E::Fr>,                 // h = B0 + \eta f + \eta^2 Q_B
    pub h_gamma: E::Fr,                                 // evaluation of h at gamma
    pub a0_com: E::G1Affine,                            // commitment to polynomial A_0 = (A(X)-A(0))/X
    pub pi_h: E::G1Affine,                              // kzg proof of evaluation of h at gamma
}

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

// Generated with respect to a pre-processed table t
pub struct CqExample<F: PrimeField> {
    pub table: Vec<usize>,                          // table t
    pub f_vec: Vec<usize>,                          // a sub-vector of t
    pub f_poly: DensePolynomial<F>,                 // f as a polynomial
    pub m_vec: HashMap<usize, F>,                   // multiplicities vector
}

impl<F: PrimeField> CqExample<F> {
    // the function generates an example for CQ sub-vector lookup
    // For convenience, we'll generate all distinct elements from
    // and multiplicities too
    pub fn new(table: &Vec<usize>, m_domain_size: usize) -> CqExample<F> {
        let mut rng = ark_std::test_rng();
        let m = 1usize << m_domain_size;
        let mut m_vec: HashMap<usize, F> = HashMap::new();
        let mut f_vec: Vec<usize> = Vec::new();
        for i in 0..m {
            f_vec.push(table[ usize::rand(&mut rng) % table.len()]);
        }

        let m_t = frequency_finder(&table);
        let m_f = frequency_finder(&f_vec);

        for i in 0..table.len() {
            if m_f.contains_key(&table[i]) {
                let x_f = *m_f.get(&table[i]).unwrap();
                let x_t = *m_t.get(&table[i]).unwrap();
                m_vec.insert(i, F::from(x_f as u128).div(F::from(x_t as u128)));
            }
        }

        let f_vec_ff = f_vec.iter().map(|x| F::from(*x as u128)).collect::<Vec<_>>();
        let m_domain: GeneralEvaluationDomain<F> = GeneralEvaluationDomain::new(1 << m_domain_size).unwrap();
        let f_poly = DensePolynomial::from_coefficients_vec(m_domain.ifft(&f_vec_ff));
        CqExample {
            table: table.clone(),
            f_vec,
            f_poly,
            m_vec
        }

    }
}

pub fn compute_cq_proof<E: PairingEngine>(
    instance: &CqLookupInstance<E>,
    input: &CqProverInput<E>,
    example: &CqExample<E::Fr>,
    cq_pp: &CqPublicParams<E>,
    pp: &PublicParameters<E>
) -> CqProof<E> {
    let N = 1usize << instance.h_domain_size;
    let m = 1usize << instance.m_domain_size;
    let mut transcript = CaulkTranscript::<E::Fr>::new();
    // add instance to the transcript
    transcript.append_element(b"t_com", &instance.t_com);
    transcript.append_element(b"f_com", &instance.f_com);

    let round1  = compute_prover_round1(example, instance.h_domain_size, cq_pp);
    transcript.append_element(b"phi_com", &round1.phi_com);
    let beta = transcript.get_and_append_challenge(b"ch_beta");
    let round2 = compute_prover_round2(beta, instance, input, example, cq_pp, pp);
    // add elements to transcript
    transcript.append_element(b"a_com", &round2.a_com);
    transcript.append_element(b"qa_com", &round2.qa_com);
    transcript.append_element(b"b0_com", &round2.b0_com);
    transcript.append_element(b"qb_com", &round2.qb_com);
    transcript.append_element(b"p_com", &round2.p_com);
    transcript.append_element(b"a0_com", &round2.a0_com);

    // sanity check
    assert_eq!(E::pairing(round2.b0_com, pp.g2_powers[(N-1)-(m-2)]), E::pairing(round2.p_com, pp.g2_powers[0]),
     "pairing check failed");
    assert_eq!(E::pairing(round2.a_com, instance.t_com),
               E::pairing(round2.qa_com, cq_pp.z_h_com).mul(
                   E::pairing(round1.phi_com.add(round2.a_com.mul(beta).into_affine().neg()), pp.g2_powers[0])), "pairing failed for a_com");

    let gamma = transcript.get_and_append_challenge(b"ch_gamma");
    // prover sends evaluations: A(0), f(\gamma), B_0(\gamma)
    let f_gamma = round2.f_poly.evaluate(&gamma);
    let b0_gamma = round2.b0_poly.evaluate(&gamma);
    let mut a0 = E::Fr::zero();
    for i in 0..round2.sparse_A_vec.len() {
        a0.add_assign(round2.sparse_A_vec[i].1);
    }
    a0.mul_assign(E::Fr::from(N as u128).inverse().unwrap());

    // add the evaluations to the transcript
    transcript.append_element(b"a0", &a0);
    transcript.append_element(b"f_gamma", &f_gamma);
    transcript.append_element(b"b0_gamma", &b0_gamma);

    // sanity check
    assert_eq!(E::pairing(round2.a_com.add(pp.poly_ck.powers_of_g[0].mul(round2.a0).into_affine().neg()), pp.g2_powers[0]),
        E::pairing(round2.a0_com, pp.g2_powers[1]), "Pairing check on a0 failed");




    let eta = transcript.get_and_append_challenge(b"ch_eta");


    todo!();


    /*
    CqProof::<E> {
        phi_com: (),
        a_com: (),
        qa_com: (),
        b0_com: (),
        qb_com: (),
        p_com: (),
        b0_gamma: (),
        f_gamma: (),
        a0: (),
        h_gamma: (),
        a0_com: (),
        pi_h: (),
    }

     */
}

fn compute_prover_round2<E: PairingEngine>(
    beta: E::Fr,
    instance: &CqLookupInstance<E>,
    input: &CqProverInput<E>,
    example: &CqExample<E::Fr>,
    cq_pp: &CqPublicParams<E>,
    pp: &PublicParameters<E>) -> CqLookupInputRound2<E> {

    // compute non-zero lagrange coefficients A_i = m_i/(t_i + \beta)
    let h_domain = GeneralEvaluationDomain::<E::Fr>::new(1 << instance.h_domain_size).unwrap();
    let m_domain: GeneralEvaluationDomain<E::Fr> = GeneralEvaluationDomain::new(1 << instance.m_domain_size).unwrap();

    let N = h_domain.size();
    let mut scalars_A: Vec<E::Fr> = Vec::new();
    let mut scalars_A0: Vec<E::Fr> = Vec::new();
    let mut gens_A: Vec<E::G1Affine> = Vec::new();
    let mut gens_Q: Vec<E::G1Affine> = Vec::new();
    let mut sparse_A_vec: Vec<(usize, E::Fr)> = Vec::new();

    for iter in &example.m_vec {
        let coeff:E::Fr = iter.1.div(E::Fr::from(example.table[*iter.0] as u128).add(beta)); // m_i/(t_i + \beta)
        scalars_A0.push(coeff);
        sparse_A_vec.push((*iter.0, coeff));
        scalars_A.push(coeff.mul(h_domain.element(*iter.0)));     // scale by w^i
        gens_A.push(cq_pp.openings_z_h_poly[*iter.0]);
        gens_Q.push(input.openings_t_poly[*iter.0]);         // [Z_H(X)/X-w]
    }
    let a_com = VariableBaseMSM::multi_scalar_mul(&gens_A,
                                                    &scalars_A.clone().into_iter().map(|x| x.into_repr()).collect::<Vec<_>>());
    let a_com = a_com.into_affine().mul(E::Fr::from(N as u128).inverse().unwrap()).into_affine();

    let qa_com = VariableBaseMSM::multi_scalar_mul(&gens_Q,
                                                &scalars_A.clone().into_iter().map(|x| x.into_repr()).collect::<Vec<_>>());
    let qa_com = qa_com.into_affine().mul(E::Fr::from(N as u128).inverse().unwrap()).into_affine();

    // next we interpolate the B polynomial
    let mut evals_B: Vec<E::Fr> = Vec::new();
    let f_vec_ff = example.f_vec.clone().into_iter().map(|x| E::Fr::from(x as u128)).collect::<Vec<_>>();
    for i in 0usize..m_domain.size() {
        let val = E::Fr::one().div(beta + f_vec_ff[i]);
        evals_B.push(val);
    }
    let b_coeffs = m_domain.ifft(&evals_B);
    let b_poly = DensePolynomial::<E::Fr>::from_coefficients_vec(b_coeffs.clone());
    let mut b0_coeffs: Vec<E::Fr> = Vec::new();
    for i in 1..b_poly.degree() {
        b0_coeffs.push(b_coeffs[i]);
    }
    let b0_poly = DensePolynomial::<E::Fr>::from_coefficients_vec(b0_coeffs);
    let b0_com = KZGCommit::<E>::commit_g1(&pp.poly_ck, &b0_poly);
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

    // compute [A_0(X)] for A_0 = (A(X) - A(0))/X,
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
        scalars.push(iter.1.mul(h_domain.element(*iter.0)));
        gelems.push(cq_pp.openings_z_h_poly[*iter.0])
    }

    let phi_com = VariableBaseMSM::multi_scalar_mul(&gelems,
                                                    &scalars.clone().into_iter().map(|x| x.into_repr()).collect::<Vec<_>>());

    let phi_com = phi_com.into_affine().mul(E::Fr::from(N as u128).inverse().unwrap()).into_affine();
    CqLookupInputRound1 { phi_com }
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
pub fn generate_cq_table_input<E: PairingEngine>(
    t_vec: &Vec<usize>,
    pp: &PublicParameters<E>,
    h_domain_size: usize,
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


    let openings_t_poly = KZGCommit::<E>::multiple_open_fake::<E::G1Affine>(
        &t_poly,
        powers.as_slice(),
        pp.poly_ck.powers_of_g[0],
        h_domain_size
    );

    CqProverInput {
        t_com,
        t_poly,
        openings_t_poly,
    }
}



mod tests {
    use std::time::Instant;
    use ark_bls12_381::Bls12_381;
    use crate::ramlookup::caulkplus::generate_caulkplus_prover_input;
    use super::*;

    const h_domain_size: usize = 16;
    const m_domain_size: usize = 5;

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

        let example: CqExample<E::Fr> = CqExample::new(&t_vec, m_domain_size);

        let t_com = table_pp.t_com;
        let f_com = KZGCommit::<E>::commit_g1(&pp.poly_ck, &example.f_poly);
        let instance: CqLookupInstance<E> = CqLookupInstance { t_com, f_com, m_domain_size, h_domain_size };
        let proof = compute_cq_proof::<E>(
            &instance,
            &table_pp,
            &example,
            &cq_pp,
            &pp
        );


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
                       E::pairing(cq_pp.openings_z_h_poly[w],g2x + g2.mul(h_domain.element(w)).into_affine().neg()));
            // real check for log_poly
            assert_eq!(E::pairing(g1, cq_pp.log_poly_com + g2.mul(E::Fr::from(w as u128)).neg().into_affine()),
                       E::pairing(cq_pp.openings_log_poly[w],g2x + g2.mul(h_domain.element(w)).neg().into_affine()));

            // check openings for mu polys
            let N_inv = E::Fr::from(N as u128).inverse().unwrap();
            let factor = N_inv.mul(h_domain.element(w));
            let mu_poly_com = cq_pp.openings_z_h_poly[w].mul(factor).into_affine();
            assert_eq!(E::pairing(mu_poly_com + g1.neg(), g2),
                       E::pairing(cq_pp.openings_mu_polys[w],g2x + g2.mul(h_domain.element(w)).neg().into_affine()));
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
            h_domain_size
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


