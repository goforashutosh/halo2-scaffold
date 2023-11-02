// #![allow(warnings)]
#![allow(dead_code)]
#![allow(unused_imports)]
use clap::Parser;
use halo2_base::gates::{GateChip, GateInstructions, RangeChip, RangeInstructions};
use halo2_base::utils::{BigPrimeField, ScalarField};
use halo2_base::AssignedValue;
use halo2_base::{
    halo2_proofs::{
        dev::MockProver,
        halo2curves::bn256::{Bn256, Fr, G1Affine},
        plonk::{create_proof, keygen_pk, keygen_vk, verify_proof, Error},
        poly::{
            commitment::ParamsProver,
            kzg::{
                commitment::{KZGCommitmentScheme, ParamsKZG},
                multiopen::{ProverSHPLONK, VerifierSHPLONK},
                strategy::SingleStrategy,
            },
        },
        transcript::{
            Blake2bRead, Blake2bWrite, Challenge255, TranscriptReadBuffer, TranscriptWriterBuffer,
        },
    },
    Context,
    QuantumCell::{Constant, Existing, Witness},
};
use rand::Rng;
use serde::{Deserialize, Serialize};
use std::env::{set_var, var};
use std::fs;
use zk_fixed_point_chip::gadget::fixed_point::{FixedPointChip, FixedPointInstructions};

use axiom_eth::rlp::{
    builder::{FnSynthesize, RlcThreadBuilder, RlpCircuitBuilder},
    rlc::RlcChip,
    *,
};
use halo2_svd::matrix::*;
use halo2_svd::svd::*;
use rand::{rngs::StdRng, SeedableRng};
use std::cmp;

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct CircuitInput {
    pub d: Vec<f64>,
    pub m: Vec<Vec<f64>>,
    pub u: Vec<Vec<f64>>,
    pub v: Vec<Vec<f64>>,
}

/// simple tests to make sure zkvector is okay; can also be randomized
fn test_zkvector<F: ScalarField>(ctx: &mut Context<F>)
where
    F: BigPrimeField,
{
    // lookup bits must agree with the size of the lookup table, which is specified by an environmental variable
    let lookup_bits =
        var("LOOKUP_BITS").unwrap_or_else(|_| panic!("LOOKUP_BITS not set")).parse().unwrap();
    const PRECISION_BITS: u32 = 32;
    // fixed-point exp arithmetic
    let fpchip = FixedPointChip::<F, PRECISION_BITS>::default(lookup_bits);

    const N: usize = 5;
    const M: usize = 4;
    let mut matrix: Vec<Vec<f64>> = Vec::new();
    for i in 0..N {
        matrix.push(Vec::<f64>::new());
        for j in 0..M {
            matrix[i].push((i as f64) + (j as f64) / 10.0);
        }
    }
    println!("matrix = {:?}", matrix);

    let zkmatrix: ZkMatrix<F, PRECISION_BITS> = ZkMatrix::new(ctx, &fpchip, &matrix);

    println!("zkmatrix = ");
    zkmatrix.print(&fpchip);

    let mut v1: Vec<f64> = Vec::new();
    for i in 0..M {
        if i % 2 == 0 {
            v1.push((i as f64) + ((i * i + 1) as f64) / 10.0);
        } else {
            v1.push(-(i as f64) + ((i * i + 1) as f64) / 10.0);
        }
    }
    // don't mutate now
    let v1 = v1;
    println!("v1 = {:?}", v1);

    let zkvec1 = ZkVector::new(ctx, &fpchip, &v1);
    println!("zkvec1 = ");
    zkvec1.print(&fpchip);

    let mut v2: Vec<f64> = Vec::new();
    for i in 0..M {
        if i % 2 == 0 {
            v2.push((1.0 + i.pow(3) as f64) / 10.0);
        } else {
            v2.push(-(1.0 + i.pow(3) as f64) / 10.0);
        }
    }
    // don't mutate now
    let v2 = v2;
    println!("v2 = {:?}", v2);

    let zkvec2 = ZkVector::new(ctx, &fpchip, &v2);
    println!("zkvec2 = ");
    zkvec2.print(&fpchip);

    println!("Inner product:");
    let mut ip = 0.0;
    for i in 0..v1.len() {
        ip += v1[i] * v2[i];
    }
    println!("f64 non-zk: {:?}", ip);

    let ip = zkvec1.inner_product(ctx, &fpchip, &zkvec2.v);
    let ip = fpchip.dequantization(*ip.value());
    println!("zk ckt: {:?}", ip);

    println!("** The errors for Norm and dist are pretty big **");
    println!("Norm:");
    let mut norm1 = 0.0;
    let mut norm2 = 0.0;
    for i in 0..v1.len() {
        norm1 += v1[i] * v1[i];
        norm2 += v2[i] * v2[i];
    }
    let norm_sq_1 = norm1;
    let norm_sq_2 = norm2;

    norm1 = norm1.powf(0.5);
    norm2 = norm2.powf(0.5);

    println!("f64 non-zk: ");
    println!("  for v1: {:?}", norm1);
    println!("  for v2: {:?}", norm2);

    let norm1: AssignedValue<F> = zkvec1.norm(ctx, &fpchip);
    let norm2: AssignedValue<F> = zkvec2.norm(ctx, &fpchip);

    let norm1 = fpchip.dequantization(*norm1.value());
    let norm2 = fpchip.dequantization(*norm2.value());
    println!("zk ckt: ");
    println!("  for v1: {:?}", norm1);
    println!("  for v2: {:?}", norm2);

    println!("dist:");
    let mut diff: Vec<f64> = Vec::new();

    for i in 0..M {
        diff.push(v1[i] - v2[i]);
    }
    let mut dist = 0.0;
    for i in 0..diff.len() {
        dist += diff[i] * diff[i];
    }
    let dist_sq = dist;
    dist = dist.powf(0.5);
    println!("for non-zk: {:?}", dist);
    let dist = zkvec1.dist(ctx, &fpchip, &zkvec2.v);
    let dist = fpchip.dequantization(*dist.value());
    println!("for zk: {:?}", dist);

    println!("Norm-squared:");
    println!("f64 non-zk: ");
    println!("  for v1: {:?}", norm_sq_1);
    println!("  for v2: {:?}", norm_sq_2);

    let norm_sq_1: AssignedValue<F> = zkvec1._norm_square(ctx, &fpchip);
    let norm_sq_2: AssignedValue<F> = zkvec2._norm_square(ctx, &fpchip);

    let norm_sq_1 = fpchip.dequantization(*norm_sq_1.value());
    let norm_sq_2 = fpchip.dequantization(*norm_sq_2.value());
    println!("zk ckt: ");
    println!("  for v1: {:?}", norm_sq_1);
    println!("  for v2: {:?}", norm_sq_2);

    println!("dist-squared:");
    println!("for non-zk: {:?}", dist_sq);
    let dist_sq = zkvec1._dist_square(ctx, &fpchip, &zkvec2.v);
    let dist_sq = fpchip.dequantization(*dist_sq.value());
    println!("for zk: {:?}", dist_sq);

    println!("Matrix transform:");
    let mut u1: Vec<f64> = Vec::new();
    let mut u2: Vec<f64> = Vec::new();

    for i in 0..N {
        u1.push(0.0);
        u2.push(0.0);
        for j in 0..M {
            u1[i] += matrix[i][j] * v1[j];
            u2[i] += matrix[i][j] * v2[j];
        }
    }
    println!("f64 non-zk: ");
    println!("  for v1: {:?}", u1);
    println!("  for v2: {:?}", u2);

    let zku1 = zkvec1.mul(ctx, &fpchip, &zkmatrix);
    let zku2 = zkvec2.mul(ctx, &fpchip, &zkmatrix);

    println!("zk ckt: ");
    println!("zku1 = ");
    zku1.print(&fpchip);
    println!("zku2 = ");
    zku2.print(&fpchip);
}

/// useful for optimising cost and testing
fn test_field_mat_times_vec<F: ScalarField>(ctx: &mut Context<F>)
where
    F: BigPrimeField,
{
    // lookup bits must agree with the size of the lookup table, which is specified by an environmental variable
    let lookup_bits =
        var("LOOKUP_BITS").unwrap_or_else(|_| panic!("LOOKUP_BITS not set")).parse().unwrap();
    const PRECISION_BITS: u32 = 32;
    // fixed-point exp arithmetic
    let fpchip = FixedPointChip::<F, PRECISION_BITS>::default(lookup_bits);

    const N: usize = 5;
    const M: usize = 5;
    let mut rng = rand::thread_rng();

    let mut matrix: Vec<Vec<f64>> = Vec::new();
    for _i in 0..N {
        let mut row: Vec<f64> = Vec::new();
        for _j in 0..M {
            row.push(rng.gen_range(-100.0..100.0));
        }
        matrix.push(row);
    }

    let zkmatrix: ZkMatrix<F, PRECISION_BITS> = ZkMatrix::new(ctx, &fpchip, &matrix);

    println!("zkmatrix = ");
    zkmatrix.print(&fpchip);

    let mut v1: Vec<f64> = Vec::new();
    for _i in 0..M {
        v1.push(rng.gen_range(-100.0..100.0));
    }
    // don't mutate now
    let v1 = v1;
    // println!("v1 = {:?}", v1);

    let zkvec1 = ZkVector::new(ctx, &fpchip, &v1);
    println!("zkvec1 = ");
    zkvec1.print(&fpchip);

    println!("Matrix transform:");
    let mut u1: Vec<f64> = Vec::new();

    for i in 0..N {
        u1.push(0.0);
        for j in 0..M {
            u1[i] += matrix[i][j] * v1[j];
        }
    }
    println!("f64 non-zk: ");
    println!("  for v1: {:?}", u1);

    let zku1_s = field_mat_vec_mul(ctx, fpchip.gate(), &zkmatrix.matrix, &zkvec1.v);
    let mut zku1: Vec<AssignedValue<F>> = Vec::new();

    println!("zk ckt: ");
    for x in zku1_s {
        let (elem, _) = fpchip.signed_div_scale(ctx, x);
        zku1.push(elem);
    }
    let zku1 = ZkVector::<F, PRECISION_BITS> { v: zku1 };
    println!("zku1 = ");
    zku1.print(&fpchip);
}

pub fn two_phase_svd_verif<F: ScalarField>(
    mut builder: RlcThreadBuilder<F>,
    input: CircuitInput,
) -> RlpCircuitBuilder<F, impl FnSynthesize<F>> {
    let prover = builder.witness_gen_only();
    let ctx = builder.gate_builder.main(0);

    // NOTE: 2^-32 = 2.3e-10
    // 1e-12 error estimated for matrices with operator norm <= 100 and size <= 1000
    // multiplying this by 100 to be on the safer side
    const EPS_SVD: f64 = 1e-10;
    // theoretical analysis indicates this can be as small as 1e-13
    const EPS_U: f64 = 1e-10;
    const MAX_NORM: f64 = 100.0;
    // for PRECISION_BITS = 42, size*MAX_NORM*2^-(P+1) and MAX_NORM*EPS_U are both almost 1e-8
    // NOTE: if you decrease PRECISION_BITS, you should also increase the error value in line 46 of input-creator.py
    const PRECISION_BITS: u32 = 42;

    let degree: usize = var("DEGREE").unwrap_or_else(|_| panic!("DEGREE not set")).parse().unwrap();
    let lookup_bits: usize =
        var("LOOKUP_BITS").unwrap_or_else(|_| panic!("LOOKUP_BITS not set")).parse().unwrap();

    assert!(degree > lookup_bits, "DEGREE should be more than LOOKUP_BITS");

    let fpchip = FixedPointChip::<F, PRECISION_BITS>::default(lookup_bits);
    let range = fpchip.range_gate();

    // Import from the imput file the matrices of the svd, should satisfy m = u d v, the diagonal matrix is given as a vector
    let m = input.m;
    let u = input.u;
    let v = input.v;
    let d = input.d;

    // load in the circuit
    // m can be rectangular, say N X M matrix
    let m: ZkMatrix<F, PRECISION_BITS> = ZkMatrix::new(ctx, &fpchip, &m);
    // u will be N X N matrix
    let u: ZkMatrix<F, PRECISION_BITS> = ZkMatrix::new(ctx, &fpchip, &u);
    // v will be M X M matrix
    let v: ZkMatrix<F, PRECISION_BITS> = ZkMatrix::new(ctx, &fpchip, &v);
    // numpy gives d of length = min{N, M}
    let d: ZkVector<F, PRECISION_BITS> = ZkVector::new(ctx, &fpchip, &d);

    let max_dim = cmp::max(m.num_rows, m.num_col);

    let (err_svd, err_u) = err_calc(PRECISION_BITS, max_dim, MAX_NORM, EPS_SVD, EPS_U);

    let _chip = RlpChip::new(&range, None);
    // let witness = chip.decompose_rlp_field_phase0(ctx, inputs, max_len);

    let (u_t, v_t, m_times_vt, u_times_ut, v_times_vt) =
        check_svd_phase0(ctx, &fpchip, &m, &u, &v, &d, err_svd, err_u, 30);

    // copied from rlp_string_circuit in axiom-eth> src> rlp> tests
    let synthesize_phase1 = move |b: &mut RlcThreadBuilder<F>, rlc: &RlcChip<F>| {
        // old fpchip being moved
        let fpchip2 = fpchip;
        let range = fpchip2.range_gate();
        let chip = RlpChip::new(&range, Some(rlc));

        // closure captures `witness` variable
        println!("phase 1 synthesize begin");
        let (ctx_gate, ctx_rlc) = b.rlc_ctx_pair();

        rlc.load_rlc_cache((ctx_gate, ctx_rlc), &chip.range().gate, 1);
        let init_rand = rlc.gamma_pow_cached()[0];
        println!("The init rand = {:?}", init_rand.value());

        check_svd_phase1(
            ctx_gate,
            &fpchip2,
            &m,
            &u,
            &v,
            &u_t,
            &v_t,
            &m_times_vt,
            &u_times_ut,
            &v_times_vt,
            &init_rand,
        );
    };
    let circuit = RlpCircuitBuilder::new(builder, None, synthesize_phase1);
    // auto-configure circuit if not in prover mode for convenience
    if !prover {
        circuit.config(degree as usize, Some(6));
    }
    return circuit;
}

// fn main() {
//     set_var("DEGREE", 20.to_string());
//     set_var("LOOKUP_BITS", 19.to_string());
//     let k: u32 = var("DEGREE").unwrap_or_else(|_| panic!("DEGREE not set")).parse().unwrap();

//     // This is the correct SVD
//     let data = fs::read_to_string("./data/matrix.in").expect("Unable to read file");
//     // Use this file for an SVD that is incorrect at one position
//     // let data = fs::read_to_string("./data/matrix-wrong.in").expect("Unable to read file");

//     let input: CircuitInput = serde_json::from_str(&data).expect("JSON was not well-formatted");

//     let circuit = two_phase_svd_verif(RlcThreadBuilder::<Fr>::mock(), input);
//     MockProver::run(k, &circuit, vec![]).unwrap().assert_satisfied();

//     println!("Test passed");
// }

fn main() {
    set_var("DEGREE", 20.to_string());
    set_var("LOOKUP_BITS", 19.to_string());
    let k: u32 = var("DEGREE").unwrap_or_else(|_| panic!("DEGREE not set")).parse().unwrap();

    // This is the correct SVD
    // let data = fs::read_to_string("./data/matrix.in").expect("Unable to read file");
    // Use this file for an SVD that is incorrect at one position
    let data = fs::read_to_string("./data/matrix-wrong.in").expect("Unable to read file");

    let input: CircuitInput = serde_json::from_str(&data).expect("JSON was not well-formatted");

    env_logger::init();

    let mut rng = StdRng::from_seed([0u8; 32]);
    let params = ParamsKZG::<Bn256>::setup(k, &mut rng);
    let circuit = two_phase_svd_verif(RlcThreadBuilder::<Fr>::keygen(), input.clone());
    circuit.config(k as usize, Some(6));

    println!("vk gen started");
    let vk = keygen_vk(&params, &circuit).unwrap();
    println!("vk gen done");
    let pk = keygen_pk(&params, vk, &circuit).unwrap();
    println!("pk gen done");
    println!();
    println!("==============STARTING PROOF GEN===================");
    let break_points = circuit.0.break_points.take();
    drop(circuit);
    let circuit = two_phase_svd_verif(RlcThreadBuilder::<Fr>::prover(), input);
    *circuit.0.break_points.borrow_mut() = break_points;

    let mut transcript = Blake2bWrite::<_, _, Challenge255<_>>::init(vec![]);
    create_proof::<
        KZGCommitmentScheme<Bn256>,
        ProverSHPLONK<'_, Bn256>,
        Challenge255<G1Affine>,
        _,
        Blake2bWrite<Vec<u8>, G1Affine, Challenge255<G1Affine>>,
        _,
    >(&params, &pk, &[circuit], &[&[]], rng, &mut transcript)
    .unwrap();
    let proof = transcript.finalize();
    println!("proof gen done");
    let verifier_params = params.verifier_params();
    let strategy = SingleStrategy::new(verifier_params);
    let mut transcript = Blake2bRead::<_, _, Challenge255<_>>::init(&proof[..]);
    verify_proof::<
        KZGCommitmentScheme<Bn256>,
        VerifierSHPLONK<'_, Bn256>,
        Challenge255<G1Affine>,
        Blake2bRead<&[u8], G1Affine, Challenge255<G1Affine>>,
        SingleStrategy<'_, Bn256>,
    >(verifier_params, pk.get_vk(), strategy, &[&[]], &mut transcript)
    .unwrap();
    println!("verify done");
}

// to create input file use
// python3.9 input-creator.py <SIZE> <SIZE>
// to run use:
// cargo run --example svd_example
