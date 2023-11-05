// #![allow(warnings)]
#![allow(dead_code)]
// #[allow(unused_imports)]
use halo2_base::gates::{GateChip, RangeChip};
use halo2_base::utils::BigPrimeField;
use halo2_base::AssignedValue;
use halo2_base::Context;
use num_bigint::BigUint;
use zk_fixed_point_chip::gadget::fixed_point::{FixedPointChip, FixedPointInstructions};

use super::matrix::*;
use std::cmp;

/// Given matrices `m` (`N X M` dimension), `u` (`N X N` dimension), `v` (`M X M` dimension) and
/// a vector `d` (`min{N, M}` dimension) in fixed point representation with `fpchip`, performs the first part
/// of checks that the SVD of `m = u*d*v` where the vector `d` is viewed as a diagonal matrix;
///
/// `u` and `v` are unitraries and `d` is a positive decreasing vector of singular values;
///
/// Also takes as input tolerance levels `err_svd` and `err_u`, which determine the error up to which these matrices are checked (see error analysis notes)
///
/// `max_bits_d` can be set to be anything <= PRECISION_BITS; it is used to make sure no overflows occur while multiplying
///
/// Must call `check_svd_phase1` function following this function in the second phase to complete the SVD check
///
/// Might silently fail if `m` is not correctly encoded according to the fixed representation of `fpchip`
///
/// The outputs are simply witnesses to be used for the corresponding variables in `check_svd_phase1`
pub fn check_svd_phase0<F: BigPrimeField, const PRECISION_BITS: u32>(
    ctx: &mut Context<F>,
    fpchip: &FixedPointChip<F, PRECISION_BITS>,
    m: &ZkMatrix<F, PRECISION_BITS>,
    u: &ZkMatrix<F, PRECISION_BITS>,
    v: &ZkMatrix<F, PRECISION_BITS>,
    d: &ZkVector<F, PRECISION_BITS>,
    err_svd: f64,
    err_u: f64,
    max_bits_d: u32,
) -> (
    ZkMatrix<F, PRECISION_BITS>,
    ZkMatrix<F, PRECISION_BITS>,
    Vec<Vec<AssignedValue<F>>>,
    Vec<Vec<AssignedValue<F>>>,
    Vec<Vec<AssignedValue<F>>>,
) {
    #![allow(non_snake_case)]
    assert_eq!(m.num_rows, u.num_rows);
    assert_eq!(m.num_col, v.num_rows);

    let N = m.num_rows;
    // #[allow(non_snake_case)]
    let M = m.num_col;
    // #[allow(non_snake_case)]
    let minNM = cmp::min(N, M);
    // unitaries are square
    assert_eq!(u.num_rows, u.num_col);
    assert_eq!(v.num_rows, v.num_col);
    assert_eq!(minNM, d.v.len());

    let range: &RangeChip<F> = fpchip.range_gate();
    let gate: &GateChip<F> = fpchip.gate();

    // check the entries of d have at most max_bits_d + precision_bits
    let max_bits = (max_bits_d + PRECISION_BITS) as usize;
    d.entries_less_than(ctx, &fpchip, max_bits);
    // make sure d is in decreasing order
    d.entries_in_desc_order(ctx, &fpchip, max_bits);

    // check that the entries of u, v correspond to real numbers in the interval (-1.0,1.0) upto an error of 2^-PRECISION_BITS
    // unit_bnd_q = quantization of 1+2^-PRECISION_BITS
    let unit_bnd_q = BigUint::from(2u64.pow(PRECISION_BITS) + 1);
    check_mat_entries_bounded(ctx, &range, &u.matrix, &unit_bnd_q);
    check_mat_entries_bounded(ctx, &range, &v.matrix, &unit_bnd_q);

    // Lets define the transpose matrix of u and v
    let u_t: ZkMatrix<F, PRECISION_BITS> = ZkMatrix::transpose_matrix(&u);
    let v_t: ZkMatrix<F, PRECISION_BITS> = ZkMatrix::transpose_matrix(&v);

    // if-else to make sure this matrix is N X M
    let u_times_d: Vec<Vec<AssignedValue<F>>> = if minNM == M {
        mat_times_diag_mat(ctx, gate, &u.matrix, &d.v)
    } else {
        // if N < M, then you need to pad by zeroes and u_times_d should be [UD; 0] where 0 is N X (M-N) matrix of zeroes
        let zero = ctx.load_constant(F::zero());
        let mut u_times_d = mat_times_diag_mat(ctx, gate, &u.matrix, &d.v);
        for row in &mut u_times_d {
            for _ in N..M {
                row.push(zero);
            }
        }
        u_times_d
    };
    let m_times_vt: Vec<Vec<AssignedValue<F>>> = honest_prover_mat_mul(ctx, &m.matrix, &v_t.matrix);

    // define the doubly scaled errors
    let err_svd_scale =
        BigUint::from((err_svd * (2u128.pow(2 * PRECISION_BITS) as f64)).round() as u128);
    let err_u_scale =
        BigUint::from((err_u * (2u128.pow(2 * PRECISION_BITS) as f64)).round() as u128);

    check_mat_diff(ctx, &range, &u_times_d, &m_times_vt, &err_svd_scale);

    let quant = F::from(2u64.pow(PRECISION_BITS));
    let quant_square = ctx.load_constant(quant * quant);

    let u_times_ut = honest_prover_mat_mul(ctx, &u.matrix, &u_t.matrix);
    check_mat_id(ctx, &range, &u_times_ut, &quant_square, &err_u_scale);

    let v_times_vt = honest_prover_mat_mul(ctx, &v.matrix, &v_t.matrix);
    check_mat_id(ctx, &range, &v_times_vt, &quant_square, &err_u_scale);

    return (u_t, v_t, m_times_vt, u_times_ut, v_times_vt);
}

/// Second phase function for checking SVD;
///
/// `check_svd_phase0` should be run in the first phase, so that its outputs are commited to in the first phase;
///
/// Inputs correspond to the `m`, `u`, `v` as used in `check_svd_phase0` and other inputs correspond to the outputs of `check_svd_phase0`
///
/// `init_rand` is the random challenge created after the first phase; must be a commitment of all the inputs to this function
///
/// First phase might silently fail if `m` is not correctly encoded according to the fixed representation of `fpchip`
pub fn check_svd_phase1<F: BigPrimeField, const PRECISION_BITS: u32>(
    ctx: &mut Context<F>,
    fpchip: &FixedPointChip<F, PRECISION_BITS>,
    m: &ZkMatrix<F, PRECISION_BITS>,
    u: &ZkMatrix<F, PRECISION_BITS>,
    v: &ZkMatrix<F, PRECISION_BITS>,
    u_t: &ZkMatrix<F, PRECISION_BITS>,
    v_t: &ZkMatrix<F, PRECISION_BITS>,
    m_times_vt: &Vec<Vec<AssignedValue<F>>>,
    u_times_ut: &Vec<Vec<AssignedValue<F>>>,
    v_times_vt: &Vec<Vec<AssignedValue<F>>>,
    init_rand: &AssignedValue<F>,
) {
    ZkMatrix::verify_mul(ctx, &fpchip, &m, &v_t, &m_times_vt, &init_rand);
    ZkMatrix::verify_mul(ctx, &fpchip, &u, &u_t, &u_times_ut, &init_rand);
    ZkMatrix::verify_mul(ctx, &fpchip, &v, &v_t, &v_times_vt, &init_rand);
    // println!("Phase1 success");
}

/// Calculates `err_svd` and `err_u` from `eps_svd` and `eps_u` -- see Eq. 21, 22, and 23 of notes on error analysis for an explanation
///
/// `p` is the PRECISION_BITS for the fixed point chip
///
/// `size` is the size of the matrices for which the outputs are to be used
///
/// `max_norm` is the maximum operator norm for which the outputs are to be used
///
/// `eps_svd` and `eps_u` are the error parameters defined in the error analysis notes
pub fn err_calc(p: u32, size: usize, max_norm: f64, eps_svd: f64, eps_u: f64) -> (f64, f64) {
    let precision = 2.0_f64.powf(-1.0 * (p as f64 + 1.0));
    let err_svd = precision * (size as f64) * (1.0 + max_norm + eps_svd + precision)
        + (size as f64) * max_norm * precision
        + (1.0 + eps_u).powf(0.5) * (max_norm + eps_svd) * eps_u
        + (1.0 + eps_u).powf(0.5) * eps_svd;
    let err_u = eps_u + precision * (size as f64) * (2.0 * (1.0 + eps_u) + precision);
    return (err_svd, err_u);
}
