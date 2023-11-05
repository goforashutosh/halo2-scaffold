// #![allow(warnings)]
#![allow(dead_code)]
// #[allow(unused_imports)]
use halo2_base::gates::{GateChip, GateInstructions, RangeChip, RangeInstructions};
use halo2_base::utils::{biguint_to_fe, BigPrimeField};
use halo2_base::{AssignedValue, QuantumCell};
use halo2_base::{
    Context,
    QuantumCell::{Constant, Existing},
};
use num_bigint::BigUint;
use poseidon::PoseidonChip;
use zk_fixed_point_chip::gadget::fixed_point::{FixedPointChip, FixedPointInstructions};

#[derive(Clone)]
/// ZKVector is always associated to a fixed point chip for which we need [PRECISION_BITS]
pub struct ZkVector<F: BigPrimeField, const PRECISION_BITS: u32> {
    pub v: Vec<AssignedValue<F>>,
}

impl<F: BigPrimeField, const PRECISION_BITS: u32> ZkVector<F, PRECISION_BITS> {
    /// Creates a ZkVector from `v` using the quantization of the `fpchip`;
    ///
    /// Does not constrain the output in anyway
    pub fn new(
        ctx: &mut Context<F>,
        fpchip: &FixedPointChip<F, PRECISION_BITS>,
        v: &Vec<f64>,
    ) -> Self {
        let mut zk_v: Vec<AssignedValue<F>> = Vec::new();
        for elem in v {
            let elem = fpchip.quantization(*elem);
            zk_v.push(ctx.load_witness(elem));
        }
        return Self { v: zk_v };
    }

    /// Returns the length of the vector
    pub fn size(&self) -> usize {
        return self.v.len();
    }

    /// Dequantizes the vector and returns it;
    ///
    /// Action is not constrained in anyway
    pub fn dequantize(&self, fpchip: &FixedPointChip<F, PRECISION_BITS>) -> Vec<f64> {
        let mut dq_v: Vec<f64> = Vec::new();
        for elem in &self.v {
            dq_v.push(fpchip.dequantization(*elem.value()));
        }
        return dq_v;
    }

    /// Prints the dequantized version of the vector and returns it;
    ///
    /// Action is not constrained in anyway
    pub fn print(&self, fpchip: &FixedPointChip<F, PRECISION_BITS>) {
        let dq_v = self.dequantize(fpchip);
        println!("[");
        for elem in dq_v {
            println!("{:?}, ", elem);
        }
        println!("]");
    }

    /// With zk constraints calculates the inner product of this vector with vector x
    ///
    /// Outputs the inner product
    ///
    /// Order doesn't matter because we are only dealing with real numbers
    ///
    /// Low level function; uses the fact that FixedPointChip.{add, mul} just call GateChip.{add, mul}
    ///
    /// Leads to about [self.size()] + 90 constraints
    pub fn inner_product(
        &self,
        ctx: &mut Context<F>,
        fpchip: &FixedPointChip<F, PRECISION_BITS>,
        x: &Vec<AssignedValue<F>>,
    ) -> AssignedValue<F> {
        // couldn't figure out how to use inner_product of fpchip because we use x: &Vec and I didn't want to move
        assert!(self.size() == x.len());

        let mut v: Vec<QuantumCell<F>> = Vec::new();
        for elem in &self.v {
            v.push(Existing(*elem));
        }
        let v = v;

        let mut u: Vec<QuantumCell<F>> = Vec::new();
        for elem in x {
            u.push(Existing(*elem));
        }
        let u = u;

        let res_s = fpchip.gate().inner_product(ctx, u, v);

        // #CONSTRAINTS = 90
        // Implementing this way allows us to amortize the cost of calling this expensive rescaling- will also lead to more accuracy
        let (res, _) = fpchip.signed_div_scale(ctx, res_s);
        return res;
    }

    /// With zk constraints calculates the square of the norm of the vector;
    ///
    /// Outputs the square of the norm
    pub fn _norm_square(
        &self,
        ctx: &mut Context<F>,
        fpchip: &FixedPointChip<F, PRECISION_BITS>,
    ) -> AssignedValue<F> {
        return self.inner_product(ctx, fpchip, &self.v);
    }

    /// With zk constraints calculates the norm of the vector;
    ///
    /// Outputs the norm;
    ///
    /// Square root function is expensive and adds a lot error; Avoid using whenever possible
    pub fn norm(
        &self,
        ctx: &mut Context<F>,
        fpchip: &FixedPointChip<F, PRECISION_BITS>,
    ) -> AssignedValue<F> {
        let norm_sq = self._norm_square(ctx, fpchip);
        return fpchip.qsqrt(ctx, norm_sq);
    }

    /// With zk constraints calculates the distance squared of the vector from vector `x`;
    ///
    /// Outputs the distance squared
    pub fn _dist_square(
        &self,
        ctx: &mut Context<F>,
        fpchip: &FixedPointChip<F, PRECISION_BITS>,
        x: &Vec<AssignedValue<F>>,
    ) -> AssignedValue<F> {
        assert_eq!(self.size(), x.len());
        let mut diff: Vec<AssignedValue<F>> = Vec::new();
        for (r, s) in self.v.iter().zip(x.iter()) {
            diff.push(fpchip.qsub(ctx, *r, *s));
        }
        let diff = Self { v: diff };
        return diff._norm_square(ctx, fpchip);
    }

    /// With zk constraints calculates the dist of the vector from vector `x`
    ///
    /// Outputs the norm;
    ///
    /// Square root function adds a lot error and is very expensive; Avoid using whenever possible
    pub fn dist(
        &self,
        ctx: &mut Context<F>,
        fpchip: &FixedPointChip<F, PRECISION_BITS>,
        x: &Vec<AssignedValue<F>>,
    ) -> AssignedValue<F> {
        let dist_sq = self._dist_square(ctx, fpchip, x);
        return fpchip.qsqrt(ctx, dist_sq);
    }

    /// Multiplies this vector by matrix `a` in the zk-circuit and returns the constrained output `a.v`
    ///
    /// Adds about N^2+90*N constraints
    pub fn mul(
        &self,
        ctx: &mut Context<F>,
        fpchip: &FixedPointChip<F, PRECISION_BITS>,
        a: &ZkMatrix<F, PRECISION_BITS>,
    ) -> Self {
        assert_eq!(a.num_col, self.size());
        let mut y: Vec<AssignedValue<F>> = Vec::new();
        // #CONSTRAINTS = N^2+90*N
        for row in &a.matrix {
            y.push(self.inner_product(ctx, fpchip, row));
        }
        return Self { v: y };
    }

    /// Constrains all the entries of the vector to be in [0, 2^max_bits)
    pub fn entries_less_than(
        &self,
        ctx: &mut Context<F>,
        fpchip: &FixedPointChip<F, PRECISION_BITS>,
        max_bits: usize,
    ) {
        for elem in &self.v {
            fpchip.range_gate().range_check(ctx, *elem, max_bits);
        }
    }

    /// Assumes all entries of the vector are in [0, 2^max_bits) (fails silently otherwise)
    ///
    /// Constrains the entries to be in decreasing order
    pub fn entries_in_desc_order(
        &self,
        ctx: &mut Context<F>,
        fpchip: &FixedPointChip<F, PRECISION_BITS>,
        max_bits: usize,
    ) {
        let mut vec_diff: Vec<AssignedValue<F>> = Vec::new();

        for i in 0..(self.v.len() - 1) {
            let ele = fpchip.qsub(ctx, self.v[i], self.v[i + 1]);
            vec_diff.push(ele);
        }

        for elem in &vec_diff {
            fpchip.range_gate().range_check(ctx, *elem, max_bits);
        }
    }
}

#[derive(Clone)]
pub struct ZkMatrix<F: BigPrimeField, const PRECISION_BITS: u32> {
    pub matrix: Vec<Vec<AssignedValue<F>>>,
    pub num_rows: usize,
    pub num_col: usize,
}
impl<F: BigPrimeField, const PRECISION_BITS: u32> ZkMatrix<F, PRECISION_BITS> {
    /// Creates a ZkMatrix from a f64 matrix
    ///
    /// Leads to num_rows*num_col new cells
    ///
    /// Does not constrain the output in anyway
    pub fn new(
        ctx: &mut Context<F>,
        fpchip: &FixedPointChip<F, PRECISION_BITS>,
        matrix: &Vec<Vec<f64>>,
    ) -> Self {
        let mut zkmatrix: Vec<Vec<AssignedValue<F>>> = Vec::new();
        let num_rows = matrix.len();
        let num_col = matrix[0].len();
        for row in matrix {
            assert!(row.len() == num_col);
        }
        for i in 0..num_rows {
            let mut new_row: Vec<AssignedValue<F>> = Vec::new();
            for j in 0..num_col {
                let elem = matrix[i][j];
                let elem = fpchip.quantization(elem);
                new_row.push(ctx.load_witness(elem));
            }
            zkmatrix.push(new_row);
        }
        return Self { matrix: zkmatrix, num_rows: num_rows, num_col: num_col };
    }

    /// Dequantizes the matrix and returns it;
    ///
    /// Action is not constrained in anyway
    pub fn dequantize(&self, fpchip: &FixedPointChip<F, PRECISION_BITS>) -> Vec<Vec<f64>> {
        let mut dq_matrix: Vec<Vec<f64>> = Vec::new();
        for i in 0..self.num_rows {
            dq_matrix.push(Vec::<f64>::new());
            for j in 0..self.num_col {
                let elem = self.matrix[i][j];
                dq_matrix[i].push(fpchip.dequantization(*elem.value()));
            }
        }
        return dq_matrix;
    }

    /// Prints the dequantized version of the matrix and returns it;
    ///
    /// Action is not constrained in anyway
    pub fn print(&self, fpchip: &FixedPointChip<F, PRECISION_BITS>) {
        print!("[\n");
        for i in 0..self.num_rows {
            print!("[\n");
            for j in 0..self.num_col {
                let elem = self.matrix[i][j];
                let elem = fpchip.dequantization(*elem.value());
                print!("{:?}, ", elem);
            }
            print!("], \n");
        }
        println!("]");
    }

    /// Takes quantised matrices `a` and `b`, their unscaled product `c_s`
    /// and a commitment (hash) to *at least* all of these matrices `init_rand`
    /// and checks if `a*b = c_s` in field multiplication.
    ///
    /// `c_s`: unscaled product of `a` and `b`(produced by simply multiplying `a` and `b` as field elements);
    ///  producing this is the costly part of matrix multiplication
    ///
    /// `init_rand`:  is the starting randomness/ challenge value; should commit to
    /// *at least* the matrices `a, b, c_s`
    pub fn verify_mul(
        ctx: &mut Context<F>,
        fpchip: &FixedPointChip<F, PRECISION_BITS>,
        a: &Self,
        b: &Self,
        c_s: &Vec<Vec<AssignedValue<F>>>,
        init_rand: &AssignedValue<F>,
    ) {
        assert_eq!(a.num_col, b.num_rows);
        assert_eq!(c_s.len(), a.num_rows);
        assert_eq!(c_s[0].len(), b.num_col);
        assert!(c_s[0].len() >= 1);

        let d = c_s[0].len();
        let gate = fpchip.gate();

        // v = (1, r, r^2, ..., r^(d-1)) where r = init_rand is the random challenge value
        let mut v: Vec<AssignedValue<F>> = Vec::new();

        let one = ctx.load_witness(F::one());
        gate.assert_is_const(ctx, &one, &F::one());
        v.push(one);

        for i in 1..d {
            let prev = &v[i - 1];
            let r_to_i = fpchip.gate().mul(ctx, *prev, *init_rand);
            v.push(r_to_i);
        }
        let v = v;

        // println!("Random vector, v = [");
        // for x in &v {
        //     println!("{:?}", *x.value());
        // }
        // println!("]");

        let cs_times_v = field_mat_vec_mul(ctx, gate, c_s, &v);
        let b_times_v = field_mat_vec_mul(ctx, gate, &b.matrix, &v);
        let ab_times_v = field_mat_vec_mul(ctx, gate, &a.matrix, &b_times_v);

        for i in 0..cs_times_v.len() {
            gate.is_equal(ctx, cs_times_v[i], ab_times_v[i]);
        }
    }

    /// Takes `c_s` and divides it by the quantization factor to scale it;
    ///
    /// Useful after matrix multiplication;
    ///
    /// Is costly- leads to ~94 (when lookup_bits =12) cells per element
    pub fn rescale_matrix(
        ctx: &mut Context<F>,
        fpchip: &FixedPointChip<F, PRECISION_BITS>,
        c_s: &Vec<Vec<AssignedValue<F>>>,
    ) -> Self {
        // #CONSTRAINTS = 94*N^2
        // now rescale c_s
        let mut c: Vec<Vec<AssignedValue<F>>> = Vec::new();
        let num_rows = c_s.len();
        let num_col = c_s[0].len();
        for i in 0..num_rows {
            let mut new_row: Vec<AssignedValue<F>> = Vec::new();
            for j in 0..num_col {
                // use fpchip to rescale c_s[i][j]
                // implemented in circuit, so we know c produced is correct
                let (elem, _) = fpchip.signed_div_scale(ctx, c_s[i][j]);
                new_row.push(elem);
            }
            c.push(new_row);
        }
        return Self { matrix: c, num_rows: num_rows, num_col: num_col };
    }
    /// hash all the matrices in the given list
    pub fn hash_matrix_list(
        ctx: &mut Context<F>,
        gate: &GateChip<F>,
        matrix_list: &Vec<Self>,
    ) -> AssignedValue<F> {
        // T, R_F, R_P values correspond to POSEIDON-128 values given in Table 2 of the Poseidon hash paper
        const T: usize = 3;
        const RATE: usize = 2;
        const R_F: usize = 8;
        const R_P: usize = 57;

        // MODE OF USE: we will update the poseidon chip with all the values and then extract one value
        let mut poseidon = PoseidonChip::<F, T, RATE>::new(ctx, R_F, R_P).unwrap();
        for mat in matrix_list {
            for row in &mat.matrix {
                poseidon.update(row);
            }
        }
        let init_rand = poseidon.squeeze(ctx, gate).unwrap();
        // dbg!(init_rand.value());
        return init_rand;
    }

    /// Outputs the transpose matrix of a matrix `a`;
    ///
    /// Doesn't create any new constraints; just outputs the a copy of the transposed Self.matrix
    pub fn transpose_matrix(a: &Self) -> Self {
        let mut a_trans: Vec<Vec<AssignedValue<F>>> = Vec::new();

        for i in 0..a.num_col {
            let mut new_row: Vec<AssignedValue<F>> = Vec::new();
            for j in 0..a.num_rows {
                new_row.push(a.matrix[j][i].clone());
            }
            a_trans.push(new_row);
        }
        return Self { matrix: a_trans, num_rows: a.num_col, num_col: a.num_rows };
    }
}

/// Constrains that `x` satisfies `|x| < bnd`, i.e., `x` is in the set `{-(bnd-1), -(bnd-2), ..., 0, 1, ..., (bnd-1)}`
///
/// Does so by checking that `x+(bnd-1) < 2*bnd - 1` as a range check
pub fn check_abs_less_than<F: BigPrimeField>(
    ctx: &mut Context<F>,
    range: &RangeChip<F>,
    x: AssignedValue<F>,
    bnd: &BigUint,
) {
    let new_bnd = BigUint::from(2u32) * bnd - BigUint::from(1u32);
    let translated_x =
        range.gate.add(ctx, x, Constant(biguint_to_fe(&(bnd - BigUint::from(1u32)))));
    range.check_big_less_than_safe(ctx, translated_x, new_bnd);
}

/// Takes as two matrices `a` and `b` as input and checks that `|a[i][j] - b[i][j]| < tol` for each `i,j`
/// according to the absolute value check in `check_abs_less_than`
///
/// Assumes matrix `a` and `b` are well defined matrices (all rows have the same size) and asserts (outside of circuit) that they can be compared
pub fn check_mat_diff<F: BigPrimeField>(
    ctx: &mut Context<F>,
    range: &RangeChip<F>,
    a: &Vec<Vec<AssignedValue<F>>>,
    b: &Vec<Vec<AssignedValue<F>>>,
    tol: &BigUint,
) {
    assert_eq!(a.len(), b.len());
    assert_eq!(a[0].len(), b[0].len());

    for i in 0..a.len() {
        for j in 0..a[0].len() {
            let diff = range.gate.sub(ctx, a[i][j], b[i][j]);
            check_abs_less_than(ctx, &range, diff, tol);
        }
    }
}

/// Given a matrix of field elements `a` and a field element `scalar_id`, checks that `|a[i][j] - scalar_id*Id[i][j]| < tol` for each `i,j`, where Id is the identity matrix
/// according to the absolute value check in `check_abs_less_than`
pub fn check_mat_id<F: BigPrimeField>(
    ctx: &mut Context<F>,
    range: &RangeChip<F>,
    a: &Vec<Vec<AssignedValue<F>>>,
    scalar_id: &AssignedValue<F>,
    tol: &BigUint,
) {
    let mut b: Vec<Vec<AssignedValue<F>>> = Vec::new();
    let zero = ctx.load_constant(F::zero());

    for i in 0..a.len() {
        let mut row: Vec<AssignedValue<F>> = Vec::new();
        for j in 0..a[0].len() {
            if i == j {
                row.push(scalar_id.clone())
            } else {
                row.push(zero.clone());
            }
        }
        b.push(row);
    }
    check_mat_diff(ctx, &range, a, &b, tol);
}

/// Given a matrix `a` in the fixed point representation, checks that all of its entries are less in absolute value than some bound `bnd`
///
/// Assumes matrix `a` is well formed (all rows have the same size)
///
/// COMMENT- for our specific use case- to make sure that unitaries are in (-1,1), it might be better to use range_check based checks
pub fn check_mat_entries_bounded<F: BigPrimeField>(
    ctx: &mut Context<F>,
    range: &RangeChip<F>,
    a: &Vec<Vec<AssignedValue<F>>>,
    bnd: &BigUint,
) {
    for i in 0..a.len() {
        for j in 0..a[0].len() {
            check_abs_less_than(ctx, &range, a[i][j], &bnd);
        }
    }
}

/// Takes matrices `a` and `b` (viewed simply as field elements), calculates and outputs matrix product `c = a*b` outside of the zk circuit
///
/// Assumes matrix `a` and `b` are well defined matrices (all rows have the same size) and asserts (outside of circuit) that they can be multiplied
///
/// Uses trivial O(N^3) matrix multiplication algorithm
///
/// Doesn't contrain output in any way
pub fn field_mat_mul<F: BigPrimeField>(
    a: &Vec<Vec<AssignedValue<F>>>,
    b: &Vec<Vec<AssignedValue<F>>>,
) -> Vec<Vec<F>> {
    // a.num_col == b.num_rows
    assert_eq!(a[0].len(), b.len());

    let mut c: Vec<Vec<F>> = Vec::new();
    #[allow(non_snake_case)]
    let N = a.len();
    #[allow(non_snake_case)]
    let K = a[0].len();
    #[allow(non_snake_case)]
    let M = b[0].len();

    for i in 0..N {
        let mut row: Vec<F> = Vec::new();
        for j in 0..M {
            let mut elem = F::zero();
            for k in 0..K {
                elem += a[i][k].value().clone() * b[k][j].value().clone();
            }
            row.push(elem);
        }
        c.push(row);
    }
    return c;
}

/// Takes matrices `a` and `b` (viewed simply as field elements), calculates matrix product `c_s = a*b` outside of the zk circuit, loads `c_s` into the context `ctx` and outputs the loaded matrix
///
/// Assumes matrix `a` and `b` are well defined matrices (all rows have the same size) and asserts (outside of circuit) that they can be multiplied
///
/// Uses trivial O(N^3) matrix multiplication algorithm
///
/// Doesn't contrain output matrix in any way
pub fn honest_prover_mat_mul<F: BigPrimeField>(
    ctx: &mut Context<F>,
    a: &Vec<Vec<AssignedValue<F>>>,
    b: &Vec<Vec<AssignedValue<F>>>,
) -> Vec<Vec<AssignedValue<F>>> {
    // field multiply matrices a and b
    // for honest prover creates the correct product multiplied by the quantization_scale (S) when a and b are field point quantized
    let c_s = field_mat_mul(a, b);
    let mut assigned_c_s: Vec<Vec<AssignedValue<F>>> = Vec::new();

    let num_rows = c_s.len();
    let num_col = c_s[0].len();
    for i in 0..num_rows {
        let mut new_row: Vec<AssignedValue<F>> = Vec::new();
        for j in 0..num_col {
            let elem = c_s[i][j];
            new_row.push(ctx.load_witness(elem));
        }
        assigned_c_s.push(new_row);
    }
    return assigned_c_s;
}

/// Multiplies matrix `a` to vector `v` in the zk-circuit and returns the constrained output `a.v`
/// -- all assuming `a` and `v` are field elements (and not fixed point encoded)
///
/// Assumes matrix `a` is well defined (rows are equal size) and asserts (outside circuit) `a` can be multiplied to `v`
pub fn field_mat_vec_mul<F: BigPrimeField>(
    ctx: &mut Context<F>,
    gate: &GateChip<F>,
    a: &Vec<Vec<AssignedValue<F>>>,
    v: &Vec<AssignedValue<F>>,
) -> Vec<AssignedValue<F>> {
    assert_eq!(a[0].len(), v.len());
    let mut y: Vec<AssignedValue<F>> = Vec::new();
    for row in a {
        let mut w: Vec<QuantumCell<F>> = Vec::new();
        for x in v {
            w.push(Existing(*x));
        }
        let w = w;

        let mut u: Vec<QuantumCell<F>> = Vec::new();
        for x in row {
            u.push(Existing(*x));
        }
        let u = u;

        y.push(gate.inner_product(ctx, u, w));
    }

    return y;
}

/// Multiplies matrix `a` by a diagonal matrix represented as a vector `v` in the zk-circuit and returns the constrained output `a*Diag(v)`
/// -- all assuming `a` and `v` are field elements, (and not fixed point encoded)
///
/// Assumes matrix `a` is well defined (rows are equal size)
///
/// If dimension of `a` is `N X K` and `v` is length `M`, then multiplication is carried out as long as `K >= M`
///
/// In case `K > M`, multiplication result is actually the `N X M` matrix given by `a*[Diag(v) 0]^T` where 0 is the `(M X (K-M))` matrix of all zeroes;
/// this choice allows us to handle one of the cases in the SVD check
pub fn mat_times_diag_mat<F: BigPrimeField>(
    ctx: &mut Context<F>,
    gate: &GateChip<F>,
    a: &Vec<Vec<AssignedValue<F>>>,
    v: &Vec<AssignedValue<F>>,
) -> Vec<Vec<AssignedValue<F>>> {
    assert!(v.len() <= a[0].len());
    let mut m: Vec<Vec<AssignedValue<F>>> = Vec::new();
    for i in 0..a.len() {
        let mut new_row: Vec<AssignedValue<F>> = Vec::new();
        for j in 0..v.len() {
            let prod = gate.mul(ctx, a[i][j], v[j]);
            new_row.push(prod);
        }
        m.push(new_row);
    }
    return m;
}
