# The undecimated db2 cascade: exact mass and optimal uniform norm

This note explains the argument that is actually formalized in `Solution.lean`.
It is the exposition of the current development. The historical manuscript
snapshot remains `docs/manuscript-source.pdf`; that file is not rewritten here,
and it does not contain the closed form below. Names in `code` are Lean
declarations in the namespace `TWSPeriodic`.

The indexed level `j = 0` is already one smoothing stage. It is the seven-tap
kernel, not the unfiltered identity.

## 1. Definitions

### 1.1. The initial mask

The orthonormal Daubechies low-pass filter of length 4 is

```
h = c · (1 + √3,  3 + √3,  3 − √3,  1 − √3),    c = 1 / (4 √2),
```

and `h_k = 0` outside `{0, 1, 2, 3}`. The scale is chosen so that
`h_0² + h_1² + h_2² + h_3² = 1` (`db2Filter`, `db2Scale`, `R0`). Its
autocorrelation `R(k) = ∑_i h_i h_{i+k}` takes the values

```
R(0) = 1,   R(1) = 9/16,   R(2) = 0,   R(3) = −1/16
```

(`db2Autocorr`, `autocorr_zero` through `autocorr_three`). One half of the
symmetric autocorrelation is the initial real kernel `k_0`, supported on
`{-3, …, 3}`:

```
k_0 = [−1,  0,  9,  16,  9,  0,  −1] / 32.
```

The signed sum of these seven taps is `1`. Their absolute sum is `36/32 = 9/8`
(`db2Tap`, `db2_filter_identification`, `db2Tap_l1`).

### 1.2. Integer coefficients and the real kernel

Clear the denominator by setting `A_j(n) = k_j(n) · 2^{5(j+1)}`. The scale
`2^{5(j+1)} = 32^{j+1}` is `cascadeScale j`. The integer sequence is
`cascadeInt`:

```
A_0(0) = 16,   A_0(±1) = 9,   A_0(±3) = −1,
```

and `A_0(n) = 0` otherwise. With step `s = 2^{j+1}`,

```
A_{j+1}(n) = 16 A_j(n) + 9 A_j(n − s) + 9 A_j(n + s)
             − A_j(n − 3s) − A_j(n + 3s).
```

This is the numerator form of convolution against the dyadically upsampled
copy of `k_0`. Each step multiplies the common denominator by `32`. The real
tap on the centered window is

```
k_j(i − R_j) = A_j(i − R_j) / 32^{j+1},    i = 0, …, S_j − 1
```

(`cascadeTap`).

### 1.3. Support, symmetry, and parity

The radius and the number of taps, including the structural zeros, are

```
R_j = 3 (2^{j+1} − 1),    S_j = 2 R_j + 1 = 6 · 2^{j+1} − 5
```

(`cascadeRadius`, `cascadeSupport`). Thus `S_0 = 7`, `S_1 = 19`, `S_2 = 43`,
and `S_3 = 91`. Outside this window the integer sequence vanishes
(`cascadeInt_vanish`). It is even: `A_j(−n) = A_j(n)` (`cascadeInt_symm`).

The five-tap step splits into an even rule and an odd rule
(`cascadeInt_even`, `cascadeInt_odd`):

```
A_{j+1}(2t)     = 16 A_j(t),
A_{j+1}(2t+1)   = −A_j(t−1) + 9 A_j(t) + 9 A_j(t+1) − A_j(t+2).
```

Two further vanishing identities are used as boundary anchors.
`A_j(2^{j+1}) = 0` and `A_j(2^{j+2}) = 0` (`cascadeInt_dyadic`,
`cascadeInt_four`). The origin is a pure power, `A_j(0) = 16^{j+1}`
(`cascadeInt_origin`).

### 1.4. Periodization and the operator

On the cyclic group `ℤ/Nℤ`, the centered offsets are `i − R_j` modulo `N`
(`cascadeOffset`). The periodized kernel is the sum of every tap that lands
on the same point (`foldKernel`, `cascadeKernel`). Distinct taps may cancel
or reinforce each other when `N < S_j`. If the offsets are injective, each
fiber has at most one tap.

The operator `C_{j,N,d}` is convolution, on `(ℤ/Nℤ)^d`, by the `d`-fold
tensor product of that kernel (`tensorKernel`, `cascadeOperator`). Both
function spaces carry the supremum norm, and the operator norm is Mathlib's
norm on continuous linear maps. For `d = 0` the domain is a one-point set
and the empty tensor product is the unit kernel.

The **free mass** does not depend on `N`:

```
m_j = ∑_{i < S_j} |k_j(i − R_j)|.
```

The **periodized mass** does:

```
μ_{j,N} = ∑_{x ∈ ℤ/Nℤ} |k_{j,N}(x)|.
```

Folding never increases the mass, so `μ_{j,N} ≤ m_j` for every `N ≥ 1`.
Equality holds when the offsets are injective. The condition `N ≥ S_j` is a
sufficient reason for injectivity (`cascadeOffset_injective`). It is not
claimed to be necessary: taps of equal sign can collide without lowering
the mass.

## 2. The theorem

Let `L = 1651/1395` and

```
c_j = L − (4/63) 4^{−j} + (1/180) 16^{−j} − (1/1736) 32^{−j}.
```

**Free mass.** For every natural number `j`, with no hypothesis on a period,

```
m_j = c_j.
```

**Norm without aliasing.** For every `j`, every dimension `d`, and every
period `N ≥ S_j`,

```
‖C_{j,N,d}‖_{∞→∞} = c_j^d.
```

**Uniform bound.** For every `j`, every `d`, and every period `N ≥ 1`,
aliasing included,

```
‖C_{j,N,d}‖_{∞→∞} ≤ L^d.
```

**Least such constant.** If a real number `B` satisfies
`‖C_{j,N,d}‖ ≤ B` for every level `j` and every period `N ≥ 1`, then
`L^d ≤ B`. The periods used to force this inequality may grow with `j`.
The statement does not say that one fixed `N` attains `L^d`. At `d = 0`
the conclusion is `1 ≤ B`. It does not force `B = 1`.

**Monotonicity, limit, and rate.** The free masses satisfy `m_j < m_{j+1}`,
`m_j → L`, and

```
0 < L − m_j ≤ (4/63) 4^{−j}.
```

**Dimension zero, separately.** For every `j` and every `N ≥ 1`,
`‖C_{j,N,0}‖ = 1`. This is the empty-product identity. It is not deduced
by specializing the least-constant inequality.

At `j = 0` one has `c_0 = 9/8` and `S_0 = 7`, which is the level-one db2
norm. The same formula reproduces the previously selected finite levels:
`c_1 = 299/256`, `c_2 = 9663/8192`, and `c_3 = 309991/262144`.

## 3. The argument

### 3.1. Why a signed identity is not enough

The triangle inequality, applied to `j+1` convolutions with a kernel of
mass `9/8`, yields only `m_j ≤ (9/8)^{j+1}`. The signed sum of `A_j` equals
`32^{j+1}`, because the real kernel has signed sum `1`. That identity fixes
the center of the Fourier symbol. It does not fix `∑ |A_j(n)|`. The proof
therefore has to determine the sign of every tap, including the taps created
at the junctions between dyadic blocks.

### 3.2. Positive center, with a ratio cone

Write `δ_j(k) = A_j(k) − A_j(k+1)` (`cDiff`). On the center block
`0 ≤ k < 2^{j+1}`, the sequence `A_j(k)` is strictly positive. The inductive
carrier is the predicate `CenterOK j`: every consecutive difference in that
block is positive, and consecutive differences have ratios in the interval
`[1/3, 3]`.

The even and odd rules turn three consecutive differences into the
differences of the next level (`cDiff_even`, `cDiff_odd`). The linear forms

```
a + 8b − c,    −a + 8b + c
```

stay positive and stay inside the same ratio interval whenever `(a, b, c)`
does (`diffCone_step`, `diffCone_cross`). Those cones cover the interior.
The two endpoints of the block are not interior points. They are expressed
through the edge samples

```
P_j = A_j(2^{j+1} − 2),   Q_j = A_j(2^{j+1} − 1),
F_j = −A_j(2^{j+1} + 1),  G_j = −A_j(2^{j+1} + 2)
```

(`edgeP`, `edgeQ`, `edgeF`, `edgeG`). The five-tap step gives a linear
recurrence for this four-tuple (`edgeP_succ`, `edgeQ_succ`, `edgeF_succ`,
`edgeG_succ`). Solving it produces the closed forms in `edge_formula`; the
only combination needed later is

```
3 (Q_j + F_j) = 32 · 8^j − 2 · 2^j
```

(`edge_sum_formula`). Positivity of `Q_j` and `F_j`, and the ratio
inequalities at the junction, reduce to comparisons of the shape
`6j + 13 ≤ 16 · 2^j` (`edgeQ_pos`, `edgeF_pos`, `edge_order`,
`two_pow_ge_linear`). The cases `j = 0` and `j = 1` are finite and are
decided directly (`centerOK_zero`, `centerOK_one`). From `j ≥ 1` the cone
passes to the next level (`centerOK_succ`), so `CenterOK` holds for every
`j` (`centerOK_all`).

Positivity of the samples themselves is then a walk back from the last
center sample. That sample equals `Q_j > 0`, and every preceding difference
is positive (`cascadeInt_center_pos`).

### 3.3. Negative first side, and the copied tail

On the next block, `A_j(2^{j+1} + k) ≤ 0` for `0 ≤ k < 2^{j+1}`. The
endpoint `k = 0` is the dyadic zero. For `1 ≤ k < 2^{j+1}` the value is
strictly negative. The carrier is `SideOK j`: those absolute values are
positive, and consecutive absolute values have ratios in `[1/2, 5/2]`
(`sideAbs`).

Even samples of the next side are sixteen times the previous side
(`sideAbs_even`). An interior odd sample is the four-point form
`−a + 9b + 9c − d`. Whenever the previous absolute values lie in the ratio
interval, this form stays positive and the new ratios stay in `[1/2, 5/2]`
(`sideStencil`, `side_new_interior`). The first two odd places use the edge
tuple `(Q, F, G, H)` (`side_new_head`, `side_new_third`). The last places
use the dyadic zero together with one further identity: once the index is
at least `4 · 2^{j+1} − 2`, four of the five taps in the recurrence land
outside the support of `A_j`, and

```
A_{j+1}(n) = −A_j(n − 3 · 2^{j+1})
```

(`cascadeInt_tail`). The far side of level `j+1` is therefore a signed copy
of a side of level `j`. This copy is available only for `j ≥ 1`, which is
why the side recurrence below starts at that threshold. The side predicate
is decided at `j = 0, 1, 2` and then inducts for every later level
(`sideOK_zero`, `sideOK_one`, `sideOK_two`, `sideOK_succ`, `sideOK_all`).
The sign statement used for absolute values is `side_nonpos`.

A uniform claim that every side ratio is at most `2` is false, and the
proof does not make it. The cone that is preserved is `[1/2, 5/2]`.

### 3.4. Decomposition of the absolute mass

Because the center block is positive,

```
∑_{k < 2^{j+1}} A_j(k) = ∑_{k < 2^{j+1}} |A_j(k)|
```

(`centerSum`, `oneAbs_center`). Because the first side is nonpositive,
the corresponding absolute sum equals `−∑ A_j(2^{j+1} + k)` (`sideSum`,
`sideMass`, `oneAbs_side`). Let `oneAbs j` be the absolute sum of `A_j`
from `0` through `R_j`. For `j ≥ 1` the tail past `2^{j+2}` reproduces the
previous level's side beyond its center, and

```
oneAbs j = centerSum j + sideMass j + oneAbs(j−1) − centerSum(j−1)
```

(`oneAbs_decompose`). Symmetry identifies the negative half with the
positive half, up to the center sample, which must not be counted twice:

```
absMass j = 2 · oneAbs j − A_j(0)
```

(`absMass`, `oneAbs_reflect`, `absMass_fin`). Unfolding the recurrence
gives the global decomposition actually summed:

```
absMass j = centerFull j + 2 ∑_{i=0}^{j} sideMass i,
```

where `centerFull j = 2 · centerSum j − A_j(0)` (`absMass_signed`,
`centerFull`). The free real mass is this integer divided by the scale
(`free_l1`, `absMass_real`).

### 3.5. Recurrences for the block sums

Split a dyadic range into even and odd indices (`sum_range_even_odd`) and
apply the parity rules. Shifting a complete range of a function on `ℤ` only
changes the endpoints (`sum_shift_pred`, `sum_shift_succ`,
`sum_shift_add_two`). The endpoint contributions are exactly the edge
samples already computed. The result is

```
centerSum(j+1) = 32 · centerSum j − 8 A_j(0) + Q_j + F_j,
```

and therefore

```
centerFull(j+1) = 32 · centerFull j + 2 (Q_j + F_j)
```

(`centerSum_succ`, `centerFull_succ`). For the side, and only for `j ≥ 1`,

```
sideSum(j+1) = 32 · sideSum j − e_j − e_{j−1},
e_j = Q_j + F_j,
```

(`sideSum_succ`). The two initial side sums are finite: `sideSum 0 = −1`
and `sideSum 1 = −43`. Substituting `3 e_j = 32 · 8^j − 2 · 2^j` and
inducting gives the closed block formulae

```
45 · centerFull j = 1568 · 32^j − 40 · 8^j + 2 · 2^j,
30 · sideMass j   = 44 · 32^j − 15 · 8^j + 2^j
```

(`centerFull_formula`, `sideMass_formula`).

### 3.6. The closed form

Sum the side formula over `i = 0, …, j` (`sideMassSum_closed`). Each sum is
geometric (`geom_sum_mul`):

```
∑_{i=0}^{j} 32^i = (32^{j+1} − 1) / 31,
```

and likewise for `8` and `2`. The integer combination

```
9765 · (centerFull j + 2 ∑ sideMass i)
  = 217 · (45 · centerFull j) + 651 · (30 · ∑ sideMass i)
```

matches the two cleared formulae, because `217 · 45 = 9765` and
`651 · 30 = 2 · 9765`. After the geometric sums are inserted, polynomial
arithmetic leaves

```
9765 · absMass j = 4 (92456 · 32^j − 4960 · 8^j + 434 · 2^j − 45)
```

(`absMass_closed`). Divide by the scale `2^{5(j+1)} = 4 · 2^{5j+3}`. The
factor `4` cancels, and

```
m_j = P_j / (9765 · 2^{5j+3}),
P_j = 92456 · 32^j − 4960 · 8^j + 434 · 2^j − 45
```

(`absMass_real`, `cascade_l1_ratio`). The constant term of this expression
is

```
92456 / (9765 · 8) = 11557 / 9765 = 1651 / 1395 = L.
```

The difference is

```
L − m_j = (4960 · 8^j − 434 · 2^j + 45) / (9765 · 2^{5j+3})
```

(`cascade_l1_gap_formula`). Rewriting the powers of two as powers of
`1/4`, `1/16`, and `1/32` turns the right-hand side into

```
(4/63) 4^{−j} − (1/180) 16^{−j} + (1/1736) 32^{−j}
```

(`cascade_gap_series`). Therefore `m_j = c_j` (`cascade_l1_series`). The
leading coefficients agree because `63 · 4960 = 32 · 9765`. The numerator
of the gap is positive because `2^j ≤ 8^j` gives

```
4960 · 8^j − 434 · 2^j + 45 ≥ 4526 · 8^j + 45 > 0
```

(`cascade_gap_num_pos`). Dropping the two smaller terms of the series, and
using `(1/1736) 32^{−j} ≤ (1/180) 16^{−j}`, yields the rate

```
0 < L − m_j ≤ (4/63) 4^{−j}
```

(`absMass_gap`).

### 3.7. Increase and convergence

The same gap formula at `j` and at `j+1` reduces `m_j < m_{j+1}` to a
comparison of numerators. The denominator grows by exactly `32`. After the
powers are expanded,

```
32 · num_j − num_{j+1} = 119040 · 8^j − 13020 · 2^j + 1395,
```

and `2^j ≤ 8^j` lowers the right-hand side to `106020 · 8^j + 1395 > 0`
(`absMass_succ_lt`). Thus the gap itself decreases, and the free mass
increases.

For the limit, `0 ≤ 1/4 < 1`, and likewise for `1/16` and `1/32`, so each
geometric term tends to zero. The four-term expression tends to `L`, and
`m_j` tends to `L` with it (`absMass_tendsto`).

### 3.8. From the free mass to the periodic norm

On any finite abelian group, convolution by a kernel `k` has supremum
operator norm equal to `∑ |k|`. The upper bound is the triangle inequality.
The matching lower bound is the explicit sign signal
`f(x) = 1` when `k(−x) ≥ 0` and `f(x) = −1` otherwise: it has unit supremum
norm, and `(C_k f)(0) = ∑ |k|` (`convolution_opNorm`, `signSignal`).

Folding sums colliding coefficients before the absolute value is taken, so
the periodized mass is at most the free mass. Injective offsets give
equality (`foldKernel_l1_le`, `foldKernel_l1_eq`, `periodization_norm`).
The centered cascade offsets are injective whenever `N ≥ S_j`. Combined
with `m_j = c_j`, this is the exact periodized mass, and it is the
statement selected as `cascade_l1_formula`. The identity `m_j = c_j` itself
does not mention `N`; it is `cascade_l1_series`, reached from the free sum
by `free_l1`.

For a separable kernel `K(x_1, …, x_d) = ∏_{t<d} k(x_t)`,

```
∑ |K| = (∑ |k|)^d,
```

including `d = 0`, where both sides equal `1` (`tensorKernel_l1`,
`tensor_convolution_opNorm`). Therefore, whenever `N ≥ S_j`,

```
‖C_{j,N,d}‖ = c_j^d
```

(`cascade_opNorm_formula`). For an arbitrary positive period the folded
mass is at most `m_j`, and `m_j < L`, so

```
‖C_{j,N,d}‖ ≤ m_j^d ≤ L^d
```

(`cascade_opNorm_uniform`). The inequality includes `N = 1`. It does not
assert that the positive-dimensional period-one norm equals `1`. That
separate identity is not a selected theorem.

### 3.9. The least constant

Fix `d`, and suppose `B` bounds the operator at every level and every
positive period. Choose the period `N_j = S_j`, which is positive and grows
with `j`. There is then no aliasing, and the norm equals `m_j^d`. The
hypothesis supplies `m_j^d ≤ B` for every `j`. The map `t ↦ t^d` is
continuous and `m_j → L`, so `m_j^d → L^d`. A number that lies above every
term of a convergent sequence lies above the limit (`cascade_uniform_constant_least`).
Hence `L^d ≤ B`.

At `d = 0` the same sentence says `1 ≤ B`. Each individual zero-dimensional
norm is nevertheless equal to `1`, for every period, because the operator
norm is `m^0 = 1` after tensorization (`cascade_opNorm_d_zero`). An upper
bound `B` of a family of ones may be strictly larger than `1`. The
least-constant theorem records the inequality `1 ≤ B` and stops there.

## 4. What the bound improves, and what it does not say

Comparing one stage at a time gives `m_j ≤ (9/8)^{j+1}`, since level `j`
is a convolution of `j+1` copies of a kernel of mass `9/8` and the triangle
inequality does not see cancellation between positive and negative taps.
Already at level `1` this product is `(9/8)^2 = 81/64`, while the exact
mass is `299/256`. The product grows without bound as `j` increases. The
exact mass increases, but it remains below the finite limit `L ≈ 1.1835`.
The sign analysis is what replaces the product bound by this limit. The
comparison is elementary once the exact mass is known. It does not, by
itself, show that the formula is absent from the literature. That question
is recorded in `docs/RELATED_WORK.md`.

The constant `L^d` is optimal for the family of smoothing operators
`C_{j,N,d}` as `j` and `N` vary. It is not an optimality statement about a
nonlinear summary applied after smoothing. The summary bounds elsewhere in
the development assume a Lipschitz bound and a seminorm comparison. They
do not prove bottleneck stability of persistence diagrams, and they do not
prove that a persistence landscape is non-expansive.

The manuscript equation that printed the rounded two-dimensional values
`1.364151`, `1.391375`, and `1.398358` is the specialization `d = 2` at
levels `1`, `2`, and `3`. Those three exact squares are
`89401/65536`, `93373569/67108864`, and `96094420081/68719476736`.

## 5. Selected statements and the lemmas under them

The eight selected cascade-formula statements are the public face of the
argument above. The sign cones, the block recurrences, and `absMass_closed`
are lemmas in `Solution.lean`. They are not separate entries in
`comparator.json`.

| Selected statement | What it asserts | Principal lemmas |
|---|---|---|
| `cascade_l1_formula` | `μ_{j,N} = c_j` whenever `N ≥ S_j` | `cascade_l1_all`, `cascade_l1_series` |
| `cascade_opNorm_formula` | `‖C_{j,N,d}‖ = c_j^d` whenever `N ≥ S_j` | `cascade_opNorm_all`, `cascade_l1_series` |
| `cascade_opNorm_uniform` | `‖C_{j,N,d}‖ ≤ L^d` for every `N ≥ 1` | `cascade_opNorm_le_level`, `absMass_gap` |
| `cascade_l1_gap` | `0 < L − m_j ≤ (4/63) 4^{−j}` | `free_l1`, `absMass_gap` |
| `cascade_l1_succ_lt` | `m_j < m_{j+1}` | `free_l1`, `absMass_succ_lt` |
| `cascade_l1_tendsto` | `m_j → L` | `free_l1`, `absMass_tendsto` |
| `cascade_uniform_constant_least` | every common bound is at least `L^d` | `cascade_opNorm_all`, `absMass_tendsto` |
| `cascade_opNorm_d_zero` | `‖C_{j,N,0}‖ = 1` for every `N ≥ 1` | `tensor_convolution_opNorm` |

The finite levels `cascade_level1_opNorm`, `cascade_level2_opNorm`, and
`cascade_level3_opNorm` predate the closed form. They evaluate the integer
masses `1196`, `38652`, and `1239964` at scales `1024`, `32768`, and
`1048576`. They agree with `c_1`, `c_2`, and `c_3`, and they remain
selected.
