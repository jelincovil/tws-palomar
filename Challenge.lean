module

public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Algebra.Monoid

@[expose] public section

/-!
# Exact sup-operator norms of finite periodic convolutions

The function-space norm is Mathlib's finite Pi sup norm. The operator is an
actual continuous linear map, not a name for a coefficient sum.
The corresponding proofs are in Solution.lean. Deliberate theorem holes
are confined to this Challenge; all definition bodies are explicit.
-/

open Finset Real
open scoped BigOperators
namespace TWSPeriodic
noncomputable section

/-- Real circular convolution on a finite additive commutative group.
The finite Pi norm on both function spaces is the maximum absolute value. -/
def convolutionOperator {G : Type} [Fintype G] [AddCommGroup G]
    (k : G → ℝ) : (G → ℝ) →L[ℝ] (G → ℝ) where
  toFun f x := ∑ y : G, k y * f (x - y)
  map_add' f g := by
    ext x
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c f := by
    ext x
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    ring
  cont := by fun_prop

/-- Push a finite signed stencil onto a finite group, adding all taps that
land at the same offset. Colliding opposite signs may cancel. -/
def foldKernel {I G : Type} [Fintype I] [DecidableEq G]
    (a : I → ℝ) (q : I → G) (x : G) : ℝ :=
  ∑ i : I, if q i = x then a i else 0

/-- Separable product kernel in `d` coordinates. -/
def tensorKernel {G : Type} (k : G → ℝ) (d : ℕ) (x : Fin d → G) : ℝ :=
  ∏ j : Fin d, k (x j)

/-- Orthonormal db2 normalization factor. -/
noncomputable def db2Scale : ℝ := 1 / (4 * sqrt 2)

/-- Orthonormal db2 low-pass coefficients, zero beyond the fourth tap. -/
noncomputable def db2Filter : ℕ → ℝ
  | 0 => db2Scale * (1 + sqrt 3)
  | 1 => db2Scale * (3 + sqrt 3)
  | 2 => db2Scale * (3 - sqrt 3)
  | 3 => db2Scale * (1 - sqrt 3)
  | _ => 0

/-- db2 autocorrelation at a nonnegative lag. -/
noncomputable def db2Autocorr (k : ℕ) : ℝ :=
  ∑ n ∈ range 4, db2Filter n * db2Filter (n + k)

/-- Level-one db2 approximation kernel, ordered at offsets -3,...,3.
These are the coefficients of one half of the db2 autocorrelation. -/
def db2Tap : Fin 7 → ℝ
  | ⟨0, _⟩ => -1 / 32
  | ⟨1, _⟩ => 0
  | ⟨2, _⟩ => 9 / 32
  | ⟨3, _⟩ => 16 / 32
  | ⟨4, _⟩ => 9 / 32
  | ⟨5, _⟩ => 0
  | ⟨6, _⟩ => -1 / 32

/-- Centered offsets in the cyclic group; this definition also handles
small periods, where distinct integer offsets can collide. -/
def db2Offset (N : ℕ) (i : Fin 7) : ZMod N := (i.val : ZMod N) - 3

/-- Actual periodization of the seven taps by addition in each residue class. -/
def db2Kernel (N : ℕ) : ZMod N → ℝ := foldKernel db2Tap (db2Offset N)

/-- Separable periodic level-one db2 operator on the `d`-dimensional torus.
`NeZero N` ensures that the cyclic group and function space are finite. -/
def db2Operator (N d : ℕ) [NeZero N] :
    ((Fin d → ZMod N) → ℝ) →L[ℝ] ((Fin d → ZMod N) → ℝ) :=
  convolutionOperator (tensorKernel (db2Kernel N) d)

/-- Radius of the undecimated db2 cascade at level `j`: `3 * (2^(j+1) - 1)`. -/
def cascadeRadius (j : ℕ) : ℕ := 3 * (2 ^ (j + 1) - 1)

/-- Number of integer taps of the free cascade kernel, including the zeros. -/
def cascadeSupport (j : ℕ) : ℕ := 2 * cascadeRadius j + 1

/-- Common denominator `2^(5*(j+1))` of the cascade coefficients. -/
def cascadeScale (j : ℕ) : ℕ := 2 ^ (5 * (j + 1))

/-- Integer numerator of the undecimated db2 cascade.
`cascadeInt j n` equals `k_j(n) * 2^(5*(j+1))`, where
`k_0 = [-1, 0, 9, 16, 9, 0, -1] / 32` and
`k_{j+1} = k_j ∗ (↑_{2^{j+1}} k_0)`. The step is the five-tap stencil
`16` at `0`, `9` at `±s` and `-1` at `±3s`, with `s = 2^(j+1)`. -/
def cascadeInt : ℕ → ℤ → ℤ
  | 0, n =>
      if n = 0 then 16
      else if Int.natAbs n = 1 then 9
      else if Int.natAbs n = 3 then -1
      else 0
  | j + 1, n =>
      let s : ℤ := 2 ^ (j + 1)
      16 * cascadeInt j n + 9 * cascadeInt j (n - s) + 9 * cascadeInt j (n + s)
        - cascadeInt j (n - 3 * s) - cascadeInt j (n + 3 * s)

/-- Real tap of the free cascade kernel, ordered on offsets `-R, ..., R`. -/
def cascadeTap (j : ℕ) (i : Fin (cascadeSupport j)) : ℝ :=
  ((cascadeInt j ((i.val : ℤ) - (cascadeRadius j : ℤ))) : ℝ) / (cascadeScale j : ℝ)

/-- Centered offsets of those taps in the cyclic group of period `N`. -/
def cascadeOffset (j N : ℕ) (i : Fin (cascadeSupport j)) : ZMod N :=
  (i.val : ZMod N) - (cascadeRadius j : ZMod N)

/-- Periodization of one cascade level. Distinct taps may collide when `N` is small. -/
def cascadeKernel (j N : ℕ) : ZMod N → ℝ :=
  foldKernel (cascadeTap j) (cascadeOffset j N)

/-- Separable periodic cascade operator at level `j` on the `d`-dimensional torus. -/
def cascadeOperator (j N d : ℕ) [NeZero N] :
    ((Fin d → ZMod N) → ℝ) →L[ℝ] ((Fin d → ZMod N) → ℝ) :=
  convolutionOperator (tensorKernel (cascadeKernel j N) d)

/-! ## Selected statements -/

/-- The induced sup norm of any real convolution on a finite abelian group
is exactly the l1 norm of its kernel. The lower bound uses a sign signal. -/
theorem convolution_opNorm {G : Type} [Fintype G] [AddCommGroup G]
    (k : G → ℝ) : ‖convolutionOperator k‖ = ∑ y : G, |k y| := by
  sorry

/-- A periodized finite stencil never has larger operator norm than its
unperiodized l1 mass. If offsets are injective, the bound is attained.
Injectivity is sufficient, not necessary: same-sign collisions can also
preserve l1 mass. -/
theorem periodization_norm {I G : Type} [Fintype I] [Fintype G]
    [AddCommGroup G] [DecidableEq G] (a : I → ℝ) (q : I → G) :
    ‖convolutionOperator (foldKernel a q)‖ ≤ ∑ i : I, |a i| ∧
    (Function.Injective q →
      ‖convolutionOperator (foldKernel a q)‖ = ∑ i : I, |a i|) := by
  sorry

/-- Exact dimension dependence for every separable real convolution. -/
theorem tensor_convolution_opNorm {G : Type} [Fintype G] [AddCommGroup G]
    (k : G → ℝ) (d : ℕ) :
    ‖convolutionOperator (tensorKernel k d)‖ = (∑ y : G, |k y|) ^ d := by
  sorry

/-- The seven rational taps really are half the autocorrelation of the
specified orthonormal db2 low-pass filter, at centered integer lags. -/
theorem db2_filter_identification (i : Fin 7) :
    db2Tap i = db2Autocorr (Int.natAbs ((i.val : ℤ) - 3)) / 2 := by
  sorry

/-- Paper Proposition 3.4, level one: the actual finite-grid operator norm,
for every positive period N >= 7 and every dimension d (including d=0). -/
theorem db2_opNorm (N d : ℕ) [NeZero N] (hN : 7 ≤ N) :
    ‖db2Operator N d‖ = ((9 : ℝ) / 8) ^ d := by
  sorry

/-- A unit-amplitude signal attains the exact db2 bound. This proves
sharpness of the smoothing operator, not of a downstream TDA pipeline. -/
theorem db2_attains (N d : ℕ) [NeZero N] (hN : 7 ≤ N) :
    ∃ f : (Fin d → ZMod N) → ℝ,
      ‖f‖ = 1 ∧ ‖db2Operator N d f‖ = ((9 : ℝ) / 8) ^ d := by
  sorry

/-- The explicit deterministic perturbation bound for the smoothing map. -/
theorem db2_lipschitz (N d : ℕ) [NeZero N] (hN : 7 ≤ N)
    (f g : (Fin d → ZMod N) → ℝ) :
    ‖db2Operator N d f - db2Operator N d g‖ ≤ ((9 : ℝ) / 8) ^ d * ‖f - g‖ := by
  sorry

/-- The exact db2 norm is the least constant that bounds the smoothing
operator. This is the sharp choice of `Cfp` in Lemma 3.2, not sharpness of a
landscape. -/
theorem db2_opNorm_least (N d : ℕ) [NeZero N] (hN : 7 ≤ N) {C : ℝ}
    (hC : ∀ f : (Fin d → ZMod N) → ℝ, ‖db2Operator N d f‖ ≤ C * ‖f‖) :
    ((9 : ℝ) / 8) ^ d ≤ C := by
  sorry

/-- Exact operator norm of undecimated db2 cascade level one.
The free kernel has nineteen taps, zeros included, and l1 mass `299/256`.
For every period `N >= 19` the centered offsets do not collide, so this is
the periodic operator norm in every dimension, including `d = 0`. Squaring
at `d = 2` gives `89401/65536`. This is one finite level, not a closed form
for every level. -/
theorem cascade_level1_opNorm (N d : ℕ) [NeZero N] (hN : 19 ≤ N) :
    ‖cascadeOperator 1 N d‖ = ((299 : ℝ) / 256) ^ d := by
  sorry

/-- Exact operator norm of cascade level two: `9663/8192`, for every
`N >= 43` and every dimension. The two-dimensional square is
`93373569/67108864`. -/
theorem cascade_level2_opNorm (N d : ℕ) [NeZero N] (hN : 43 ≤ N) :
    ‖cascadeOperator 2 N d‖ = ((9663 : ℝ) / 8192) ^ d := by
  sorry

/-- Exact operator norm of cascade level three: `309991/262144`, for every
`N >= 91` and every dimension. The two-dimensional square is
`96094420081/68719476736`. -/
theorem cascade_level3_opNorm (N d : ℕ) [NeZero N] (hN : 91 ≤ N) :
    ‖cascadeOperator 3 N d‖ = ((309991 : ℝ) / 262144) ^ d := by
  sorry

/-- Exact ℓ¹ mass of the periodized kernel when `N` is at least the support.
That hypothesis is a sufficient no-collision condition. The free mass, which
does not depend on `N`, equals the same expression. -/
theorem cascade_l1_formula (j N : ℕ) [NeZero N] (hN : cascadeSupport j ≤ N) :
    (∑ x : ZMod N, |cascadeKernel j N x|) =
      (1651 : ℝ) / 1395 - ((4 : ℝ) / 63) * ((1 : ℝ) / 4) ^ j
        + ((1 : ℝ) / 180) * ((1 : ℝ) / 16) ^ j
        - ((1 : ℝ) / 1736) * ((1 : ℝ) / 32) ^ j := by
  sorry

/-- Exact operator norm of every cascade level when the period is at least the
support: `‖C_{j,N,d}‖ = c_j^d`, including `d = 0`. -/
theorem cascade_opNorm_formula (j N d : ℕ) [NeZero N]
    (hN : cascadeSupport j ≤ N) :
    ‖cascadeOperator j N d‖ =
      ((1651 : ℝ) / 1395 - ((4 : ℝ) / 63) * ((1 : ℝ) / 4) ^ j
        + ((1 : ℝ) / 180) * ((1 : ℝ) / 16) ^ j
        - ((1 : ℝ) / 1736) * ((1 : ℝ) / 32) ^ j) ^ d := by
  sorry

/-- Uniform bound for every positive period, including periods shorter than
the support. Aliasing cannot increase the norm. `L = 1651/1395`. At `d = 0`
the right-hand side is 1. This includes `N = 1`. -/
theorem cascade_opNorm_uniform (j N d : ℕ) [NeZero N] :
    ‖cascadeOperator j N d‖ ≤ ((1651 : ℝ) / 1395) ^ d := by
  sorry

/-- Explicit rate: the free mass stays strictly below `1651/1395` and the gap
is at most `(4/63) 4^{-j}`. -/
theorem cascade_l1_gap (j : ℕ) :
    0 < (1651 : ℝ) / 1395 - (∑ i : Fin (cascadeSupport j), |cascadeTap j i|) ∧
      (1651 : ℝ) / 1395 - (∑ i : Fin (cascadeSupport j), |cascadeTap j i|)
        ≤ ((4 : ℝ) / 63) * ((1 : ℝ) / 4) ^ j := by
  sorry

/-- The free ℓ¹ mass is strictly increasing in the level. -/
theorem cascade_l1_succ_lt (j : ℕ) :
    (∑ i : Fin (cascadeSupport j), |cascadeTap j i|) <
      ∑ i : Fin (cascadeSupport (j + 1)), |cascadeTap (j + 1) i| := by
  sorry

/-- The free ℓ¹ mass converges to `1651/1395`. -/
theorem cascade_l1_tendsto :
    Filter.Tendsto (fun j : ℕ => ∑ i : Fin (cascadeSupport j), |cascadeTap j i|)
      Filter.atTop (nhds ((1651 : ℝ) / 1395)) := by
  sorry

/-- `1651/1395` raised to `d` is the least constant that bounds every level
and every positive period at once. A fixed period is not claimed to attain it.
At `d = 0` the conclusion is `1 ≤ B`. It does not force `B = 1`. -/
theorem cascade_uniform_constant_least (d : ℕ) {B : ℝ}
    (hB : ∀ j N : ℕ, (hN : NeZero N) → ‖cascadeOperator j N d‖ ≤ B) :
    ((1651 : ℝ) / 1395) ^ d ≤ B := by
  sorry

/-- Dimension zero is exactly the identity, for every level and every positive
period, including periods that alias. -/
theorem cascade_opNorm_d_zero (j N : ℕ) [NeZero N] :
    ‖cascadeOperator j N 0‖ = 1 := by
  sorry

end
end TWSPeriodic
