module

public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic

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

/-- Theorem A as bound propagation. `landscape` is any summary of a smoothed
field. `hΛ` is a supplied Lipschitz bound in an auxiliary seminorm `lInf`;
`hEmb` is the supplied comparison of that seminorm with `lTwo`. Bottleneck
stability and landscape non-expansiveness are not proved: either one may be
used only to justify these hypotheses. -/
theorem summary_bound_propagation
    {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {Λ : Type} [AddCommGroup Λ]
    (P : E →L[ℝ] F) (landscape : F → Λ)
    (lInf lTwo : Λ → ℝ) (L μ : ℝ)
    (hL : 0 ≤ L) (hμ : 0 ≤ μ)
    (hΛ : ∀ u v, lInf (landscape u - landscape v) ≤ L * ‖u - v‖)
    (hEmb : ∀ w, lTwo w ≤ Real.sqrt μ * lInf w)
    (f g : E) :
    lTwo (landscape (P f) - landscape (P g))
      ≤ L * ‖P‖ * Real.sqrt μ * ‖f - g‖ := by
  sorry

/-- Theorem A for level-one periodic db2: the supplied summary inherits the
exact smoothing factor `(9/8)^d`. -/
theorem db2_summary_stability
    {Λ : Type} [AddCommGroup Λ]
    (N d : ℕ) [NeZero N] (hN : 7 ≤ N)
    (landscape : ((Fin d → ZMod N) → ℝ) → Λ)
    (lInf lTwo : Λ → ℝ) (L μ : ℝ)
    (hL : 0 ≤ L) (hμ : 0 ≤ μ)
    (hΛ : ∀ u v, lInf (landscape u - landscape v) ≤ L * ‖u - v‖)
    (hEmb : ∀ w, lTwo w ≤ Real.sqrt μ * lInf w)
    (f g : (Fin d → ZMod N) → ℝ) :
    lTwo (landscape (db2Operator N d f) - landscape (db2Operator N d g))
      ≤ L * ((9 : ℝ) / 8) ^ d * Real.sqrt μ * ‖f - g‖ := by
  sorry

/-- The exact db2 norm is the least constant that bounds the smoothing
operator. This is the sharp choice of `Cfp` in Lemma 3.2, not sharpness of a
landscape. -/
theorem db2_opNorm_least (N d : ℕ) [NeZero N] (hN : 7 ≤ N) {C : ℝ}
    (hC : ∀ f : (Fin d → ZMod N) → ℝ, ‖db2Operator N d f‖ ≤ C * ‖f‖) :
    ((9 : ℝ) / 8) ^ d ≤ C := by
  sorry

/-- Corollary 4.2 for a summary already measured in one norm. The hypothesis
is the Lipschitz bound of that summary, including the factor `L * sqrt μ`. -/
theorem db2_squared_summary_stability
    {S : Type} [NormedAddCommGroup S]
    (N d : ℕ) [NeZero N] (hN : 7 ≤ N)
    (landscape : ((Fin d → ZMod N) → ℝ) → S)
    (L μ : ℝ) (hL : 0 ≤ L) (hμ : 0 ≤ μ)
    (hΛ : ∀ u v, ‖landscape u - landscape v‖ ≤ L * Real.sqrt μ * ‖u - v‖)
    (f g : (Fin d → ZMod N) → ℝ) :
    |‖landscape (db2Operator N d f)‖ ^ 2 - ‖landscape (db2Operator N d g)‖ ^ 2|
      ≤ (L * ((9 : ℝ) / 8) ^ d * Real.sqrt μ * ‖f - g‖)
        * (‖landscape (db2Operator N d f)‖ + ‖landscape (db2Operator N d g)‖) := by
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

end
end TWSPeriodic
