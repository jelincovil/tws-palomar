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
actual continuous linear map, not a name for a coefficient sum. All new
proofs are in this file; no theorem from the legacy TWS skeleton is imported.
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

/-! ## General convolution and its maximizing sign signal -/

@[simp] theorem convolutionOperator_apply {G : Type} [Fintype G] [AddCommGroup G]
    (k f : G → ℝ) (x : G) :
    convolutionOperator k f x = ∑ y : G, k y * f (x - y) := rfl

theorem convolution_bound {G : Type} [Fintype G] [AddCommGroup G]
    (k f : G → ℝ) :
    ‖convolutionOperator k f‖ ≤ (∑ y : G, |k y|) * ‖f‖ := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).2
  intro x
  calc
    ‖convolutionOperator k f x‖ ≤ ∑ y : G, ‖k y * f (x - y)‖ :=
      norm_sum_le _ _
    _ = ∑ y : G, |k y| * ‖f (x - y)‖ := by
      simp only [norm_mul, Real.norm_eq_abs]
    _ ≤ ∑ y : G, |k y| * ‖f‖ := by
      apply Finset.sum_le_sum
      intro y _
      exact mul_le_mul_of_nonneg_left (norm_le_pi_norm f (x - y)) (abs_nonneg _)
    _ = (∑ y : G, |k y|) * ‖f‖ := (Finset.sum_mul _ _ _).symm

/-- A sign signal reflected about zero; zero coefficients are assigned +1. -/
def signSignal {G : Type} [Neg G] (k : G → ℝ) (x : G) : ℝ :=
  if 0 ≤ k (-x) then 1 else -1

theorem signSignal_norm {G : Type} [Fintype G] [AddCommGroup G]
    (k : G → ℝ) : ‖signSignal k‖ = 1 := by
  have hpoint (x : G) : ‖signSignal k x‖ = 1 := by
    unfold signSignal
    split_ifs <;> norm_num
  apply le_antisymm
  · exact (pi_norm_le_iff_of_nonneg (by norm_num)).2 fun x => (hpoint x).le
  · calc
      (1 : ℝ) = ‖signSignal k (0 : G)‖ := (hpoint 0).symm
      _ ≤ ‖signSignal k‖ := norm_le_pi_norm _ _

theorem convolution_signSignal_zero {G : Type} [Fintype G] [AddCommGroup G]
    (k : G → ℝ) : convolutionOperator k (signSignal k) 0 = ∑ y : G, |k y| := by
  rw [convolutionOperator_apply]
  apply Finset.sum_congr rfl
  intro y _
  simp only [zero_sub, signSignal, neg_neg]
  split_ifs with hy
  · simp [abs_of_nonneg hy]
  · simp [abs_of_neg (lt_of_not_ge hy)]

/-- The induced sup norm of any real convolution on a finite abelian group
is exactly the l1 norm of its kernel. The lower bound uses a sign signal. -/
theorem convolution_opNorm {G : Type} [Fintype G] [AddCommGroup G]
    (k : G → ℝ) : ‖convolutionOperator k‖ = ∑ y : G, |k y| := by
  apply le_antisymm
  · exact (convolutionOperator k).opNorm_le_bound
      (Finset.sum_nonneg fun y _ => abs_nonneg (k y)) (convolution_bound k)
  · calc
      (∑ y : G, |k y|) = ‖convolutionOperator k (signSignal k) 0‖ := by
        rw [convolution_signSignal_zero, Real.norm_eq_abs,
          abs_of_nonneg (Finset.sum_nonneg fun y _ => abs_nonneg (k y))]
      _ ≤ ‖convolutionOperator k (signSignal k)‖ := norm_le_pi_norm _ _
      _ ≤ ‖convolutionOperator k‖ :=
        (convolutionOperator k).unit_le_opNorm (signSignal k) (signSignal_norm k).le

theorem convolution_attains {G : Type} [Fintype G] [AddCommGroup G]
    (k : G → ℝ) :
    ∃ f : G → ℝ, ‖f‖ = 1 ∧ ‖convolutionOperator k f‖ = ‖convolutionOperator k‖ := by
  refine ⟨signSignal k, signSignal_norm k, le_antisymm ?_ ?_⟩
  · exact (convolutionOperator k).unit_le_opNorm (signSignal k) (signSignal_norm k).le
  · calc
      ‖convolutionOperator k‖ = ∑ y : G, |k y| := convolution_opNorm k
      _ = ‖convolutionOperator k (signSignal k) 0‖ := by
        rw [convolution_signSignal_zero, Real.norm_eq_abs,
          abs_of_nonneg (Finset.sum_nonneg fun y _ => abs_nonneg (k y))]
      _ ≤ ‖convolutionOperator k (signSignal k)‖ := norm_le_pi_norm _ _

/-! ## Periodization: a universal bound, and exactness without collisions -/

theorem foldKernel_l1_le {I G : Type} [Fintype I] [Fintype G] [DecidableEq G]
    (a : I → ℝ) (q : I → G) :
    (∑ x : G, |foldKernel a q x|) ≤ ∑ i : I, |a i| := by
  classical
  calc
    (∑ x : G, |foldKernel a q x|) ≤
        ∑ x : G, ∑ i : I, |if q i = x then a i else 0| := by
      apply Finset.sum_le_sum
      intro x _
      exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i : I, ∑ x : G, |if q i = x then a i else 0| := Finset.sum_comm
    _ = ∑ i : I, |a i| := by simp [apply_ite]

theorem foldKernel_l1_eq {I G : Type} [Fintype I] [Fintype G] [DecidableEq G]
    (a : I → ℝ) (q : I → G) (hq : Function.Injective q) :
    (∑ x : G, |foldKernel a q x|) = ∑ i : I, |a i| := by
  classical
  have hpoint (x : G) :
      |foldKernel a q x| = ∑ i : I, if q i = x then |a i| else 0 := by
    by_cases hx : ∃ i, q i = x
    · obtain ⟨i, rfl⟩ := hx
      have heq (j : I) : q j = q i ↔ j = i := hq.eq_iff
      simp [foldKernel, heq]
    · have heq (i : I) : q i ≠ x := fun h => hx ⟨i, h⟩
      simp [foldKernel, heq]
  simp_rw [hpoint]
  rw [Finset.sum_comm]
  simp

/-- A periodized finite stencil never has larger operator norm than its
unperiodized l1 mass. If offsets are injective, the bound is attained.
Injectivity is sufficient, not necessary: same-sign collisions can also
preserve l1 mass. -/
theorem periodization_norm {I G : Type} [Fintype I] [Fintype G]
    [AddCommGroup G] [DecidableEq G] (a : I → ℝ) (q : I → G) :
    ‖convolutionOperator (foldKernel a q)‖ ≤ ∑ i : I, |a i| ∧
    (Function.Injective q →
      ‖convolutionOperator (foldKernel a q)‖ = ∑ i : I, |a i|) := by
  rw [convolution_opNorm]
  exact ⟨foldKernel_l1_le a q, foldKernel_l1_eq a q⟩

/-- The l1 norm of a separable product is the product of the l1 norms. -/
theorem tensorKernel_l1 {G : Type} [Fintype G] (k : G → ℝ) (d : ℕ) :
    (∑ x : Fin d → G, |tensorKernel k d x|) = (∑ y : G, |k y|) ^ d := by
  classical
  simp only [tensorKernel, Finset.abs_prod]
  exact (Fintype.sum_pow (fun y : G => |k y|) d).symm

/-- Exact dimension dependence for every separable real convolution. -/
theorem tensor_convolution_opNorm {G : Type} [Fintype G] [AddCommGroup G]
    (k : G → ℝ) (d : ℕ) :
    ‖convolutionOperator (tensorKernel k d)‖ = (∑ y : G, |k y|) ^ d := by
  rw [convolution_opNorm, tensorKernel_l1]

/-! ## Concrete db2 specialization -/

-- Filter algebra adapted from the MIT-licensed predecessor; see NOTICE.
lemma c_sq : db2Scale ^ 2 = 1 / 32 := by
  unfold db2Scale
  have ht : (4 * sqrt 2) ^ 2 = (32 : ℝ) := by
    rw [mul_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  field_simp
  rw [← mul_pow]
  exact ht.symm

lemma h0 : db2Filter 0 = db2Scale * (1 + sqrt 3) := by simp [db2Filter]
lemma h1 : db2Filter 1 = db2Scale * (3 + sqrt 3) := by simp [db2Filter]
lemma h2 : db2Filter 2 = db2Scale * (3 - sqrt 3) := by simp [db2Filter]
lemma h3 : db2Filter 3 = db2Scale * (1 - sqrt 3) := by simp [db2Filter]

lemma R3 : db2Filter 0 * db2Filter 3 = (-1 : ℝ) / 16 := by
  rw [h0, h3]
  have : db2Scale * (1 + sqrt 3) * (db2Scale * (1 - sqrt 3)) = db2Scale ^ 2 * (1 - (sqrt 3) ^ 2) := by ring
  rw [this, c_sq, sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  norm_num

lemma R2 : db2Filter 0 * db2Filter 2 + db2Filter 1 * db2Filter 3 = 0 := by
  rw [h0, h1, h2, h3]
  have : (1 + sqrt 3) * (3 - sqrt 3) + (3 + sqrt 3) * (1 - sqrt 3) = 0 := by
    ring_nf
    rw [sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    ring
  have hfac :
      db2Scale * (1 + sqrt 3) * (db2Scale * (3 - sqrt 3)) + db2Scale * (3 + sqrt 3) * (db2Scale * (1 - sqrt 3)) =
        db2Scale ^ 2 * ((1 + sqrt 3) * (3 - sqrt 3) + (3 + sqrt 3) * (1 - sqrt 3)) := by
    ring
  rw [hfac, this]
  ring

lemma R1 : db2Filter 0 * db2Filter 1 + db2Filter 1 * db2Filter 2 + db2Filter 2 * db2Filter 3 = (9 : ℝ) / 16 := by
  rw [h0, h1, h2, h3]
  have h18 :
      (1 + sqrt 3) * (3 + sqrt 3) + (3 + sqrt 3) * (3 - sqrt 3) +
        (3 - sqrt 3) * (1 - sqrt 3) = 18 := by
    ring_nf
    rw [sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    ring
  have hfac :
      db2Scale * (1 + sqrt 3) * (db2Scale * (3 + sqrt 3)) + db2Scale * (3 + sqrt 3) * (db2Scale * (3 - sqrt 3)) +
        db2Scale * (3 - sqrt 3) * (db2Scale * (1 - sqrt 3)) =
        db2Scale ^ 2 * ((1 + sqrt 3) * (3 + sqrt 3) + (3 + sqrt 3) * (3 - sqrt 3) +
          (3 - sqrt 3) * (1 - sqrt 3)) := by
    ring
  calc
    db2Scale * (1 + sqrt 3) * (db2Scale * (3 + sqrt 3)) +
        db2Scale * (3 + sqrt 3) * (db2Scale * (3 - sqrt 3)) +
        db2Scale * (3 - sqrt 3) * (db2Scale * (1 - sqrt 3))
        = db2Scale ^ 2 * 18 := by rw [hfac, h18]
    _ = (1 / 32) * 18 := by rw [c_sq]
    _ = 9 / 16 := by norm_num

lemma R0 : db2Filter 0 ^ 2 + db2Filter 1 ^ 2 + db2Filter 2 ^ 2 + db2Filter 3 ^ 2 = 1 := by
  rw [h0, h1, h2, h3]
  have h32 :
      (1 + sqrt 3) ^ 2 + (3 + sqrt 3) ^ 2 + (3 - sqrt 3) ^ 2 + (1 - sqrt 3) ^ 2 = 32 := by
    ring_nf
    rw [sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    ring
  have hfac :
      (db2Scale * (1 + sqrt 3)) ^ 2 + (db2Scale * (3 + sqrt 3)) ^ 2 + (db2Scale * (3 - sqrt 3)) ^ 2 +
        (db2Scale * (1 - sqrt 3)) ^ 2 =
        db2Scale ^ 2 * ((1 + sqrt 3) ^ 2 + (3 + sqrt 3) ^ 2 + (3 - sqrt 3) ^ 2 +
          (1 - sqrt 3) ^ 2) := by
    ring
  calc
    (db2Scale * (1 + sqrt 3)) ^ 2 + (db2Scale * (3 + sqrt 3)) ^ 2 + (db2Scale * (3 - sqrt 3)) ^ 2 +
        (db2Scale * (1 - sqrt 3)) ^ 2
        = db2Scale ^ 2 * 32 := by rw [hfac, h32]
    _ = (1 / 32) * 32 := by rw [c_sq]
    _ = 1 := by norm_num

lemma autocorr_zero : db2Autocorr 0 = 1 := by
  unfold db2Autocorr
  simp [sum_range_succ]
  simpa [pow_two] using R0

lemma autocorr_one : db2Autocorr 1 = (9 : ℝ) / 16 := by
  unfold db2Autocorr
  simp [sum_range_succ, db2Filter]
  simpa [db2Filter] using R1

lemma autocorr_two : db2Autocorr 2 = 0 := by
  unfold db2Autocorr
  simp [sum_range_succ, db2Filter]
  simpa [db2Filter] using R2

lemma autocorr_three : db2Autocorr 3 = (-1 : ℝ) / 16 := by
  unfold db2Autocorr
  simp [sum_range_succ, db2Filter]
  simpa [db2Filter] using R3



/-- The seven rational taps really are half the autocorrelation of the
specified orthonormal db2 low-pass filter, at centered integer lags. -/
theorem db2_filter_identification (i : Fin 7) :
    db2Tap i = db2Autocorr (Int.natAbs ((i.val : ℤ) - 3)) / 2 := by
  fin_cases i <;>
    norm_num [db2Tap, autocorr_zero, autocorr_one, autocorr_two, autocorr_three]

theorem db2Tap_l1 : (∑ i : Fin 7, |db2Tap i|) = (9 : ℝ) / 8 := by
  norm_num [db2Tap, Fin.sum_univ_succ]

theorem db2Offset_injective (N : ℕ) (hN : 7 ≤ N) :
    Function.Injective (db2Offset N) := by
  intro i j hij
  unfold db2Offset at hij
  have hc : (i.val : ZMod N) = (j.val : ZMod N) := by
    rw [← sub_add_cancel (i.val : ZMod N) (3 : ZMod N), hij, sub_add_cancel]
  have hv := congrArg ZMod.val hc
  rw [ZMod.val_natCast_of_lt (lt_of_lt_of_le i.isLt hN),
      ZMod.val_natCast_of_lt (lt_of_lt_of_le j.isLt hN)] at hv
  exact Fin.ext hv

theorem db2Kernel_l1 (N : ℕ) [NeZero N] (hN : 7 ≤ N) :
    (∑ x : ZMod N, |db2Kernel N x|) = (9 : ℝ) / 8 := by
  change (∑ x : ZMod N, |foldKernel db2Tap (db2Offset N) x|) = (9 : ℝ) / 8
  rw [foldKernel_l1_eq db2Tap (db2Offset N) (db2Offset_injective N hN), db2Tap_l1]

/-- Paper Proposition 3.4, level one: the actual finite-grid operator norm,
for every positive period N >= 7 and every dimension d (including d=0). -/
theorem db2_opNorm (N d : ℕ) [NeZero N] (hN : 7 ≤ N) :
    ‖db2Operator N d‖ = ((9 : ℝ) / 8) ^ d := by
  unfold db2Operator
  rw [tensor_convolution_opNorm, db2Kernel_l1 N hN]

/-- A unit-amplitude signal attains the exact db2 bound. This proves
sharpness of the smoothing operator, not of a downstream TDA pipeline. -/
theorem db2_attains (N d : ℕ) [NeZero N] (hN : 7 ≤ N) :
    ∃ f : (Fin d → ZMod N) → ℝ,
      ‖f‖ = 1 ∧ ‖db2Operator N d f‖ = ((9 : ℝ) / 8) ^ d := by
  obtain ⟨f, hf, heq⟩ := convolution_attains (tensorKernel (db2Kernel N) d)
  exact ⟨f, hf, heq.trans (db2_opNorm N d hN)⟩

/-- The explicit deterministic perturbation bound for the smoothing map. -/
theorem db2_lipschitz (N d : ℕ) [NeZero N] (hN : 7 ≤ N)
    (f g : (Fin d → ZMod N) → ℝ) :
    ‖db2Operator N d f - db2Operator N d g‖ ≤ ((9 : ℝ) / 8) ^ d * ‖f - g‖ := by
  rw [← map_sub]
  calc
    ‖db2Operator N d (f - g)‖ ≤ ‖db2Operator N d‖ * ‖f - g‖ :=
      (db2Operator N d).le_opNorm (f - g)
    _ = ((9 : ℝ) / 8) ^ d * ‖f - g‖ := by rw [db2_opNorm N d hN]

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
  have _hμ : 0 ≤ μ := hμ
  have hμsqrt : 0 ≤ Real.sqrt μ := Real.sqrt_nonneg μ
  have hop : ‖P f - P g‖ ≤ ‖P‖ * ‖f - g‖ := by
    rw [← map_sub]
    exact P.le_opNorm (f - g)
  have hInf : lInf (landscape (P f) - landscape (P g)) ≤ L * ‖P‖ * ‖f - g‖ := by
    refine (hΛ (P f) (P g)).trans ?_
    calc
      L * ‖P f - P g‖ ≤ L * (‖P‖ * ‖f - g‖) := mul_le_mul_of_nonneg_left hop hL
      _ = L * ‖P‖ * ‖f - g‖ := by ring
  refine (hEmb (landscape (P f) - landscape (P g))).trans ?_
  calc
    Real.sqrt μ * lInf (landscape (P f) - landscape (P g))
        ≤ Real.sqrt μ * (L * ‖P‖ * ‖f - g‖) :=
      mul_le_mul_of_nonneg_left hInf hμsqrt
    _ = L * ‖P‖ * Real.sqrt μ * ‖f - g‖ := by ring

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
  calc
    lTwo (landscape (db2Operator N d f) - landscape (db2Operator N d g))
        ≤ L * ‖db2Operator N d‖ * Real.sqrt μ * ‖f - g‖ :=
      summary_bound_propagation (db2Operator N d) landscape lInf lTwo L μ hL hμ hΛ hEmb f g
    _ = L * ((9 : ℝ) / 8) ^ d * Real.sqrt μ * ‖f - g‖ := by rw [db2_opNorm N d hN]

/-- The exact db2 norm is the least constant that bounds the smoothing
operator. This is the sharp choice of `Cfp` in Lemma 3.2, not sharpness of a
landscape. -/
theorem db2_opNorm_least (N d : ℕ) [NeZero N] (hN : 7 ≤ N) {C : ℝ}
    (hC : ∀ f : (Fin d → ZMod N) → ℝ, ‖db2Operator N d f‖ ≤ C * ‖f‖) :
    ((9 : ℝ) / 8) ^ d ≤ C := by
  obtain ⟨f, hf, heq⟩ := db2_attains N d hN
  have hle := hC f
  rw [heq, hf, mul_one] at hle
  exact hle

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
  have _hμ : 0 ≤ μ := hμ
  have hμsqrt : 0 ≤ Real.sqrt μ := Real.sqrt_nonneg μ
  have hgap :
      ‖landscape (db2Operator N d f) - landscape (db2Operator N d g)‖
        ≤ L * ((9 : ℝ) / 8) ^ d * Real.sqrt μ * ‖f - g‖ := by
    calc
      ‖landscape (db2Operator N d f) - landscape (db2Operator N d g)‖
          ≤ L * Real.sqrt μ * ‖db2Operator N d f - db2Operator N d g‖ := hΛ _ _
      _ ≤ L * Real.sqrt μ * (((9 : ℝ) / 8) ^ d * ‖f - g‖) :=
        mul_le_mul_of_nonneg_left (db2_lipschitz N d hN f g) (mul_nonneg hL hμsqrt)
      _ = L * ((9 : ℝ) / 8) ^ d * Real.sqrt μ * ‖f - g‖ := by ring
  set a : ℝ := ‖landscape (db2Operator N d f)‖ with ha
  set b : ℝ := ‖landscape (db2Operator N d g)‖ with hb
  have hsq : |a ^ 2 - b ^ 2| = |a - b| * (a + b) := by
    rw [ha, hb, sq_sub_sq, abs_mul,
      abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _)), mul_comm]
  have hab : |a - b| ≤ ‖landscape (db2Operator N d f) - landscape (db2Operator N d g)‖ :=
    abs_norm_sub_norm_le _ _
  calc
    |a ^ 2 - b ^ 2| = |a - b| * (a + b) := hsq
    _ ≤ ‖landscape (db2Operator N d f) - landscape (db2Operator N d g)‖ * (a + b) :=
      mul_le_mul_of_nonneg_right hab (add_nonneg (norm_nonneg _) (norm_nonneg _))
    _ ≤ (L * ((9 : ℝ) / 8) ^ d * Real.sqrt μ * ‖f - g‖) * (a + b) :=
      mul_le_mul_of_nonneg_right hgap (add_nonneg (norm_nonneg _) (norm_nonneg _))

/-! ## Exact norms of the first three undecimated cascade levels -/

theorem cascadeOffset_injective (j N : ℕ) (hN : cascadeSupport j ≤ N) :
    Function.Injective (cascadeOffset j N) := by
  intro a b hab
  unfold cascadeOffset at hab
  have hc : (a.val : ZMod N) = (b.val : ZMod N) := by
    rw [← sub_add_cancel (a.val : ZMod N) (cascadeRadius j : ZMod N), hab, sub_add_cancel]
  have hv := congrArg ZMod.val hc
  rw [ZMod.val_natCast_of_lt (lt_of_lt_of_le a.isLt hN),
      ZMod.val_natCast_of_lt (lt_of_lt_of_le b.isLt hN)] at hv
  exact Fin.ext hv

lemma cascadeTap_abs (j : ℕ) (i : Fin (cascadeSupport j)) :
    |cascadeTap j i| =
      ((cascadeInt j ((i.val : ℤ) - (cascadeRadius j : ℤ))).natAbs : ℝ) /
        (cascadeScale j : ℝ) := by
  unfold cascadeTap
  rw [abs_div, ← Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast,
    abs_of_nonneg (Nat.cast_nonneg _)]

lemma cascadeTap_l1 (j num den : ℕ)
    (hsum : ∑ i : Fin (cascadeSupport j),
        (cascadeInt j ((i.val : ℤ) - (cascadeRadius j : ℤ))).natAbs = num)
    (hscale : cascadeScale j = den) :
    (∑ i : Fin (cascadeSupport j), |cascadeTap j i|) = (num : ℝ) / den := by
  simp_rw [cascadeTap_abs, hscale, div_eq_mul_inv]
  rw [← Finset.sum_mul, ← Nat.cast_sum, hsum]

theorem cascadeKernel_l1 (j N num den : ℕ) [NeZero N]
    (hN : cascadeSupport j ≤ N)
    (hsum : ∑ i : Fin (cascadeSupport j),
        (cascadeInt j ((i.val : ℤ) - (cascadeRadius j : ℤ))).natAbs = num)
    (hscale : cascadeScale j = den) :
    (∑ x : ZMod N, |cascadeKernel j N x|) = (num : ℝ) / den := by
  change (∑ x : ZMod N, |foldKernel (cascadeTap j) (cascadeOffset j N) x|) = (num : ℝ) / den
  rw [foldKernel_l1_eq (cascadeTap j) (cascadeOffset j N) (cascadeOffset_injective j N hN),
    cascadeTap_l1 j num den hsum hscale]

/-- Exact operator norm of undecimated db2 cascade level one.
The free kernel has nineteen taps, zeros included, and l1 mass `299/256`.
For every period `N >= 19` the centered offsets do not collide, so this is
the periodic operator norm in every dimension, including `d = 0`. Squaring
at `d = 2` gives `89401/65536`. This is one finite level, not a closed form
for every level. -/
theorem cascade_level1_opNorm (N d : ℕ) [NeZero N] (hN : 19 ≤ N) :
    ‖cascadeOperator 1 N d‖ = ((299 : ℝ) / 256) ^ d := by
  have hsupp : cascadeSupport 1 = 19 := by decide
  have hscale : cascadeScale 1 = 1024 := by decide
  have hsum : ∑ i : Fin (cascadeSupport 1),
      (cascadeInt 1 ((i.val : ℤ) - (cascadeRadius 1 : ℤ))).natAbs = 1196 := by
    set_option maxHeartbeats 10000000 in
    decide
  have hle : cascadeSupport 1 ≤ N := by rw [hsupp]; exact hN
  unfold cascadeOperator
  rw [tensor_convolution_opNorm, cascadeKernel_l1 1 N 1196 1024 hle hsum hscale]
  refine congrArg (fun x : ℝ => x ^ d) ?_
  norm_num

/-- Exact operator norm of cascade level two: `9663/8192`, for every
`N >= 43` and every dimension. The two-dimensional square is
`93373569/67108864`. -/
theorem cascade_level2_opNorm (N d : ℕ) [NeZero N] (hN : 43 ≤ N) :
    ‖cascadeOperator 2 N d‖ = ((9663 : ℝ) / 8192) ^ d := by
  have hsupp : cascadeSupport 2 = 43 := by decide
  have hscale : cascadeScale 2 = 32768 := by decide
  have hsum : ∑ i : Fin (cascadeSupport 2),
      (cascadeInt 2 ((i.val : ℤ) - (cascadeRadius 2 : ℤ))).natAbs = 38652 := by
    set_option maxHeartbeats 10000000 in
    decide
  have hle : cascadeSupport 2 ≤ N := by rw [hsupp]; exact hN
  unfold cascadeOperator
  rw [tensor_convolution_opNorm, cascadeKernel_l1 2 N 38652 32768 hle hsum hscale]
  refine congrArg (fun x : ℝ => x ^ d) ?_
  norm_num

/-- Exact operator norm of cascade level three: `309991/262144`, for every
`N >= 91` and every dimension. The two-dimensional square is
`96094420081/68719476736`. -/
theorem cascade_level3_opNorm (N d : ℕ) [NeZero N] (hN : 91 ≤ N) :
    ‖cascadeOperator 3 N d‖ = ((309991 : ℝ) / 262144) ^ d := by
  have hsupp : cascadeSupport 3 = 91 := by decide
  have hscale : cascadeScale 3 = 1048576 := by decide
  have hsum : ∑ i : Fin (cascadeSupport 3),
      (cascadeInt 3 ((i.val : ℤ) - (cascadeRadius 3 : ℤ))).natAbs = 1239964 := by
    set_option maxRecDepth 8192 in
    set_option maxHeartbeats 10000000 in
    decide
  have hle : cascadeSupport 3 ≤ N := by rw [hsupp]; exact hN
  unfold cascadeOperator
  rw [tensor_convolution_opNorm, cascadeKernel_l1 3 N 1239964 1048576 hle hsum hscale]
  refine congrArg (fun x : ℝ => x ^ d) ?_
  norm_num

/-! ## Cascade parity, symmetry and support -/

lemma natAbs_ge_sub (a k : ℤ) : a.natAbs - k.natAbs ≤ (a - k).natAbs := by
  have h := Int.natAbs_add_le (a - k) k
  rw [sub_add_cancel] at h
  omega

lemma cascadeInt_zero_of_large {n : ℤ} (h : 3 < n.natAbs) : cascadeInt 0 n = 0 := by
  rw [cascadeInt.eq_1]
  have h0 : n ≠ 0 := by
    rintro rfl
    simp at h
  have h1 : n.natAbs ≠ 1 := by omega
  have h3 : n.natAbs ≠ 3 := by omega
  simp [h0, h1, h3]

lemma cascadeRadius_zero : cascadeRadius 0 = 3 := by decide

lemma cascadeRadius_succ (j : ℕ) :
    cascadeRadius (j + 1) = cascadeRadius j + 3 * 2 ^ (j + 1) := by
  unfold cascadeRadius
  have hpow : 2 ^ (j + 2) = 2 * 2 ^ (j + 1) := by
    rw [pow_succ, Nat.mul_comm]
  rw [hpow]
  have h1 : 1 ≤ 2 ^ (j + 1) := Nat.one_le_two_pow
  omega

lemma int_two_pow_natAbs (n : ℕ) : ((2 : ℤ) ^ n).natAbs = 2 ^ n := by
  rw [Int.natAbs_pow]
  rfl

lemma cascadeInt_symm (j : ℕ) (n : ℤ) : cascadeInt j (-n) = cascadeInt j n := by
  induction j generalizing n with
  | zero =>
    rw [cascadeInt.eq_1, cascadeInt.eq_1]
    simp [Int.natAbs_neg]
  | succ j ih =>
    rw [cascadeInt.eq_2 (-n) j, cascadeInt.eq_2 n j]
    rw [show -n - 2 ^ (j + 1) = -(n + 2 ^ (j + 1)) by ring,
        show -n + 2 ^ (j + 1) = -(n - 2 ^ (j + 1)) by ring,
        show -n - 3 * 2 ^ (j + 1) = -(n + 3 * 2 ^ (j + 1)) by ring,
        show -n + 3 * 2 ^ (j + 1) = -(n - 3 * 2 ^ (j + 1)) by ring]
    rw [ih n, ih (n + 2 ^ (j + 1)), ih (n - 2 ^ (j + 1)),
        ih (n + 3 * 2 ^ (j + 1)), ih (n - 3 * 2 ^ (j + 1))]
    ring

lemma cascadeInt_even_base (t : ℤ) : cascadeInt 1 (2 * t) = 16 * cascadeInt 0 t := by
  by_cases h : t.natAbs ≤ 8
  · cases t with
    | ofNat k =>
      match k with
      | 0 => decide
      | 1 => decide
      | 2 => decide
      | 3 => decide
      | 4 => decide
      | 5 => decide
      | 6 => decide
      | 7 => decide
      | 8 => decide
      | k + 9 =>
        exfalso
        simp at h
        omega
    | negSucc k =>
      match k with
      | 0 => decide
      | 1 => decide
      | 2 => decide
      | 3 => decide
      | 4 => decide
      | 5 => decide
      | 6 => decide
      | 7 => decide
      | k + 8 =>
        exfalso
        simp [Int.natAbs_negSucc] at h
  · have ht : 8 < t.natAbs := lt_of_not_ge h
    rw [cascadeInt.eq_2 (2 * t) 0]
    have hpow : (2 : ℤ) ^ (0 + 1) = 2 := by norm_num
    rw [hpow]
    have hfar (c : ℤ) (hc : c.natAbs ≤ 6) : 3 < (2 * t - c).natAbs := by
      have hge := natAbs_ge_sub (2 * t) c
      have hmul : (2 * t).natAbs = 2 * t.natAbs := by rw [Int.natAbs_mul]; rfl
      omega
    have hz (c : ℤ) (hc : c.natAbs ≤ 6) : cascadeInt 0 (2 * t - c) = 0 :=
      cascadeInt_zero_of_large (hfar c hc)
    have h0 : cascadeInt 0 (2 * t) = 0 := by simpa using hz 0 (by decide)
    have hm2 : cascadeInt 0 (2 * t - 2) = 0 := hz 2 (by decide)
    have hp2 : cascadeInt 0 (2 * t + 2) = 0 := by simpa using hz (-2) (by decide)
    have hm6 : cascadeInt 0 (2 * t - 3 * 2) = 0 := hz (3 * 2) (by decide)
    have hp6 : cascadeInt 0 (2 * t + 3 * 2) = 0 := by simpa using hz (-(3 * 2)) (by decide)
    have ht0 : cascadeInt 0 t = 0 := cascadeInt_zero_of_large (by omega)
    rw [h0, hm2, hp2, hm6, hp6, ht0]
    norm_num

lemma cascadeInt_even (j : ℕ) : ∀ t : ℤ, cascadeInt (j + 1) (2 * t) = 16 * cascadeInt j t := by
  induction j with
  | zero =>
    intro t
    exact cascadeInt_even_base t
  | succ j ih =>
    intro t
    rw [cascadeInt.eq_2 (2 * t) (j + 1)]
    have hpow : (2 : ℤ) ^ (j + 2) = 2 * (2 : ℤ) ^ (j + 1) := by
      rw [pow_succ]
      ring
    rw [hpow]
    rw [show 2 * t - 2 * (2 : ℤ) ^ (j + 1) = 2 * (t - (2 : ℤ) ^ (j + 1)) by ring,
        show 2 * t + 2 * (2 : ℤ) ^ (j + 1) = 2 * (t + (2 : ℤ) ^ (j + 1)) by ring,
        show 2 * t - 3 * (2 * (2 : ℤ) ^ (j + 1)) = 2 * (t - 3 * (2 : ℤ) ^ (j + 1)) by ring,
        show 2 * t + 3 * (2 * (2 : ℤ) ^ (j + 1)) = 2 * (t + 3 * (2 : ℤ) ^ (j + 1)) by ring]
    rw [ih t, ih (t - (2 : ℤ) ^ (j + 1)), ih (t + (2 : ℤ) ^ (j + 1)),
        ih (t - 3 * (2 : ℤ) ^ (j + 1)), ih (t + 3 * (2 : ℤ) ^ (j + 1))]
    rw [cascadeInt.eq_2 t j]
    ring

lemma oddStencil_step (σ t : ℤ) (B : ℤ → ℤ) :
    let odd (u : ℤ) : ℤ := -B (u - 1) + 9 * B u + 9 * B (u + 1) - B (u + 2)
    let A (n : ℤ) : ℤ :=
      16 * B n + 9 * B (n - σ) + 9 * B (n + σ) - B (n - 3 * σ) - B (n + 3 * σ)
    16 * odd t + 9 * odd (t - σ) + 9 * odd (t + σ) - odd (t - 3 * σ) - odd (t + 3 * σ)
      = -A (t - 1) + 9 * A t + 9 * A (t + 1) - A (t + 2) := by
  dsimp
  ring

lemma cascadeInt_odd_base (t : ℤ) :
    cascadeInt 1 (2 * t + 1) =
      -cascadeInt 0 (t - 1) + 9 * cascadeInt 0 t + 9 * cascadeInt 0 (t + 1)
        - cascadeInt 0 (t + 2) := by
  by_cases h : t.natAbs ≤ 10
  · cases t with
    | ofNat k =>
      match k with
      | 0 => decide
      | 1 => decide
      | 2 => decide
      | 3 => decide
      | 4 => decide
      | 5 => decide
      | 6 => decide
      | 7 => decide
      | 8 => decide
      | 9 => decide
      | 10 => decide
      | k + 11 =>
        exfalso
        simp at h
        omega
    | negSucc k =>
      match k with
      | 0 => decide
      | 1 => decide
      | 2 => decide
      | 3 => decide
      | 4 => decide
      | 5 => decide
      | 6 => decide
      | 7 => decide
      | 8 => decide
      | 9 => decide
      | k + 10 =>
        exfalso
        simp [Int.natAbs_negSucc] at h
  · have ht : 10 < t.natAbs := lt_of_not_ge h
    rw [cascadeInt.eq_2 (2 * t + 1) 0]
    have hpow : (2 : ℤ) ^ (0 + 1) = 2 := by norm_num
    rw [hpow]
    have hfar (c : ℤ) (hc : c.natAbs ≤ 6) : 3 < (2 * t + 1 - c).natAbs := by
      have hge := natAbs_ge_sub (2 * t + 1) c
      have habs : 2 * t.natAbs - 1 ≤ (2 * t + 1).natAbs := by
        have hsub := natAbs_ge_sub (2 * t) (-1)
        have hmul : (2 * t).natAbs = 2 * t.natAbs := by rw [Int.natAbs_mul]; rfl
        omega
      omega
    have hz (c : ℤ) (hc : c.natAbs ≤ 6) : cascadeInt 0 (2 * t + 1 - c) = 0 :=
      cascadeInt_zero_of_large (hfar c hc)
    have h0 : cascadeInt 0 (2 * t + 1) = 0 := by simpa using hz 0 (by decide)
    have hm2 : cascadeInt 0 (2 * t + 1 - 2) = 0 := hz 2 (by decide)
    have hp2 : cascadeInt 0 (2 * t + 1 + 2) = 0 := by simpa using hz (-2) (by decide)
    have hm6 : cascadeInt 0 (2 * t + 1 - 3 * 2) = 0 := hz (3 * 2) (by decide)
    have hp6 : cascadeInt 0 (2 * t + 1 + 3 * 2) = 0 := by
      simpa using hz (-(3 * 2)) (by decide)
    have hr (c : ℤ) (hc : c.natAbs ≤ 2) : cascadeInt 0 (t - c) = 0 := by
      apply cascadeInt_zero_of_large
      have hge := natAbs_ge_sub t c
      omega
    have hr0 : cascadeInt 0 t = 0 := by simpa using hr 0 (by decide)
    have hr1 : cascadeInt 0 (t - 1) = 0 := hr 1 (by decide)
    have hp1 : cascadeInt 0 (t + 1) = 0 := by simpa using hr (-1) (by decide)
    have hp2t : cascadeInt 0 (t + 2) = 0 := by simpa using hr (-2) (by decide)
    rw [h0, hm2, hp2, hm6, hp6, hr0, hr1, hp1, hp2t]
    norm_num

lemma cascadeInt_odd (j : ℕ) : ∀ t : ℤ,
    cascadeInt (j + 1) (2 * t + 1) =
      -cascadeInt j (t - 1) + 9 * cascadeInt j t + 9 * cascadeInt j (t + 1)
        - cascadeInt j (t + 2) := by
  induction j with
  | zero =>
    intro t
    exact cascadeInt_odd_base t
  | succ j ih =>
    intro t
    rw [cascadeInt.eq_2 (2 * t + 1) (j + 1)]
    have hpow : (2 : ℤ) ^ (j + 2) = 2 * (2 : ℤ) ^ (j + 1) := by
      rw [pow_succ]
      ring
    set σ : ℤ := (2 : ℤ) ^ (j + 1)
    rw [hpow]
    rw [show 2 * t + 1 - 2 * σ = 2 * (t - σ) + 1 by ring,
        show 2 * t + 1 + 2 * σ = 2 * (t + σ) + 1 by ring,
        show 2 * t + 1 - 3 * (2 * σ) = 2 * (t - 3 * σ) + 1 by ring,
        show 2 * t + 1 + 3 * (2 * σ) = 2 * (t + 3 * σ) + 1 by ring]
    rw [ih t, ih (t - σ), ih (t + σ), ih (t - 3 * σ), ih (t + 3 * σ)]
    have halg := oddStencil_step σ t (cascadeInt j)
    rw [cascadeInt.eq_2 (t - 1) j, cascadeInt.eq_2 t j,
        cascadeInt.eq_2 (t + 1) j, cascadeInt.eq_2 (t + 2) j]
    simpa [σ] using halg

lemma cascadeInt_vanish (j : ℕ) {n : ℤ} (h : cascadeRadius j < n.natAbs) :
    cascadeInt j n = 0 := by
  induction j generalizing n with
  | zero =>
    rw [cascadeRadius_zero] at h
    exact cascadeInt_zero_of_large h
  | succ j ih =>
    rw [cascadeInt.eq_2 n j]
    have hbig : cascadeRadius j + 3 * 2 ^ (j + 1) < n.natAbs := by
      rwa [← cascadeRadius_succ j]
    have hkill (k : ℤ) (hk : k.natAbs ≤ 3 * 2 ^ (j + 1)) : cascadeInt j (n - k) = 0 := by
      apply ih
      have hge := natAbs_ge_sub n k
      omega
    have hcenter : cascadeInt j n = 0 := by
      apply ih
      omega
    have hpow : ((2 : ℤ) ^ (j + 1)).natAbs = 2 ^ (j + 1) := int_two_pow_natAbs _
    have hs : ((2 : ℤ) ^ (j + 1)).natAbs ≤ 3 * 2 ^ (j + 1) := by
      rw [hpow]
      omega
    have h3 : (3 * (2 : ℤ) ^ (j + 1)).natAbs = 3 * 2 ^ (j + 1) := by
      rw [Int.natAbs_mul, hpow]
      rfl
    rw [show n + (2 : ℤ) ^ (j + 1) = n - -((2 : ℤ) ^ (j + 1)) by ring,
        show n + 3 * (2 : ℤ) ^ (j + 1) = n - -(3 * (2 : ℤ) ^ (j + 1)) by ring]
    rw [hcenter,
        hkill ((2 : ℤ) ^ (j + 1)) hs,
        hkill (-((2 : ℤ) ^ (j + 1))) (by rw [Int.natAbs_neg]; exact hs),
        hkill (3 * (2 : ℤ) ^ (j + 1)) (by rw [h3]),
        hkill (-(3 * (2 : ℤ) ^ (j + 1))) (by rw [Int.natAbs_neg, h3])]
    ring

lemma cascadeInt_dyadic (j : ℕ) : cascadeInt j ((2 : ℤ) ^ (j + 1)) = 0 := by
  induction j with
  | zero => decide
  | succ j ih =>
    rw [show (2 : ℤ) ^ (j + 2) = 2 * (2 : ℤ) ^ (j + 1) by rw [pow_succ]; ring,
        cascadeInt_even j ((2 : ℤ) ^ (j + 1)), ih, mul_zero]

lemma cascadeInt_four (j : ℕ) : cascadeInt j ((2 : ℤ) ^ (j + 2)) = 0 := by
  induction j with
  | zero => decide
  | succ j ih =>
    rw [show (2 : ℤ) ^ (j + 3) = 2 * (2 : ℤ) ^ (j + 2) by rw [pow_succ]; ring,
        cascadeInt_even j ((2 : ℤ) ^ (j + 2)), ih, mul_zero]

lemma cascadeInt_origin (j : ℕ) : cascadeInt j 0 = (16 : ℤ) ^ (j + 1) := by
  induction j with
  | zero => decide
  | succ j ih =>
    rw [show (0 : ℤ) = 2 * 0 by ring, cascadeInt_even j 0, ih, pow_succ]
    ring


/-! ## Edge values of the cascade

`edgeP j` is `Aⱼ(2^{j+1}-2)`, `edgeQ j` is `Aⱼ(2^{j+1}-1)`,
`edgeF j` is `-Aⱼ(2^{j+1}+1)` and `edgeG j` is `-Aⱼ(2^{j+1}+2)`. -/

def edgeP (j : ℕ) : ℤ := cascadeInt j ((2 : ℤ) ^ (j + 1) - 2)

def edgeQ (j : ℕ) : ℤ := cascadeInt j ((2 : ℤ) ^ (j + 1) - 1)

def edgeF (j : ℕ) : ℤ := -cascadeInt j ((2 : ℤ) ^ (j + 1) + 1)

def edgeG (j : ℕ) : ℤ := -cascadeInt j ((2 : ℤ) ^ (j + 1) + 2)

def edgeH (j : ℕ) : ℤ := -cascadeInt j ((2 : ℤ) ^ (j + 1) + 3)

lemma edgeP_succ (j : ℕ) : edgeP (j + 1) = 16 * edgeQ j := by
  unfold edgeP edgeQ
  have h : (2 : ℤ) ^ (j + 2) - 2 = 2 * ((2 : ℤ) ^ (j + 1) - 1) := by ring
  rw [h, cascadeInt_even]

lemma edgeQ_succ (j : ℕ) : edgeQ (j + 1) = -edgeP j + 9 * edgeQ j + edgeF j := by
  unfold edgeQ edgeP edgeF
  have h : (2 : ℤ) ^ (j + 2) - 1 = 2 * ((2 : ℤ) ^ (j + 1) - 1) + 1 := by ring
  rw [h, cascadeInt_odd j ((2 : ℤ) ^ (j + 1) - 1)]
  rw [show (2 : ℤ) ^ (j + 1) - 1 + 1 = (2 : ℤ) ^ (j + 1) by ring, cascadeInt_dyadic j]
  ring

lemma edgeG_succ (j : ℕ) : edgeG (j + 1) = 16 * edgeF j := by
  unfold edgeG edgeF
  have h : (2 : ℤ) ^ (j + 2) + 2 = 2 * ((2 : ℤ) ^ (j + 1) + 1) := by ring
  rw [h, cascadeInt_even]
  ring

lemma edgeF_succ (j : ℕ) : edgeF (j + 1) = edgeQ j + 9 * edgeF j - edgeG j := by
  unfold edgeF edgeQ edgeG
  have h : (2 : ℤ) ^ (j + 2) + 1 = 2 * (2 : ℤ) ^ (j + 1) + 1 := by ring
  rw [h, cascadeInt_odd j ((2 : ℤ) ^ (j + 1)), cascadeInt_dyadic j]
  ring

lemma edgeH_succ (j : ℕ) : edgeH (j + 1) = 9 * edgeF j + 9 * edgeG j - edgeH j := by
  unfold edgeH edgeF edgeG
  have h : (2 : ℤ) ^ (j + 2) + 3 = 2 * ((2 : ℤ) ^ (j + 1) + 1) + 1 := by ring
  rw [h, cascadeInt_odd j ((2 : ℤ) ^ (j + 1) + 1)]
  rw [show (2 : ℤ) ^ (j + 1) + 1 - 1 = (2 : ℤ) ^ (j + 1) by ring, cascadeInt_dyadic j]
  ring

lemma pow_eight (j : ℕ) : (8 : ℤ) ^ j = (2 : ℤ) ^ j * (4 : ℤ) ^ j := by
  rw [show (8 : ℤ) = 2 * 4 by norm_num, mul_pow]

lemma edge_formula (j : ℕ) :
    3 * edgeP j = 32 * (8 : ℤ) ^ j + 24 * ((j : ℤ) + 1) * (4 : ℤ) ^ j - 8 * (2 : ℤ) ^ j ∧
    3 * edgeQ j = 16 * (8 : ℤ) ^ j + 3 * (2 * (j : ℤ) + 4) * (4 : ℤ) ^ j - (2 : ℤ) ^ j ∧
    3 * edgeF j = 16 * (8 : ℤ) ^ j - 3 * (2 * (j : ℤ) + 4) * (4 : ℤ) ^ j - (2 : ℤ) ^ j ∧
    3 * edgeG j = 32 * (8 : ℤ) ^ j - 24 * ((j : ℤ) + 1) * (4 : ℤ) ^ j - 8 * (2 : ℤ) ^ j := by
  induction j with
  | zero =>
    unfold edgeP edgeQ edgeF edgeG
    decide
  | succ j ih =>
    rcases ih with ⟨hp, hq, hf, hg⟩
    have hp' : 3 * edgeP (j + 1) = 16 * (3 * edgeQ j) := by
      rw [edgeP_succ]
      ring
    have hq' : 3 * edgeQ (j + 1) = -(3 * edgeP j) + 9 * (3 * edgeQ j) + 3 * edgeF j := by
      rw [edgeQ_succ]
      ring
    have hf' : 3 * edgeF (j + 1) = 3 * edgeQ j + 9 * (3 * edgeF j) - 3 * edgeG j := by
      rw [edgeF_succ]
      ring
    have hg' : 3 * edgeG (j + 1) = 16 * (3 * edgeF j) := by
      rw [edgeG_succ]
      ring
    rw [hp', hq', hf', hg', hp, hq, hf, hg]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> (simp only [Nat.cast_add, Nat.cast_one, pow_succ]; ring)

lemma edgeQ_pos (j : ℕ) : 0 < edgeQ j := by
  have hq := (edge_formula j).2.1
  have hfac : 16 * (8 : ℤ) ^ j - (2 : ℤ) ^ j = (2 : ℤ) ^ j * (16 * (4 : ℤ) ^ j - 1) := by
    rw [pow_eight]
    ring
  have h4 : (1 : ℤ) ≤ (4 : ℤ) ^ j := one_le_pow₀ (by norm_num)
  have hmain : 0 < 16 * (8 : ℤ) ^ j - (2 : ℤ) ^ j := by
    rw [hfac]
    have h2 : 0 < (2 : ℤ) ^ j := by positivity
    have hrest : 0 < 16 * (4 : ℤ) ^ j - 1 := by linarith
    nlinarith
  have hmid : 0 ≤ 3 * (2 * (j : ℤ) + 4) * (4 : ℤ) ^ j := by positivity
  have hsum : 0 < 16 * (8 : ℤ) ^ j + 3 * (2 * (j : ℤ) + 4) * (4 : ℤ) ^ j - (2 : ℤ) ^ j := by
    linarith
  linarith

lemma edge_base_values :
    edgeP 0 = 16 ∧ edgeQ 0 = 9 ∧ edgeF 0 = 1 ∧ edgeG 0 = 0 ∧ edgeH 0 = 0 := by
  unfold edgeP edgeQ edgeF edgeG edgeH
  decide

lemma cascadeInt_low (j : ℕ) :
    cascadeInt j 1 = (16 : ℤ) ^ (j + 1) - (3 * (j : ℤ) + 7) * (4 : ℤ) ^ j ∧
    cascadeInt j 2 = (16 : ℤ) ^ (j + 1) - (12 * (j : ℤ) + 16) * (4 : ℤ) ^ j := by
  induction j with
  | zero =>
    decide
  | succ j ih =>
    rcases ih with ⟨h1, h2⟩
    constructor
    · rw [show (1 : ℤ) = 2 * 0 + 1 by ring, cascadeInt_odd j 0]
      rw [show (0 : ℤ) - 1 = -1 by ring, cascadeInt_symm j 1]
      rw [show (0 : ℤ) + 1 = 1 by ring, show (0 : ℤ) + 2 = 2 by ring,
          cascadeInt_origin j, h1, h2]
      simp only [pow_succ, Nat.cast_succ]
      ring
    · rw [show (2 : ℤ) = 2 * 1 by ring, cascadeInt_even j 1, h1]
      simp only [pow_succ, Nat.cast_succ]
      ring

/-- Interior of the four-point stencil preserves the difference-ratio interval `[1/3, 3]`. -/
lemma diffCone_step (a b c : ℤ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : a ≤ 3 * b) (_hba : b ≤ 3 * a)
    (_hbc : b ≤ 3 * c) (hcb : c ≤ 3 * b) :
    let d0 : ℤ := a + 8 * b - c
    let d1 : ℤ := -a + 8 * b + c
    0 < d0 ∧ 0 < d1 ∧ d0 ≤ 3 * d1 ∧ d1 ≤ 3 * d0 := by
  dsimp
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith [ha, hb, hc, hab, _hba, _hbc, hcb]

lemma diffCone_cross (a b c d : ℤ)
    (_ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (_hd : 0 < d)
    (hab : a ≤ 3 * b) (hba : b ≤ 3 * a)
    (hbc : b ≤ 3 * c) (hcb : c ≤ 3 * b)
    (hcd : c ≤ 3 * d) (hdc : d ≤ 3 * c) :
    let d1 : ℤ := -a + 8 * b + c
    let d2 : ℤ := b + 8 * c - d
    0 < d2 ∧ d1 ≤ 3 * d2 ∧ d2 ≤ 3 * d1 := by
  dsimp
  refine ⟨?_, ?_, ?_⟩ <;> linarith [_ha, hb, hc, _hd, hab, hba, hbc, hcb, hcd, hdc]


lemma pow_four_sq (j : ℕ) : (4 : ℤ) ^ j = (2 : ℤ) ^ j * (2 : ℤ) ^ j := by
  have h4 : (4 : ℤ) = (2 : ℤ) ^ 2 := by norm_num
  rw [h4, ← pow_mul, mul_comm, pow_mul, pow_two]

lemma edge_p_gap (j : ℕ) :
    3 * (edgeP j - 2 * edgeQ j) = 6 * (2 : ℤ) ^ j * (2 * (j : ℤ) * (2 : ℤ) ^ j - 1) := by
  have hp := (edge_formula j).1
  have hq := (edge_formula j).2.1
  have h : 3 * (edgeP j - 2 * edgeQ j) = 3 * edgeP j - 2 * (3 * edgeQ j) := by ring
  rw [h, hp, hq, pow_eight, pow_four_sq]
  ring

lemma edge_q_sub_f (j : ℕ) :
    3 * (edgeQ j - edgeF j) = 6 * (2 * (j : ℤ) + 4) * (4 : ℤ) ^ j := by
  have hq := (edge_formula j).2.1
  have hf := (edge_formula j).2.2.1
  have h : 3 * (edgeQ j - edgeF j) = 3 * edgeQ j - 3 * edgeF j := by ring
  rw [h, hq, hf]
  ring

lemma edge_two_f_sub_g (j : ℕ) :
    3 * (2 * edgeF j - edgeG j) = 12 * (j : ℤ) * (4 : ℤ) ^ j + 6 * (2 : ℤ) ^ j := by
  have hf := (edge_formula j).2.2.1
  have hg := (edge_formula j).2.2.2
  have h : 3 * (2 * edgeF j - edgeG j) = 2 * (3 * edgeF j) - 3 * edgeG j := by ring
  rw [h, hf, hg]
  ring

lemma edge_five_gap (j : ℕ) :
    5 * (3 * edgeQ j) - 2 * (3 * edgeP j) =
      (4 : ℤ) ^ j * (16 * (2 : ℤ) ^ j - 18 * (j : ℤ) + 12) + 11 * (2 : ℤ) ^ j := by
  have hp := (edge_formula j).1
  have hq := (edge_formula j).2.1
  rw [hp, hq, pow_eight]
  ring

lemma two_pow_ge_linear (j : ℕ) : 6 * (j : ℤ) + 13 ≤ 16 * (2 : ℤ) ^ j := by
  induction j with
  | zero => norm_num
  | succ j ih =>
    have hpow : (2 : ℤ) ^ (j + 1) = 2 * (2 : ℤ) ^ j := by rw [pow_succ]; ring
    rw [Nat.cast_succ, hpow]
    linarith

lemma four_two_pow_ge (j : ℕ) : 3 * (j : ℤ) + 4 ≤ 4 * (2 : ℤ) ^ j := by
  induction j with
  | zero => norm_num
  | succ j ih =>
    have hpow : (2 : ℤ) ^ (j + 1) = 2 * (2 : ℤ) ^ j := by rw [pow_succ]; ring
    rw [Nat.cast_succ, hpow]
    linarith

lemma eighteen_pow_ge (j : ℕ) : 18 * (j : ℤ) < 16 * (2 : ℤ) ^ j + 12 := by
  induction j with
  | zero => norm_num
  | succ j ih =>
    cases j with
    | zero => norm_num
    | succ j =>
      have hpow : (2 : ℤ) ^ (j + 1 + 1) = 2 * (2 : ℤ) ^ (j + 1) := by
        rw [pow_succ]
        ring
      have htwo : (2 : ℤ) ≤ (2 : ℤ) ^ (j + 1) :=
        pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) (Nat.le_add_left 1 j)
      have hcast : ((j + 1 + 1 : ℕ) : ℤ) = ((j + 1 : ℕ) : ℤ) + 1 :=
        Nat.cast_succ (j + 1)
      rw [hcast, hpow]
      linarith

lemma edgeF_pos (j : ℕ) : 0 < edgeF j := by
  cases j with
  | zero =>
    have hf : edgeF 0 = 1 := (edge_base_values).2.2.1
    linarith
  | succ j =>
    have hf := (edge_formula (j + 1)).2.2.1
    have hcoe : 16 * (8 : ℤ) ^ (j + 1) - 3 * (2 * ((j + 1 : ℕ) : ℤ) + 4) * (4 : ℤ) ^ (j + 1)
        - (2 : ℤ) ^ (j + 1)
        = (4 : ℤ) ^ (j + 1) * (16 * (2 : ℤ) ^ (j + 1) - 6 * ((j + 1 : ℕ) : ℤ) - 12)
          - (2 : ℤ) ^ (j + 1) := by
      rw [pow_eight]
      ring
    have hlin : (1 : ℤ) ≤ 16 * (2 : ℤ) ^ (j + 1) - 6 * ((j + 1 : ℕ) : ℤ) - 12 := by
      linarith [two_pow_ge_linear (j + 1)]
    have hstrict : (2 : ℤ) ^ (j + 1) < (4 : ℤ) ^ (j + 1) := by
      rw [pow_four_sq]
      have h2 : (2 : ℤ) ≤ (2 : ℤ) ^ (j + 1) :=
        pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) (Nat.le_add_left 1 j)
      nlinarith
    have hpos : 0 < (4 : ℤ) ^ (j + 1) * (16 * (2 : ℤ) ^ (j + 1) - 6 * ((j + 1 : ℕ) : ℤ) - 12)
        - (2 : ℤ) ^ (j + 1) := by
      nlinarith [hlin, hstrict]
    linarith

lemma edge_order (j : ℕ) :
    edgeF j < edgeQ j ∧ edgeG j < 2 * edgeF j ∧
      (1 ≤ j → 2 * edgeQ j < edgeP j) ∧ 2 * edgeP j < 5 * edgeQ j := by
  have hqf := edge_q_sub_f j
  have hgf := edge_two_f_sub_g j
  have hgap := edge_p_gap j
  have hfive := edge_five_gap j
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hpos : 0 < 6 * (2 * (j : ℤ) + 4) * (4 : ℤ) ^ j := by positivity
    linarith
  · have hpos : 0 < 12 * (j : ℤ) * (4 : ℤ) ^ j + 6 * (2 : ℤ) ^ j := by
      have : 0 < (2 : ℤ) ^ j := by positivity
      positivity
    linarith
  · intro hj
    have hpos : 0 < 6 * (2 : ℤ) ^ j * (2 * (j : ℤ) * (2 : ℤ) ^ j - 1) := by
      have h2 : 0 < (2 : ℤ) ^ j := by positivity
      have hlin : (2 : ℤ) ≤ 2 * (j : ℤ) * (2 : ℤ) ^ j := by
        have hj' : (1 : ℤ) ≤ j := by exact_mod_cast hj
        have hpow : (1 : ℤ) ≤ (2 : ℤ) ^ j := one_le_pow₀ (by norm_num)
        nlinarith
      nlinarith
    linarith
  · have hinner : 0 < 16 * (2 : ℤ) ^ j - 18 * (j : ℤ) + 12 := by
      linarith [eighteen_pow_ge j]
    have h4 : 0 < (4 : ℤ) ^ j := by positivity
    have htail : 0 < 11 * (2 : ℤ) ^ j := by positivity
    have hsum : 0 < (4 : ℤ) ^ j * (16 * (2 : ℤ) ^ j - 18 * (j : ℤ) + 12) + 11 * (2 : ℤ) ^ j := by
      nlinarith
    linarith

/-! ## Center differences

`cDiff j k = A_j(k) - A_j(k+1)`. On the center `0 ≤ k < 2^(j+1) - 1` these
differences stay positive and consecutive ratios stay in `[1/3, 3]`. -/

def cDiff (j : ℕ) (k : ℤ) : ℤ :=
  cascadeInt j k - cascadeInt j (k + 1)

lemma cDiff_even (j : ℕ) (t : ℤ) :
    cDiff (j + 1) (2 * t) =
      cDiff j (t - 1) + 8 * cDiff j t - cDiff j (t + 1) := by
  unfold cDiff
  rw [cascadeInt_even j t, cascadeInt_odd j t]
  ring

lemma cDiff_odd (j : ℕ) (t : ℤ) :
    cDiff (j + 1) (2 * t + 1) =
      -cDiff j (t - 1) + 8 * cDiff j t + cDiff j (t + 1) := by
  unfold cDiff
  rw [show (2 * t + 1 + 1 : ℤ) = 2 * (t + 1) by ring, cascadeInt_even j (t + 1),
    cascadeInt_odd j t]
  ring

lemma cDiff_neg_one (j : ℕ) : cDiff j (-1) = -cDiff j 0 := by
  unfold cDiff
  rw [show (-1 : ℤ) + 1 = 0 by ring, cascadeInt_symm j 1]
  ring

lemma cDiff_zero (j : ℕ) :
    cDiff j 0 = (3 * (j : ℤ) + 7) * (4 : ℤ) ^ j := by
  unfold cDiff
  rw [show (0 : ℤ) + 1 = 1 by ring, cascadeInt_origin j, (cascadeInt_low j).1]
  ring

lemma cDiff_one (j : ℕ) :
    cDiff j 1 = 9 * ((j : ℤ) + 1) * (4 : ℤ) ^ j := by
  unfold cDiff
  rw [show (1 : ℤ) + 1 = 2 by ring, (cascadeInt_low j).1, (cascadeInt_low j).2]
  ring

lemma cDiff_succ_one (j : ℕ) :
    cDiff (j + 1) 1 = 9 * cDiff j 0 + cDiff j 1 := by
  rw [show (1 : ℤ) = 2 * 0 + 1 by ring, cDiff_odd j 0]
  rw [show (0 : ℤ) - 1 = -1 by ring, cDiff_neg_one j, show (0 : ℤ) + 1 = 1 by ring]
  ring

lemma cDiff_last (j : ℕ) :
    cDiff j ((2 : ℤ) ^ (j + 1) - 1) = edgeQ j := by
  unfold cDiff edgeQ
  rw [show ((2 : ℤ) ^ (j + 1) - 1) + 1 = (2 : ℤ) ^ (j + 1) by ring, cascadeInt_dyadic j]
  ring

lemma cDiff_penultimate (j : ℕ) :
    cDiff j ((2 : ℤ) ^ (j + 1) - 2) = edgeP j - edgeQ j := by
  unfold cDiff edgeP edgeQ
  rw [show ((2 : ℤ) ^ (j + 1) - 2) + 1 = (2 : ℤ) ^ (j + 1) - 1 by ring]

lemma cDiff_dyadic (j : ℕ) :
    cDiff j ((2 : ℤ) ^ (j + 1)) = edgeF j := by
  unfold cDiff edgeF
  rw [cascadeInt_dyadic j]
  ring

lemma nat_pow_cast_sub (j k : ℕ) (hk : k ≤ 2 ^ (j + 1)) :
    ((2 ^ (j + 1) - k : ℕ) : ℤ) = (2 : ℤ) ^ (j + 1) - (k : ℤ) := by
  rw [Nat.cast_sub hk, Nat.cast_pow]
  simp

lemma cast_two_mul (t : ℕ) : ((2 * t : ℕ) : ℤ) = 2 * (t : ℤ) := by
  rw [Nat.cast_mul]
  ring

lemma cast_two_mul_succ (t : ℕ) : ((2 * t + 1 : ℕ) : ℤ) = 2 * (t : ℤ) + 1 := by
  rw [Nat.cast_add, Nat.cast_mul]
  ring

lemma cDiff_head_ratio (j : ℕ) :
    0 < cDiff j 0 ∧ 0 < cDiff j 1 ∧
      cDiff j 0 ≤ 3 * cDiff j 1 ∧ cDiff j 1 ≤ 3 * cDiff j 0 := by
  rw [cDiff_zero, cDiff_one]
  have h4 : 0 < (4 : ℤ) ^ j := by positivity
  refine ⟨?_, ?_, ?_, ?_⟩
  · positivity
  · positivity
  · have hcoe : (3 * (j : ℤ) + 7) ≤ 27 * ((j : ℤ) + 1) := by linarith
    have hmul := mul_le_mul_of_nonneg_right hcoe (le_of_lt h4)
    linarith
  · have hcoe : 9 * ((j : ℤ) + 1) ≤ 3 * (3 * (j : ℤ) + 7) := by linarith
    have hmul := mul_le_mul_of_nonneg_right hcoe (le_of_lt h4)
    linarith

lemma cDiff_left_slack (j : ℕ) :
    3 * cDiff j 0 ≤ 7 * cDiff j 1 ∧ 5 * cDiff j 1 ≤ 26 * cDiff j 0 := by
  rw [cDiff_zero, cDiff_one]
  have h4 : 0 ≤ (4 : ℤ) ^ j := by positivity
  refine ⟨?_, ?_⟩
  · have hcoe : 3 * (3 * (j : ℤ) + 7) ≤ 7 * (9 * ((j : ℤ) + 1)) := by linarith
    have hmul := mul_le_mul_of_nonneg_right hcoe h4
    linarith
  · have hcoe : 5 * (9 * ((j : ℤ) + 1)) ≤ 26 * (3 * (j : ℤ) + 7) := by linarith
    have hmul := mul_le_mul_of_nonneg_right hcoe h4
    linarith

lemma leftCross (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (_hc : 0 < c)
    (hcb : c ≤ 3 * b) (h3 : 3 * a ≤ 7 * b) (h5 : 5 * b ≤ 26 * a) :
    0 < 9 * a + b ∧ 0 < a + 8 * b - c ∧
      9 * a + b ≤ 3 * (a + 8 * b - c) ∧ a + 8 * b - c ≤ 3 * (9 * a + b) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

lemma rightDiffs (p q f δ : ℤ)
    (hq : 0 < q) (hf : 0 < f) (hfq : f < q)
    (hpq : 2 * q < p) (hp5 : 2 * p < 5 * q)
    (hδ : 0 < δ) (hδd : δ ≤ 3 * (p - q)) (_hdδ : p - q ≤ 3 * δ) :
    0 < 8 * p - 9 * q + δ ∧ 0 < 8 * p - 7 * q - δ ∧ 0 < p + 7 * q - f ∧
      8 * p - 9 * q + δ ≤ 3 * (8 * p - 7 * q - δ) ∧
      8 * p - 7 * q - δ ≤ 3 * (8 * p - 9 * q + δ) ∧
      8 * p - 7 * q - δ ≤ 3 * (p + 7 * q - f) ∧
      p + 7 * q - f ≤ 3 * (8 * p - 7 * q - δ) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

lemma rightJunction (e δ d q : ℤ)
    (_he : 0 < e) (hδ : 0 < δ) (hd : 0 < d) (_hq : 0 < q)
    (hed : e ≤ 3 * δ) (_hde : δ ≤ 3 * e)
    (hδd : δ ≤ 3 * d) (_hdδ : d ≤ 3 * δ)
    (hqd : q < d) (hdq : 2 * d < 3 * q) :
    0 < -e + 8 * δ + d ∧ 0 < 8 * d - q + δ ∧
      -e + 8 * δ + d ≤ 3 * (8 * d - q + δ) ∧
      8 * d - q + δ ≤ 3 * (-e + 8 * δ + d) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

def CenterOK (j : ℕ) : Prop :=
  (∀ k : ℕ, k + 1 < 2 ^ (j + 1) → 0 < cDiff j (k : ℤ)) ∧
  (∀ k : ℕ, k + 2 < 2 ^ (j + 1) →
    cDiff j (k : ℤ) ≤ 3 * cDiff j ((k + 1 : ℕ) : ℤ) ∧
    cDiff j ((k + 1 : ℕ) : ℤ) ≤ 3 * cDiff j (k : ℤ))

lemma centerOK_zero : CenterOK 0 := by
  refine ⟨?_, ?_⟩
  · intro k hk
    have hk0 : k = 0 := by omega
    subst hk0
    unfold cDiff
    decide
  · intro k hk
    omega

lemma centerOK_one : CenterOK 1 := by
  refine ⟨?_, ?_⟩
  · intro k hk
    have hk' : k ≤ 2 := by omega
    interval_cases k <;> (unfold cDiff; decide)
  · intro k hk
    have hk' : k ≤ 1 := by omega
    interval_cases k <;> (unfold cDiff; decide)

lemma cDiff_step_cone {j t : ℕ} (hC : CenterOK j) (ht1 : 1 ≤ t)
    (ht : t + 2 < 2 ^ (j + 1)) :
    0 < cDiff (j + 1) (2 * (t : ℤ)) ∧
      0 < cDiff (j + 1) (2 * (t : ℤ) + 1) ∧
      cDiff (j + 1) (2 * (t : ℤ)) ≤ 3 * cDiff (j + 1) (2 * (t : ℤ) + 1) ∧
      cDiff (j + 1) (2 * (t : ℤ) + 1) ≤ 3 * cDiff (j + 1) (2 * (t : ℤ)) := by
  rcases hC with ⟨hpos, hratio⟩
  have hpred : (t - 1) + 1 = t := Nat.sub_add_cancel ht1
  have hab := (hratio (t - 1) (by omega)).1
  have hba := (hratio (t - 1) (by omega)).2
  have hbc := (hratio t (by omega)).1
  have hcb := (hratio t (by omega)).2
  rw [hpred] at hab hba
  have hcone := diffCone_step
    (cDiff j ((t - 1 : ℕ) : ℤ)) (cDiff j (t : ℤ)) (cDiff j ((t + 1 : ℕ) : ℤ))
    (hpos (t - 1) (by omega)) (hpos t (by omega)) (hpos (t + 1) (by omega))
    hab hba hbc hcb
  dsimp at hcone
  have hsub : (t : ℤ) - 1 = ((t - 1 : ℕ) : ℤ) := (Nat.cast_sub ht1).symm
  have hadd : (t : ℤ) + 1 = ((t + 1 : ℕ) : ℤ) := by
    symm
    rw [Nat.cast_add]
    ring
  have heven := cDiff_even j (t : ℤ)
  have hodd := cDiff_odd j (t : ℤ)
  rw [hsub, hadd] at heven hodd
  rw [heven, hodd]
  exact hcone

lemma cDiff_cross_cone {j t : ℕ} (hC : CenterOK j) (ht1 : 1 ≤ t)
    (ht : t + 3 < 2 ^ (j + 1)) :
    cDiff (j + 1) (2 * (t : ℤ) + 1) ≤
        3 * cDiff (j + 1) (2 * ((t + 1 : ℕ) : ℤ)) ∧
      cDiff (j + 1) (2 * ((t + 1 : ℕ) : ℤ)) ≤
        3 * cDiff (j + 1) (2 * (t : ℤ) + 1) := by
  rcases hC with ⟨hpos, hratio⟩
  have hpred : (t - 1) + 1 = t := Nat.sub_add_cancel ht1
  have htwo : (t + 1) + 1 = t + 2 := by omega
  have hab := (hratio (t - 1) (by omega)).1
  have hba := (hratio (t - 1) (by omega)).2
  have hbc := (hratio t (by omega)).1
  have hcb := (hratio t (by omega)).2
  have hcd := (hratio (t + 1) (by omega)).1
  have hdc := (hratio (t + 1) (by omega)).2
  rw [hpred] at hab hba
  rw [htwo] at hcd hdc
  have hcone := diffCone_cross
    (cDiff j ((t - 1 : ℕ) : ℤ)) (cDiff j (t : ℤ))
    (cDiff j ((t + 1 : ℕ) : ℤ)) (cDiff j ((t + 2 : ℕ) : ℤ))
    (hpos (t - 1) (by omega)) (hpos t (by omega))
    (hpos (t + 1) (by omega)) (hpos (t + 2) (by omega))
    hab hba hbc hcb hcd hdc
  dsimp at hcone
  have hsub : (t : ℤ) - 1 = ((t - 1 : ℕ) : ℤ) := (Nat.cast_sub ht1).symm
  have hadd : (t : ℤ) + 1 = ((t + 1 : ℕ) : ℤ) := by
    symm
    rw [Nat.cast_add]
    ring
  have hadd2 : ((t + 1 : ℕ) : ℤ) + 1 = ((t + 2 : ℕ) : ℤ) := by
    symm
    rw [show (t + 2 : ℕ) = t + 1 + 1 by omega, Nat.cast_add]
    ring
  have hback : ((t + 1 : ℕ) : ℤ) - 1 = (t : ℤ) := by
    rw [Nat.cast_add]
    ring
  have hodd := cDiff_odd j (t : ℤ)
  have heven := cDiff_even j ((t + 1 : ℕ) : ℤ)
  rw [hsub, hadd] at hodd
  rw [hback, hadd2] at heven
  rw [hodd, heven]
  exact ⟨hcone.2.1, hcone.2.2⟩

lemma two_pow_center_ge (j : ℕ) (hj : 1 ≤ j) : 4 ≤ 2 ^ (j + 1) := by
  have hpow := pow_le_pow_right₀ (by decide : (1 : ℕ) ≤ 2) (show 2 ≤ j + 1 by omega)
  norm_num at hpow
  exact hpow

lemma cDiff_left_cross {j : ℕ} (hj : 1 ≤ j) (hC : CenterOK j) :
    0 < cDiff (j + 1) 2 ∧
      cDiff (j + 1) 1 ≤ 3 * cDiff (j + 1) 2 ∧
      cDiff (j + 1) 2 ≤ 3 * cDiff (j + 1) 1 := by
  rcases hC with ⟨hpos, hratio⟩
  have hM := two_pow_center_ge j hj
  have ha := hpos 0 (by omega)
  have hb := hpos 1 (by omega)
  have hc := hpos 2 (by omega)
  have hcb := (hratio 1 (by omega)).2
  have hslack := cDiff_left_slack j
  have hcross := leftCross _ _ _ ha hb hc hcb hslack.1 hslack.2
  have hR : cDiff (j + 1) 2 = cDiff j 0 + 8 * cDiff j 1 - cDiff j 2 := by
    rw [show (2 : ℤ) = 2 * (1 : ℤ) by ring, cDiff_even j 1]
    rw [show (1 : ℤ) - 1 = 0 by ring, show (1 : ℤ) + 1 = 2 by ring]
    rfl
  rw [cDiff_succ_one j, hR]
  exact ⟨hcross.2.1, hcross.2.2.1, hcross.2.2.2⟩

lemma cDiff_right_evals (j : ℕ) :
    cDiff (j + 1) (2 * ((2 : ℤ) ^ (j + 1) - 2)) =
        8 * edgeP j - 9 * edgeQ j + cDiff j ((2 : ℤ) ^ (j + 1) - 3) ∧
      cDiff (j + 1) (2 * ((2 : ℤ) ^ (j + 1) - 2) + 1) =
        8 * edgeP j - 7 * edgeQ j - cDiff j ((2 : ℤ) ^ (j + 1) - 3) ∧
      cDiff (j + 1) (2 * ((2 : ℤ) ^ (j + 1) - 1)) =
        edgeP j + 7 * edgeQ j - edgeF j := by
  set N : ℤ := (2 : ℤ) ^ (j + 1)
  refine ⟨?_, ?_, ?_⟩
  · rw [cDiff_even j (N - 2), show (N - 2) - 1 = N - 3 by ring,
      show (N - 2) + 1 = N - 1 by ring, cDiff_penultimate j, cDiff_last j]
    ring
  · rw [cDiff_odd j (N - 2), show (N - 2) - 1 = N - 3 by ring,
      show (N - 2) + 1 = N - 1 by ring, cDiff_penultimate j, cDiff_last j]
    ring
  · rw [cDiff_even j (N - 1), show (N - 1) - 1 = N - 2 by ring,
      show (N - 1) + 1 = N by ring, cDiff_penultimate j, cDiff_last j, cDiff_dyadic j]
    ring

lemma cDiff_right_cone {j : ℕ} (hj : 1 ≤ j) (hC : CenterOK j) :
    0 < cDiff (j + 1) (2 * ((2 : ℤ) ^ (j + 1) - 2)) ∧
      0 < cDiff (j + 1) (2 * ((2 : ℤ) ^ (j + 1) - 2) + 1) ∧
      0 < cDiff (j + 1) (2 * ((2 : ℤ) ^ (j + 1) - 1)) ∧
      cDiff (j + 1) (2 * ((2 : ℤ) ^ (j + 1) - 2)) ≤
        3 * cDiff (j + 1) (2 * ((2 : ℤ) ^ (j + 1) - 2) + 1) ∧
      cDiff (j + 1) (2 * ((2 : ℤ) ^ (j + 1) - 2) + 1) ≤
        3 * cDiff (j + 1) (2 * ((2 : ℤ) ^ (j + 1) - 2)) ∧
      cDiff (j + 1) (2 * ((2 : ℤ) ^ (j + 1) - 2) + 1) ≤
        3 * cDiff (j + 1) (2 * ((2 : ℤ) ^ (j + 1) - 1)) ∧
      cDiff (j + 1) (2 * ((2 : ℤ) ^ (j + 1) - 1)) ≤
        3 * cDiff (j + 1) (2 * ((2 : ℤ) ^ (j + 1) - 2) + 1) := by
  rcases hC with ⟨hpos, hratio⟩
  have hM := two_pow_center_ge j hj
  have hδ := hpos (2 ^ (j + 1) - 3) (by omega)
  have _hpen := hpos (2 ^ (j + 1) - 2) (by omega)
  have hpair := hratio (2 ^ (j + 1) - 3) (by omega)
  have hcast3 := nat_pow_cast_sub j 3 (by omega)
  have hcast2 := nat_pow_cast_sub j 2 (by omega)
  have hδ' : cDiff j ((2 : ℤ) ^ (j + 1) - 3) = cDiff j ((2 ^ (j + 1) - 3 : ℕ) : ℤ) := by
    rw [hcast3]; rfl
  have hpen' : cDiff j ((2 : ℤ) ^ (j + 1) - 2) = cDiff j ((2 ^ (j + 1) - 2 : ℕ) : ℤ) := by
    rw [hcast2]; rfl
  have horder := edge_order j
  have hpq : 2 * edgeQ j < edgeP j := horder.2.2.1 hj
  have hp5 : 2 * edgeP j < 5 * edgeQ j := horder.2.2.2
  have hq : 0 < edgeQ j := edgeQ_pos j
  have hf : 0 < edgeF j := edgeF_pos j
  have hfq : edgeF j < edgeQ j := horder.1
  have hδZ : 0 < cDiff j ((2 : ℤ) ^ (j + 1) - 3) := by
    rw [hδ']
    exact hδ
  have hstep32 : (2 ^ (j + 1) - 3) + 1 = 2 ^ (j + 1) - 2 := by omega
  have hδd : cDiff j ((2 : ℤ) ^ (j + 1) - 3) ≤ 3 * (edgeP j - edgeQ j) := by
    have h := hpair.1
    rw [hstep32] at h
    rw [← hδ', ← hpen', cDiff_penultimate j] at h
    exact h
  have hdδ : edgeP j - edgeQ j ≤ 3 * cDiff j ((2 : ℤ) ^ (j + 1) - 3) := by
    have h := hpair.2
    rw [hstep32] at h
    rw [← hδ', ← hpen', cDiff_penultimate j] at h
    exact h
  have hAlg := rightDiffs (edgeP j) (edgeQ j) (edgeF j)
    (cDiff j ((2 : ℤ) ^ (j + 1) - 3)) hq hf hfq hpq hp5 hδZ hδd hdδ
  have heval := cDiff_right_evals j
  rw [heval.1, heval.2.1, heval.2.2]
  exact hAlg

lemma cDiff_junction_expr (j : ℕ) :
    cDiff (j + 1) (2 * ((2 : ℤ) ^ (j + 1) - 3) + 1) =
      -cDiff j ((2 : ℤ) ^ (j + 1) - 4) + 8 * cDiff j ((2 : ℤ) ^ (j + 1) - 3) +
        cDiff j ((2 : ℤ) ^ (j + 1) - 2) := by
  set N : ℤ := (2 : ℤ) ^ (j + 1)
  rw [cDiff_odd j (N - 3), show (N - 3) - 1 = N - 4 by ring, show (N - 3) + 1 = N - 2 by ring]

lemma cDiff_junction_cone {j : ℕ} (hj : 1 ≤ j) (hC : CenterOK j) :
    cDiff (j + 1) (2 * ((2 : ℤ) ^ (j + 1) - 3) + 1) ≤
        3 * cDiff (j + 1) (2 * ((2 : ℤ) ^ (j + 1) - 2)) ∧
      cDiff (j + 1) (2 * ((2 : ℤ) ^ (j + 1) - 2)) ≤
        3 * cDiff (j + 1) (2 * ((2 : ℤ) ^ (j + 1) - 3) + 1) := by
  rcases hC with ⟨hpos, hratio⟩
  have hM := two_pow_center_ge j hj
  have he := hpos (2 ^ (j + 1) - 4) (by omega)
  have hδ := hpos (2 ^ (j + 1) - 3) (by omega)
  have hd := hpos (2 ^ (j + 1) - 2) (by omega)
  have hpairE := hratio (2 ^ (j + 1) - 4) (by omega)
  have hpairD := hratio (2 ^ (j + 1) - 3) (by omega)
  have hc4 := nat_pow_cast_sub j 4 (by omega)
  have hc3 := nat_pow_cast_sub j 3 (by omega)
  have hc2 := nat_pow_cast_sub j 2 (by omega)
  have horder := edge_order j
  have hq : 0 < edgeQ j := edgeQ_pos j
  have hpq : 2 * edgeQ j < edgeP j := horder.2.2.1 hj
  have hp5 : 2 * edgeP j < 5 * edgeQ j := horder.2.2.2
  have hd_eq : cDiff j ((2 : ℤ) ^ (j + 1) - 2) = edgeP j - edgeQ j := cDiff_penultimate j
  have hqd : edgeQ j < cDiff j ((2 : ℤ) ^ (j + 1) - 2) := by
    rw [hd_eq]
    linarith
  have hdq : 2 * cDiff j ((2 : ℤ) ^ (j + 1) - 2) < 3 * edgeQ j := by
    rw [hd_eq]
    linarith
  have heZ : 0 < cDiff j ((2 : ℤ) ^ (j + 1) - 4) := by rw [hc4] at he; exact he
  have hδZ : 0 < cDiff j ((2 : ℤ) ^ (j + 1) - 3) := by rw [hc3] at hδ; exact hδ
  have hdZ : 0 < cDiff j ((2 : ℤ) ^ (j + 1) - 2) := by rw [hc2] at hd; exact hd
  have h41 : (2 ^ (j + 1) - 4) + 1 = 2 ^ (j + 1) - 3 := by omega
  have h32 : (2 ^ (j + 1) - 3) + 1 = 2 ^ (j + 1) - 2 := by omega
  have hE1 := hpairE.1
  have hE2 := hpairE.2
  have hD1 := hpairD.1
  have hD2 := hpairD.2
  rw [h41] at hE1 hE2
  rw [h32] at hD1 hD2
  rw [hc4, hc3] at hE1 hE2
  rw [hc3, hc2] at hD1 hD2
  have hJ := rightJunction
    (cDiff j ((2 : ℤ) ^ (j + 1) - 4))
    (cDiff j ((2 : ℤ) ^ (j + 1) - 3))
    (cDiff j ((2 : ℤ) ^ (j + 1) - 2))
    (edgeQ j) heZ hδZ hdZ hq
    hE1 hE2 hD1 hD2 hqd hdq
  have hexpr := cDiff_junction_expr j
  have hD4 := (cDiff_right_evals j).1
  have h1 := hJ.2.2.1
  have h2 := hJ.2.2.2
  have hform : 8 * (edgeP j - edgeQ j) - edgeQ j = 8 * edgeP j - 9 * edgeQ j := by ring
  rw [hd_eq, hform] at h1 h2
  rw [hexpr, hD4, hd_eq]
  exact ⟨h1, h2⟩

lemma centerOK_succ {j : ℕ} (hj : 1 ≤ j) (hC : CenterOK j) : CenterOK (j + 1) := by
  have hM := two_pow_center_ge j hj
  have hpow : 2 ^ (j + 1 + 1) = 2 * 2 ^ (j + 1) := by
    rw [pow_succ]
    ring
  rcases cDiff_right_cone hj hC with ⟨hD4, hD3, hD2, h43, h34, h32, h23⟩
  refine ⟨?_, ?_⟩
  · intro k hk
    rw [hpow] at hk
    rcases Nat.even_or_odd' k with ⟨t, ht | ht⟩
    · rw [ht] at hk ⊢
      by_cases ht0 : t = 0
      · subst ht0
        simpa using (cDiff_head_ratio (j + 1)).1
      · rw [cast_two_mul t]
        by_cases htop : 2 ^ (j + 1) ≤ t + 2
        · have htM : t = 2 ^ (j + 1) - 1 ∨ t = 2 ^ (j + 1) - 2 := by omega
          rcases htM with htM | htM
          · rw [htM, nat_pow_cast_sub j 1 (by omega)]
            exact hD2
          · rw [htM, nat_pow_cast_sub j 2 (by omega)]
            exact hD4
        · have ht1 : 1 ≤ t := by omega
          have htI : t + 2 < 2 ^ (j + 1) := by omega
          exact (cDiff_step_cone hC ht1 htI).1
    · rw [ht] at hk ⊢
      by_cases ht0 : t = 0
      · subst ht0
        simpa using (cDiff_head_ratio (j + 1)).2.1
      · rw [cast_two_mul_succ t]
        by_cases htop : 2 ^ (j + 1) ≤ t + 2
        · have htM : t = 2 ^ (j + 1) - 2 := by omega
          rw [htM, nat_pow_cast_sub j 2 (by omega)]
          exact hD3
        · have ht1 : 1 ≤ t := by omega
          have htI : t + 2 < 2 ^ (j + 1) := by omega
          exact (cDiff_step_cone hC ht1 htI).2.1
  · intro k hk
    rw [hpow] at hk
    by_cases hk0 : k = 0
    · subst hk0
      have h := cDiff_head_ratio (j + 1)
      exact ⟨h.2.2.1, h.2.2.2⟩
    · by_cases hk1 : k = 1
      · subst hk1
        have h := cDiff_left_cross hj hC
        exact ⟨h.2.1, h.2.2⟩
      · rcases Nat.even_or_odd' k with ⟨t, ht | ht⟩
        · rw [ht] at hk ⊢
          rw [cast_two_mul t, cast_two_mul_succ t]
          by_cases htop : 2 ^ (j + 1) ≤ t + 2
          · have htM : t = 2 ^ (j + 1) - 2 := by omega
            rw [htM, nat_pow_cast_sub j 2 (by omega)]
            exact ⟨h43, h34⟩
          · have ht1 : 1 ≤ t := by omega
            have htI : t + 2 < 2 ^ (j + 1) := by omega
            exact (cDiff_step_cone hC ht1 htI).2.2
        · rw [ht] at hk ⊢
          have hnext : (2 * t + 1) + 1 = 2 * (t + 1) := by omega
          rw [cast_two_mul_succ t, hnext, cast_two_mul (t + 1)]
          by_cases hcross : t + 3 < 2 ^ (j + 1)
          · have ht1 : 1 ≤ t := by omega
            exact cDiff_cross_cone hC ht1 hcross
          · have htM : t = 2 ^ (j + 1) - 3 ∨ t = 2 ^ (j + 1) - 2 := by omega
            rcases htM with htM | htM
            · rw [htM]
              have hidx : (2 ^ (j + 1) - 3) + 1 = 2 ^ (j + 1) - 2 := by omega
              rw [hidx, nat_pow_cast_sub j 3 (by omega), nat_pow_cast_sub j 2 (by omega)]
              exact cDiff_junction_cone hj hC
            · rw [htM]
              have hidx : (2 ^ (j + 1) - 2) + 1 = 2 ^ (j + 1) - 1 := by omega
              rw [hidx, nat_pow_cast_sub j 2 (by omega), nat_pow_cast_sub j 1 (by omega)]
              exact ⟨h32, h23⟩

lemma centerOK_all (j : ℕ) : CenterOK j := by
  induction j with
  | zero => exact centerOK_zero
  | succ n ih =>
    cases n with
    | zero => exact centerOK_one
    | succ m => exact centerOK_succ (Nat.le_add_left 1 m) ih

lemma cascadeInt_center_pos (j k : ℕ) (hk : k < 2 ^ (j + 1)) :
    0 < cascadeInt j (k : ℤ) := by
  have hdiff := (centerOK_all j).1
  have hone : 1 ≤ 2 ^ (j + 1) := Nat.one_le_two_pow
  have hval : cascadeInt j ((2 : ℤ) ^ (j + 1) - 1) = edgeQ j := by
    have hlast := cDiff_last j
    unfold cDiff at hlast
    rw [show ((2 : ℤ) ^ (j + 1) - 1) + 1 = (2 : ℤ) ^ (j + 1) by ring] at hlast
    rw [cascadeInt_dyadic j] at hlast
    linarith
  induction hmeas : (2 ^ (j + 1) - 1 - k) generalizing k with
  | zero =>
      have hk' : k = 2 ^ (j + 1) - 1 := by omega
      rw [hk', nat_pow_cast_sub j 1 hone]
      simp only [Nat.cast_one]
      rw [hval]
      exact edgeQ_pos j
  | succ d ih =>
      have hk1 : (k + 1) < 2 ^ (j + 1) := by omega
      have hstep := hdiff k hk1
      unfold cDiff at hstep
      have hcast : (k : ℤ) + 1 = ((k + 1 : ℕ) : ℤ) := Nat.cast_succ k
      rw [hcast] at hstep
      have hrec := ih (k + 1) hk1 (by omega)
      linarith

/-- Interior of a negative first-side block preserves absolute ratios in `[1/2, 5/2]`. -/
lemma sideStencil (a b c d : ℤ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hba : b ≤ 2 * a) (hab : 2 * a ≤ 5 * b)
    (hcb : c ≤ 2 * b) (hbc : 2 * b ≤ 5 * c)
    (hdc : d ≤ 2 * c) (_hcd : 2 * c ≤ 5 * d) :
    let w := -a + 9 * b + 9 * c - d
    0 < w ∧ w ≤ 2 * (16 * b) ∧ 2 * (16 * b) ≤ 5 * w ∧
      16 * c ≤ 2 * w ∧ 2 * w ≤ 5 * (16 * c) := by
  dsimp
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> linarith

lemma cascadeInt_tail (j : ℕ) {n : ℤ} (hn : 4 * (2 : ℤ) ^ (j + 1) - 2 ≤ n) :
    cascadeInt (j + 1) n = -cascadeInt j (n - 3 * (2 : ℤ) ^ (j + 1)) := by
  rw [cascadeInt.eq_2 n j]
  set s : ℤ := (2 : ℤ) ^ (j + 1)
  have hspos : (1 : ℤ) ≤ s := one_le_pow₀ (by norm_num : (1 : ℤ) ≤ 2)
  have hR : (cascadeRadius j : ℤ) = 3 * s - 3 := by
    unfold cascadeRadius
    rw [Nat.cast_mul, Nat.cast_sub (by exact Nat.one_le_two_pow), Nat.cast_pow]
    simp [s]
    ring
  have kill (x : ℤ) (hx : (cascadeRadius j : ℤ) < x) : cascadeInt j x = 0 := by
    apply cascadeInt_vanish
    have hx0 : 0 ≤ x := by
      have : (0 : ℤ) ≤ cascadeRadius j := by positivity
      linarith
    have habs : (x.natAbs : ℤ) = x := Int.natAbs_of_nonneg hx0
    rw [← habs] at hx
    exact_mod_cast hx
  have hcenter : cascadeInt j n = 0 := kill n (by linarith [hR, hn, hspos])
  have hm : cascadeInt j (n - s) = 0 := kill (n - s) (by linarith [hR, hn, hspos])
  have hp : cascadeInt j (n + s) = 0 := kill (n + s) (by linarith [hR, hn, hspos])
  have hp3 : cascadeInt j (n + 3 * s) = 0 := kill (n + 3 * s) (by linarith [hR, hn, hspos])
  rw [hcenter, hm, hp, hp3]
  ring

/-! ## First-side signs

On level `j`, with `N = 2^(j+1)`, the samples `A_j(N+k)` for `k = 1, …, N-1`
are strictly negative, and consecutive absolute values have ratios in
`[1/2, 5/2]`. Evens of the next level are sixteen times the previous side.
Interior odds stay in that ratio interval by `sideStencil`. The two left odds
use the edge tuple `(q,f,g,h)`; the two right odds use the dyadic zero and,
for the last sample, the tail copy of `edgeF` one level down. -/

lemma two_pow_add_two (j : ℕ) : (2 : ℤ) ^ (j + 2) = 4 * (2 : ℤ) ^ j := by
  have h1 : (2 : ℤ) ^ (j + 1) = 2 * (2 : ℤ) ^ j := by rw [pow_succ]; ring
  rw [show j + 2 = (j + 1) + 1 by omega, pow_succ, h1]
  ring

lemma head_gap_nonneg (j : ℕ) :
    0 ≤ 512 * (8 : ℤ) ^ j - (216 * (j : ℤ) + 408) * (4 : ℤ) ^ j
      - 38 * (2 : ℤ) ^ j := by
  induction j with
  | zero => norm_num
  | succ j ih =>
    have h8 : (8 : ℤ) ^ (j + 1) = 8 * (8 : ℤ) ^ j := by rw [pow_succ]; ring
    have h4 : (4 : ℤ) ^ (j + 1) = 4 * (4 : ℤ) ^ j := by rw [pow_succ]; ring
    have h2 : (2 : ℤ) ^ (j + 1) = 2 * (2 : ℤ) ^ j := by rw [pow_succ]; ring
    have hcast : ((j + 1 : ℕ) : ℤ) = (j : ℤ) + 1 := Nat.cast_succ j
    rw [h8, h4, h2, hcast]
    have hstep :
        512 * (8 * (8 : ℤ) ^ j)
            - (216 * ((j : ℤ) + 1) + 408) * (4 * (4 : ℤ) ^ j)
            - 38 * (2 * (2 : ℤ) ^ j)
          = 8 * (512 * (8 : ℤ) ^ j - (216 * (j : ℤ) + 408) * (4 : ℤ) ^ j
              - 38 * (2 : ℤ) ^ j)
            + ((864 * (j : ℤ) + 768) * (4 : ℤ) ^ j + 228 * (2 : ℤ) ^ j) := by
      ring
    rw [hstep]
    have hpos : 0 ≤ (864 * (j : ℤ) + 768) * (4 : ℤ) ^ j + 228 * (2 : ℤ) ^ j := by
      positivity
    linarith

lemma edge_head_upper (j : ℕ) :
    2 * (edgeQ j + 9 * edgeF j - edgeG j) ≤ 80 * edgeF j := by
  have hq := (edge_formula j).2.1
  have hf := (edge_formula j).2.2.1
  have hg := (edge_formula j).2.2.2
  have hgap := head_gap_nonneg j
  have hdiff : 31 * (3 * edgeF j) + 3 * edgeG j - 3 * edgeQ j =
      512 * (8 : ℤ) ^ j - (216 * (j : ℤ) + 408) * (4 : ℤ) ^ j
        - 38 * (2 : ℤ) ^ j := by
    rw [hq, hf, hg]
    ring
  have hnonneg : 0 ≤ 31 * (3 * edgeF j) + 3 * edgeG j - 3 * edgeQ j := by
    rw [hdiff]
    exact hgap
  have hmul : 3 * (31 * edgeF j + edgeG j - edgeQ j) =
      31 * (3 * edgeF j) + 3 * edgeG j - 3 * edgeQ j := by ring
  have : 0 ≤ 31 * edgeF j + edgeG j - edgeQ j := by linarith
  linarith

lemma edgeG_pos {j : ℕ} (hj : 1 ≤ j) : 0 < edgeG j := by
  cases j with
  | zero => omega
  | succ j =>
    rw [edgeG_succ]
    exact mul_pos (by norm_num) (edgeF_pos j)

lemma edgeP_pos {j : ℕ} (hj : 1 ≤ j) : 0 < edgeP j := by
  have h := (edge_order j).2.2.1 hj
  linarith [edgeQ_pos j]

/-- Leftmost new side sample, compared with the following even sample `16 f`. -/
lemma sideHead (q f g : ℤ) (hq : 0 < q) (hf : 0 < f)
    (hqf : f < q) (hgf : g < 2 * f)
    (hup : 2 * (q + 9 * f - g) ≤ 80 * f) :
    let w := q + 9 * f - g
    0 < w ∧ 16 * f ≤ 2 * w ∧ 2 * w ≤ 5 * (16 * f) := by
  dsimp
  refine ⟨?_, ?_, ?_⟩ <;> linarith

/-- Third new side sample, between the evens `16 f` and `16 g`. -/
lemma sideHeadThird (f g h : ℤ)
    (hf : 0 < f) (hg : 0 < g) (hh : 0 < h)
    (hgf : g ≤ 2 * f) (hfg : 2 * f ≤ 5 * g)
    (hhg : h ≤ 2 * g) (_hgh : 2 * g ≤ 5 * h) :
    let w := 9 * f + 9 * g - h
    0 < w ∧ w ≤ 2 * (16 * f) ∧ 2 * (16 * f) ≤ 5 * w ∧
      16 * g ≤ 2 * w ∧ 2 * w ≤ 5 * (16 * g) := by
  dsimp
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> linarith

/-- Right interior odd, whose stencil reads a dyadic zero. -/
lemma sideEndZero (a b c : ℤ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hba : b ≤ 2 * a) (hab : 2 * a ≤ 5 * b)
    (hcb : c ≤ 2 * b) (hbc : 2 * b ≤ 5 * c) :
    let w := -a + 9 * b + 9 * c
    0 < w ∧ w ≤ 2 * (16 * b) ∧ 2 * (16 * b) ≤ 5 * w ∧
      16 * c ≤ 2 * w ∧ 2 * w ≤ 5 * (16 * c) := by
  dsimp
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> linarith

/-- Last new side sample. `b` and `c` are the previous center edge, so `b/c ∈ (2, 5/2)`. -/
lemma sideTailEnd (b c f : ℤ)
    (hb : 0 < b) (hc : 0 < c) (hf : 0 < f) (hfc : f < c)
    (hbc : 2 * c < b) (hcb : 2 * b < 5 * c) :
    let w := -b + 9 * c + f
    0 < w ∧ w ≤ 2 * (16 * c) ∧ 2 * (16 * c) ≤ 5 * w := by
  dsimp
  refine ⟨?_, ?_, ?_⟩ <;> linarith

lemma cascadeInt_tail_penult (j : ℕ) (hj : 1 ≤ j) :
    cascadeInt j ((2 : ℤ) ^ (j + 2) - 2) = -edgeP (j - 1) := by
  have hsum : (j - 1) + 1 = j := Nat.sub_add_cancel hj
  have hn : 4 * (2 : ℤ) ^ ((j - 1) + 1) - 2 ≤ (2 : ℤ) ^ (j + 2) - 2 := by
    rw [hsum, two_pow_add_two j]
  have htail := cascadeInt_tail (j - 1) hn
  rw [hsum] at htail
  have harg : (2 : ℤ) ^ (j + 2) - 2 - 3 * (2 : ℤ) ^ j = (2 : ℤ) ^ j - 2 := by
    rw [two_pow_add_two j]
    ring
  rw [harg] at htail
  unfold edgeP
  rw [show (2 : ℤ) ^ ((j - 1) + 1) = (2 : ℤ) ^ j by rw [hsum]]
  exact htail

lemma cascadeInt_tail_last (j : ℕ) (hj : 1 ≤ j) :
    cascadeInt j ((2 : ℤ) ^ (j + 2) - 1) = -edgeQ (j - 1) := by
  have hsum : (j - 1) + 1 = j := Nat.sub_add_cancel hj
  have hn : 4 * (2 : ℤ) ^ ((j - 1) + 1) - 2 ≤ (2 : ℤ) ^ (j + 2) - 1 := by
    rw [hsum, two_pow_add_two j]
    omega
  have htail := cascadeInt_tail (j - 1) hn
  rw [hsum] at htail
  have harg : (2 : ℤ) ^ (j + 2) - 1 - 3 * (2 : ℤ) ^ j = (2 : ℤ) ^ j - 1 := by
    rw [two_pow_add_two j]
    ring
  rw [harg] at htail
  unfold edgeQ
  rw [show (2 : ℤ) ^ ((j - 1) + 1) = (2 : ℤ) ^ j by rw [hsum]]
  exact htail

lemma cascadeInt_tail_next (j : ℕ) (hj : 1 ≤ j) :
    cascadeInt j ((2 : ℤ) ^ (j + 2) + 1) = edgeF (j - 1) := by
  have hsum : (j - 1) + 1 = j := Nat.sub_add_cancel hj
  have hn : 4 * (2 : ℤ) ^ ((j - 1) + 1) - 2 ≤ (2 : ℤ) ^ (j + 2) + 1 := by
    rw [hsum, two_pow_add_two j]
    omega
  have htail := cascadeInt_tail (j - 1) hn
  rw [hsum] at htail
  have harg : (2 : ℤ) ^ (j + 2) + 1 - 3 * (2 : ℤ) ^ j = (2 : ℤ) ^ j + 1 := by
    rw [two_pow_add_two j]
    ring
  rw [harg] at htail
  unfold edgeF
  rw [show (2 : ℤ) ^ ((j - 1) + 1) = (2 : ℤ) ^ j by rw [hsum]]
  exact htail

def sideAbs (j k : ℕ) : ℤ :=
  -cascadeInt j ((2 : ℤ) ^ (j + 1) + (k : ℤ))

lemma sideAbs_zero (j : ℕ) : sideAbs j 0 = 0 := by
  unfold sideAbs
  simp only [Nat.cast_zero]
  rw [show (2 : ℤ) ^ (j + 1) + 0 = (2 : ℤ) ^ (j + 1) by ring, cascadeInt_dyadic]
  ring

lemma sideAbs_one (j : ℕ) : sideAbs j 1 = edgeF j := by
  unfold sideAbs edgeF
  rfl

lemma sideAbs_two (j : ℕ) : sideAbs j 2 = edgeG j := by
  unfold sideAbs edgeG
  rfl

lemma sideAbs_three (j : ℕ) : sideAbs j 3 = edgeH j := by
  unfold sideAbs edgeH
  rfl

lemma sideAbs_dyadic (j : ℕ) : sideAbs j (2 ^ (j + 1)) = 0 := by
  unfold sideAbs
  have hidx : (2 : ℤ) ^ (j + 1) + ((2 ^ (j + 1) : ℕ) : ℤ) = (2 : ℤ) ^ (j + 2) := by
    rw [Nat.cast_pow]
    have h2 : (2 : ℤ) ^ (j + 2) = 2 * (2 : ℤ) ^ (j + 1) := by rw [pow_succ]; ring
    rw [h2]
    ring
  rw [hidx, cascadeInt_four]
  ring

lemma sideAbs_after (j : ℕ) (hj : 1 ≤ j) :
    sideAbs j (2 ^ (j + 1) + 1) = -edgeF (j - 1) := by
  unfold sideAbs
  have hidx : (2 : ℤ) ^ (j + 1) + ((2 ^ (j + 1) + 1 : ℕ) : ℤ)
      = (2 : ℤ) ^ (j + 2) + 1 := by
    rw [Nat.cast_add, Nat.cast_pow, Nat.cast_one]
    have h2 : (2 : ℤ) ^ (j + 2) = 2 * (2 : ℤ) ^ (j + 1) := by rw [pow_succ]; ring
    rw [h2]
    ring
  rw [hidx, cascadeInt_tail_next j hj]

lemma sideAbs_penult (j : ℕ) (hj : 1 ≤ j) :
    sideAbs j (2 ^ (j + 1) - 2) = edgeP (j - 1) := by
  unfold sideAbs
  have hle : 2 ≤ 2 ^ (j + 1) := by
    have hpow : 2 ^ 1 ≤ 2 ^ (j + 1) :=
      Nat.pow_le_pow_right (by norm_num : (1 : ℕ) ≤ 2) (Nat.le_add_left 1 j)
    simpa using hpow
  have hidx : (2 : ℤ) ^ (j + 1) + ((2 ^ (j + 1) - 2 : ℕ) : ℤ)
      = (2 : ℤ) ^ (j + 2) - 2 := by
    rw [nat_pow_cast_sub j 2 hle]
    have h2 : (2 : ℤ) ^ (j + 2) = 2 * (2 : ℤ) ^ (j + 1) := by rw [pow_succ]; ring
    rw [h2]
    ring
  rw [hidx, cascadeInt_tail_penult j hj]
  ring

lemma sideAbs_last (j : ℕ) (hj : 1 ≤ j) :
    sideAbs j (2 ^ (j + 1) - 1) = edgeQ (j - 1) := by
  unfold sideAbs
  have hidx : (2 : ℤ) ^ (j + 1) + ((2 ^ (j + 1) - 1 : ℕ) : ℤ)
      = (2 : ℤ) ^ (j + 2) - 1 := by
    rw [nat_pow_cast_sub j 1 Nat.one_le_two_pow]
    simp only [Nat.cast_one]
    have h2 : (2 : ℤ) ^ (j + 2) = 2 * (2 : ℤ) ^ (j + 1) := by rw [pow_succ]; ring
    rw [h2]
    ring
  rw [hidx, cascadeInt_tail_last j hj]
  ring

lemma sideAbs_even (j t : ℕ) : sideAbs (j + 1) (2 * t) = 16 * sideAbs j t := by
  unfold sideAbs
  have hpow : (2 : ℤ) ^ (j + 2) = 2 * (2 : ℤ) ^ (j + 1) := by rw [pow_succ]; ring
  have hidx : (2 : ℤ) ^ (j + 2) + ((2 * t : ℕ) : ℤ) =
      2 * ((2 : ℤ) ^ (j + 1) + (t : ℤ)) := by
    rw [cast_two_mul t, hpow]
    ring
  rw [hidx, cascadeInt_even j ((2 : ℤ) ^ (j + 1) + (t : ℤ))]
  ring

lemma sideAbs_odd_raw (j t : ℕ) :
    cascadeInt (j + 1) ((2 : ℤ) ^ (j + 2) + ((2 * t + 1 : ℕ) : ℤ)) =
      -cascadeInt j ((2 : ℤ) ^ (j + 1) + (t : ℤ) - 1)
        + 9 * cascadeInt j ((2 : ℤ) ^ (j + 1) + (t : ℤ))
        + 9 * cascadeInt j ((2 : ℤ) ^ (j + 1) + (t : ℤ) + 1)
        - cascadeInt j ((2 : ℤ) ^ (j + 1) + (t : ℤ) + 2) := by
  have hpow : (2 : ℤ) ^ (j + 2) = 2 * (2 : ℤ) ^ (j + 1) := by rw [pow_succ]; ring
  have hidx : (2 : ℤ) ^ (j + 2) + ((2 * t + 1 : ℕ) : ℤ) =
      2 * ((2 : ℤ) ^ (j + 1) + (t : ℤ)) + 1 := by
    rw [cast_two_mul_succ t, hpow]
    ring
  rw [hidx, cascadeInt_odd j ((2 : ℤ) ^ (j + 1) + (t : ℤ))]

lemma sideAbs_odd_four (j t : ℕ) (ht : 1 ≤ t) :
    sideAbs (j + 1) (2 * t + 1) =
      -sideAbs j (t - 1) + 9 * sideAbs j t + 9 * sideAbs j (t + 1)
        - sideAbs j (t + 2) := by
  unfold sideAbs
  rw [sideAbs_odd_raw j t]
  have hsub : (t : ℤ) - 1 = ((t - 1 : ℕ) : ℤ) := (Nat.cast_sub ht).symm
  have hadd1 : (t : ℤ) + 1 = ((t + 1 : ℕ) : ℤ) := (Nat.cast_succ t).symm
  have hadd2 : (t : ℤ) + 2 = ((t + 2 : ℕ) : ℤ) := by
    rw [Nat.cast_add]
    rfl
  have hL1 : (2 : ℤ) ^ (j + 1) + (t : ℤ) - 1
      = (2 : ℤ) ^ (j + 1) + ((t - 1 : ℕ) : ℤ) := by
    rw [← hsub]
    ring
  have hL2 : (2 : ℤ) ^ (j + 1) + (t : ℤ) + 1
      = (2 : ℤ) ^ (j + 1) + ((t + 1 : ℕ) : ℤ) := by
    rw [← hadd1]
    ring
  have hL3 : (2 : ℤ) ^ (j + 1) + (t : ℤ) + 2
      = (2 : ℤ) ^ (j + 1) + ((t + 2 : ℕ) : ℤ) := by
    rw [← hadd2]
    ring
  rw [hL1, hL2, hL3]
  ring

lemma sideAbs_odd_head (j : ℕ) :
    sideAbs (j + 1) 1 = edgeQ j + 9 * edgeF j - edgeG j := by
  unfold sideAbs edgeQ edgeF edgeG
  simp only [Nat.cast_one]
  have hpow : (2 : ℤ) ^ (j + 1 + 1) = 2 * (2 : ℤ) ^ (j + 1) := by rw [pow_succ]; ring
  have hidx : (2 : ℤ) ^ (j + 1 + 1) + 1 = 2 * (2 : ℤ) ^ (j + 1) + 1 := by
    rw [hpow]
  rw [hidx, cascadeInt_odd j ((2 : ℤ) ^ (j + 1)), cascadeInt_dyadic j]
  ring

lemma sideAbs_odd_third (j : ℕ) :
    sideAbs (j + 1) 3 = 9 * edgeF j + 9 * edgeG j - edgeH j := by
  unfold sideAbs edgeF edgeG edgeH
  simp only [Nat.cast_ofNat]
  have hpow : (2 : ℤ) ^ (j + 1 + 1) = 2 * (2 : ℤ) ^ (j + 1) := by rw [pow_succ]; ring
  have hidx : (2 : ℤ) ^ (j + 1 + 1) + 3 = 2 * ((2 : ℤ) ^ (j + 1) + 1) + 1 := by
    rw [hpow]
    ring
  rw [hidx, cascadeInt_odd j ((2 : ℤ) ^ (j + 1) + 1)]
  rw [show (2 : ℤ) ^ (j + 1) + 1 - 1 = (2 : ℤ) ^ (j + 1) by ring, cascadeInt_dyadic j]
  ring

def SideOK (j : ℕ) : Prop :=
  (∀ k : ℕ, 1 ≤ k → k < 2 ^ (j + 1) → 0 < sideAbs j k) ∧
  (∀ k : ℕ, 1 ≤ k → k + 1 < 2 ^ (j + 1) →
    sideAbs j (k + 1) ≤ 2 * sideAbs j k ∧
      2 * sideAbs j k ≤ 5 * sideAbs j (k + 1))

lemma side_new_head (j : ℕ) :
    0 < sideAbs (j + 1) 1 ∧
      sideAbs (j + 1) 2 ≤ 2 * sideAbs (j + 1) 1 ∧
      2 * sideAbs (j + 1) 1 ≤ 5 * sideAbs (j + 1) 2 := by
  have h := sideHead (edgeQ j) (edgeF j) (edgeG j)
      (edgeQ_pos j) (edgeF_pos j) (edge_order j).1 (edge_order j).2.1
      (edge_head_upper j)
  dsimp at h
  have hev := sideAbs_even j 1
  have htwo : 2 * 1 = 2 := by omega
  rw [htwo] at hev
  rw [sideAbs_odd_head, hev, sideAbs_one]
  exact h

lemma side_pow_ge_eight {j : ℕ} (hj : 2 ≤ j) : 8 ≤ 2 ^ (j + 1) := by
  have h3 : 3 ≤ j + 1 := by omega
  have hpow := Nat.pow_le_pow_right (by norm_num : (1 : ℕ) ≤ 2) h3
  simpa using hpow

lemma side_new_third {j : ℕ} (hj : 2 ≤ j) (hS : SideOK j) :
    0 < sideAbs (j + 1) 3 ∧
      sideAbs (j + 1) 3 ≤ 2 * sideAbs (j + 1) 2 ∧
      2 * sideAbs (j + 1) 2 ≤ 5 * sideAbs (j + 1) 3 ∧
      sideAbs (j + 1) 4 ≤ 2 * sideAbs (j + 1) 3 ∧
      2 * sideAbs (j + 1) 3 ≤ 5 * sideAbs (j + 1) 4 := by
  have h8 := side_pow_ge_eight hj
  have hpair1 := hS.2 1 (by omega) (by omega)
  have hpair2 := hS.2 2 (by omega) (by omega)
  rw [sideAbs_one, sideAbs_two] at hpair1
  rw [sideAbs_two, sideAbs_three] at hpair2
  have hh : 0 < edgeH j := by
    rw [← sideAbs_three]
    exact hS.1 3 (by omega) (by linarith [h8])
  have hcone := sideHeadThird (edgeF j) (edgeG j) (edgeH j)
      (edgeF_pos j) (edgeG_pos (by omega)) hh
      hpair1.1 hpair1.2 hpair2.1 hpair2.2
  dsimp at hcone
  have he2 := sideAbs_even j 1
  have he4 := sideAbs_even j 2
  have h2 : 2 * 1 = 2 := by omega
  have h4 : 2 * 2 = 4 := by omega
  rw [h2] at he2
  rw [h4] at he4
  rw [sideAbs_one] at he2
  rw [sideAbs_two] at he4
  rw [sideAbs_odd_third, he2, he4]
  exact hcone

lemma side_new_interior {j t : ℕ} (hS : SideOK j)
    (ht2 : 2 ≤ t) (htop : t + 2 < 2 ^ (j + 1)) :
    0 < sideAbs (j + 1) (2 * t + 1) ∧
      sideAbs (j + 1) (2 * t + 1) ≤ 2 * sideAbs (j + 1) (2 * t) ∧
      2 * sideAbs (j + 1) (2 * t) ≤ 5 * sideAbs (j + 1) (2 * t + 1) ∧
      sideAbs (j + 1) (2 * (t + 1)) ≤ 2 * sideAbs (j + 1) (2 * t + 1) ∧
      2 * sideAbs (j + 1) (2 * t + 1) ≤ 5 * sideAbs (j + 1) (2 * (t + 1)) := by
  have ht1 : 1 ≤ t := by omega
  have hfour := sideAbs_odd_four j t ht1
  have ha := hS.1 (t - 1) (by omega) (by omega)
  have hb := hS.1 t (by omega) (by omega)
  have hc := hS.1 (t + 1) (by omega) (by omega)
  have hd := hS.1 (t + 2) (by omega) htop
  have hpair1 := hS.2 (t - 1) (by omega) (by omega)
  have hpair2 := hS.2 t (by omega) (by omega)
  have hpair3 := hS.2 (t + 1) (by omega) htop
  have hpred : (t - 1) + 1 = t := Nat.sub_add_cancel (by omega)
  rw [hpred] at hpair1
  have hcone := sideStencil
      (sideAbs j (t - 1)) (sideAbs j t) (sideAbs j (t + 1)) (sideAbs j (t + 2))
      ha hb hc hd hpair1.1 hpair1.2 hpair2.1 hpair2.2 hpair3.1 hpair3.2
  dsimp at hcone
  rw [hfour, sideAbs_even j t, sideAbs_even j (t + 1)]
  exact hcone

lemma side_new_end {j : ℕ} (hj : 2 ≤ j) (hS : SideOK j) :
    0 < sideAbs (j + 1) (2 * (2 ^ (j + 1) - 2) + 1) ∧
      sideAbs (j + 1) (2 * (2 ^ (j + 1) - 2) + 1) ≤
        2 * sideAbs (j + 1) (2 * (2 ^ (j + 1) - 2)) ∧
      2 * sideAbs (j + 1) (2 * (2 ^ (j + 1) - 2)) ≤
        5 * sideAbs (j + 1) (2 * (2 ^ (j + 1) - 2) + 1) ∧
      sideAbs (j + 1) (2 * (2 ^ (j + 1) - 1)) ≤
        2 * sideAbs (j + 1) (2 * (2 ^ (j + 1) - 2) + 1) ∧
      2 * sideAbs (j + 1) (2 * (2 ^ (j + 1) - 2) + 1) ≤
        5 * sideAbs (j + 1) (2 * (2 ^ (j + 1) - 1)) := by
  have h8 := side_pow_ge_eight hj
  set N : ℕ := 2 ^ (j + 1)
  have hfour := sideAbs_odd_four j (N - 2) (by omega)
  have hsub : (N - 2) - 1 = N - 3 := by omega
  have hadd1 : (N - 2) + 1 = N - 1 := by omega
  have hadd2 : (N - 2) + 2 = N := by omega
  rw [hsub, hadd1, hadd2] at hfour
  have hzero : sideAbs j N = 0 := by
    simpa [N] using sideAbs_dyadic j
  rw [hzero, sub_zero] at hfour
  have ha := hS.1 (N - 3) (by omega) (by omega)
  have hb := hS.1 (N - 2) (by omega) (by omega)
  have hc := hS.1 (N - 1) (by omega) (by omega)
  have hp1 := hS.2 (N - 3) (by omega) (by omega)
  have hp2 := hS.2 (N - 2) (by omega) (by omega)
  have hstep1 : (N - 3) + 1 = N - 2 := by omega
  have hstep2 : (N - 2) + 1 = N - 1 := by omega
  rw [hstep1] at hp1
  rw [hstep2] at hp2
  have hcone := sideEndZero
      (sideAbs j (N - 3)) (sideAbs j (N - 2)) (sideAbs j (N - 1))
      ha hb hc hp1.1 hp1.2 hp2.1 hp2.2
  dsimp at hcone
  rw [hfour, sideAbs_even j (N - 2), sideAbs_even j (N - 1)]
  exact hcone

lemma side_new_tail {j : ℕ} (hj : 2 ≤ j) (_hS : SideOK j) :
    0 < sideAbs (j + 1) (2 * (2 ^ (j + 1) - 1) + 1) ∧
      sideAbs (j + 1) (2 * (2 ^ (j + 1) - 1) + 1) ≤
        2 * sideAbs (j + 1) (2 * (2 ^ (j + 1) - 1)) ∧
      2 * sideAbs (j + 1) (2 * (2 ^ (j + 1) - 1)) ≤
        5 * sideAbs (j + 1) (2 * (2 ^ (j + 1) - 1) + 1) := by
  have hj1 : 1 ≤ j := by omega
  have hjprev : 1 ≤ j - 1 := by omega
  have h8 := side_pow_ge_eight hj
  set N : ℕ := 2 ^ (j + 1)
  have hfour := sideAbs_odd_four j (N - 1) (by omega)
  have hsub : (N - 1) - 1 = N - 2 := by omega
  have hadd1 : (N - 1) + 1 = N := Nat.sub_add_cancel (by omega)
  have hadd2 : (N - 1) + 2 = N + 1 := by omega
  rw [hsub, hadd1, hadd2] at hfour
  have hzero : sideAbs j N = 0 := by
    simpa [N] using sideAbs_dyadic j
  have hnext : sideAbs j (N + 1) = -edgeF (j - 1) := by
    simpa [N] using sideAbs_after j hj1
  have hpen : sideAbs j (N - 2) = edgeP (j - 1) := by
    simpa [N] using sideAbs_penult j hj1
  have hlast : sideAbs j (N - 1) = edgeQ (j - 1) := by
    simpa [N] using sideAbs_last j hj1
  rw [hzero, hnext, hpen, hlast] at hfour
  have hform : sideAbs (j + 1) (2 * (N - 1) + 1) =
      -edgeP (j - 1) + 9 * edgeQ (j - 1) + edgeF (j - 1) := by
    rw [hfour]
    ring
  have hcone := sideTailEnd (edgeP (j - 1)) (edgeQ (j - 1)) (edgeF (j - 1))
      (edgeP_pos hjprev) (edgeQ_pos (j - 1)) (edgeF_pos (j - 1))
      (edge_order (j - 1)).1
      ((edge_order (j - 1)).2.2.1 hjprev) (edge_order (j - 1)).2.2.2
  dsimp at hcone
  have heven := sideAbs_even j (N - 1)
  rw [hlast] at heven
  rw [hform, heven]
  exact hcone

lemma sideOK_zero : SideOK 0 := by
  refine ⟨?_, ?_⟩
  · intro k hk1 hk
    have hk0 : k = 1 := by omega
    subst hk0
    unfold sideAbs
    decide
  · intro k _ hk
    omega

lemma sideOK_one : SideOK 1 := by
  refine ⟨?_, ?_⟩
  · intro k hk1 hk
    have hk' : k ≤ 3 := by omega
    interval_cases k <;> (unfold sideAbs; decide)
  · intro k hk1 hk
    have hk' : k ≤ 2 := by omega
    interval_cases k <;> (unfold sideAbs; decide)

lemma sideOK_two : SideOK 2 := by
  refine ⟨?_, ?_⟩
  · intro k hk1 hk
    have hk' : k ≤ 7 := by omega
    interval_cases k <;> (unfold sideAbs; decide)
  · intro k hk1 hk
    have hk' : k ≤ 6 := by omega
    interval_cases k <;> (unfold sideAbs; decide)

lemma sideOK_succ {j : ℕ} (hj : 2 ≤ j) (hS : SideOK j) : SideOK (j + 1) := by
  have hpow : 2 ^ (j + 1 + 1) = 2 * 2 ^ (j + 1) := by rw [pow_succ]; ring
  refine ⟨?_, ?_⟩
  · intro k hk1 hk
    rw [hpow] at hk
    rcases Nat.even_or_odd' k with ⟨t, ht | ht⟩
    · rw [ht]
      have ht1 : 1 ≤ t := by omega
      have htN : t < 2 ^ (j + 1) := by omega
      rw [sideAbs_even]
      exact mul_pos (by norm_num) (hS.1 t ht1 htN)
    · rw [ht]
      by_cases ht0 : t = 0
      · subst ht0
        exact (side_new_head j).1
      · by_cases ht1 : t = 1
        · subst ht1
          exact (side_new_third hj hS).1
        · by_cases htop : t + 2 < 2 ^ (j + 1)
          · exact (side_new_interior hS (by omega) htop).1
          · have htM : t = 2 ^ (j + 1) - 2 ∨ t = 2 ^ (j + 1) - 1 := by omega
            rcases htM with htM | htM
            · subst htM
              exact (side_new_end hj hS).1
            · subst htM
              exact (side_new_tail hj hS).1
  · intro k hk1 hk
    rw [hpow] at hk
    rcases Nat.even_or_odd' k with ⟨t, ht | ht⟩
    · rw [ht] at hk ⊢
      by_cases ht1 : t = 1
      · subst ht1
        have h := side_new_third hj hS
        exact ⟨h.2.1, h.2.2.1⟩
      · by_cases htop : t + 2 < 2 ^ (j + 1)
        · have h := side_new_interior hS (by omega) htop
          exact ⟨h.2.1, h.2.2.1⟩
        · have htM : t = 2 ^ (j + 1) - 2 ∨ t = 2 ^ (j + 1) - 1 := by omega
          rcases htM with htM | htM
          · subst htM
            have h := side_new_end hj hS
            exact ⟨h.2.1, h.2.2.1⟩
          · subst htM
            exact (side_new_tail hj hS).2
    · rw [ht] at hk ⊢
      by_cases ht0 : t = 0
      · subst ht0
        have h := side_new_head j
        exact ⟨h.2.1, h.2.2⟩
      · by_cases ht1 : t = 1
        · subst ht1
          have h := side_new_third hj hS
          exact ⟨h.2.2.2.1, h.2.2.2.2⟩
        · by_cases htop : t + 2 < 2 ^ (j + 1)
          · have h := side_new_interior hS (by omega) htop
            have hnext : (2 * t + 1) + 1 = 2 * (t + 1) := by omega
            rw [hnext]
            exact ⟨h.2.2.2.1, h.2.2.2.2⟩
          · have htM : t = 2 ^ (j + 1) - 2 := by omega
            subst htM
            have h := side_new_end hj hS
            have hnext : (2 * (2 ^ (j + 1) - 2) + 1) + 1 = 2 * (2 ^ (j + 1) - 1) := by
              omega
            rw [hnext]
            exact ⟨h.2.2.2.1, h.2.2.2.2⟩

lemma sideOK_all (j : ℕ) : SideOK j := by
  induction j with
  | zero => exact sideOK_zero
  | succ n ih =>
    cases n with
    | zero => exact sideOK_one
    | succ m =>
      cases m with
      | zero => exact sideOK_two
      | succ k => exact sideOK_succ (Nat.le_add_left 2 k) ih

/-! ## Signed window sums

`centerSum j` adds the nonnegative indices of the central block,
`A_j(0), …, A_j(2^{j+1}-1)`. `sideSum j` adds the next block
`A_j(2^{j+1}), …, A_j(2^{j+2}-1)`, whose first sample is the dyadic zero.
Splitting the next window into even and odd indices and shifting the odd
stencil gives, for every `j`,

`centerSum (j+1) = 32 * centerSum j - 8 * A_j(0) + edgeQ j + edgeF j`,

and, for `j ≥ 1`,

`sideSum (j+1) = 32 * sideSum j - e_j - e_{j-1}`,

where `e_j = edgeQ j + edgeF j`. -/

lemma edge_sum_formula (j : ℕ) :
    3 * (edgeQ j + edgeF j) = 32 * (8 : ℤ) ^ j - 2 * (2 : ℤ) ^ j := by
  have hq := (edge_formula j).2.1
  have hf := (edge_formula j).2.2.1
  have hsum : 3 * (edgeQ j + edgeF j) = 3 * edgeQ j + 3 * edgeF j := by ring
  rw [hsum, hq, hf]
  ring

lemma sum_range_even_odd (N : ℕ) (f : ℕ → ℤ) :
    ∑ k ∈ Finset.range (2 * N), f k =
      (∑ t ∈ Finset.range N, f (2 * t)) + ∑ t ∈ Finset.range N, f (2 * t + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have htwo : 2 * (N + 1) = 2 * N + 1 + 1 := by omega
    rw [htwo, Finset.sum_range_succ, Finset.sum_range_succ, ih,
      Finset.sum_range_succ (fun t => f (2 * t)),
      Finset.sum_range_succ (fun t => f (2 * t + 1))]
    ring

lemma sum_shift_pred (N : ℕ) (hN : 0 < N) (g : ℤ → ℤ) :
    ∑ t ∈ Finset.range N, g ((t : ℤ) - 1) =
      (∑ t ∈ Finset.range N, g (t : ℤ)) + g (-1) - g (((N - 1) : ℕ) : ℤ) := by
  induction N with
  | zero => omega
  | succ n ih =>
    by_cases hn : n = 0
    · subst hn
      rw [Finset.sum_range_one, Finset.sum_range_one]
      have hz : ((0 : ℕ) : ℤ) - 1 = -1 := by
        simp only [Nat.cast_zero]
        ring
      rw [hz]
      ring
    · have hpos : 0 < n := by omega
      have hpred : ((n : ℕ) : ℤ) - 1 = (((n - 1) : ℕ) : ℤ) := by
        have hn1 : 1 ≤ n := by omega
        rw [Nat.cast_sub hn1, Nat.cast_one]
      have hcancel : (n + 1) - 1 = n := by omega
      rw [Finset.sum_range_succ, Finset.sum_range_succ, ih hpos, hpred, hcancel]
      ring

lemma sum_shift_succ (N : ℕ) (hN : 0 < N) (g : ℤ → ℤ) :
    ∑ t ∈ Finset.range N, g ((t : ℤ) + 1) =
      (∑ t ∈ Finset.range N, g (t : ℤ)) - g 0 + g (N : ℤ) := by
  have hNsucc : (N - 1) + 1 = N := by omega
  have hidx : ((N - 1 : ℕ) : ℤ) + 1 = (N : ℤ) := by
    have hN1 : 1 ≤ N := by omega
    rw [Nat.cast_sub hN1, Nat.cast_one]
    ring
  have hsplit := Finset.sum_range_succ' (fun t : ℕ => g (t : ℤ)) (N - 1)
  rw [hNsucc] at hsplit
  have hzero : g ((0 : ℕ) : ℤ) = g 0 := by simp
  rw [hzero] at hsplit
  have hfun : ∑ i ∈ Finset.range (N - 1), g (((i + 1 : ℕ) : ℤ)) =
      ∑ i ∈ Finset.range (N - 1), g ((i : ℤ) + 1) := by
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [Nat.cast_add, Nat.cast_one]
  rw [hfun] at hsplit
  have hlast := Finset.sum_range_succ (fun t : ℕ => g ((t : ℤ) + 1)) (N - 1)
  rw [hNsucc] at hlast
  have hrest : ∑ i ∈ Finset.range (N - 1), g ((i : ℤ) + 1) =
      (∑ t ∈ Finset.range N, g (t : ℤ)) - g 0 := by
    rw [hsplit]
    ring
  rw [hlast, hidx, hrest]

lemma sum_shift_add_two (N : ℕ) (hN : 0 < N) (g : ℤ → ℤ) :
    ∑ t ∈ Finset.range N, g ((t : ℤ) + 2) =
      (∑ t ∈ Finset.range N, g (t : ℤ)) - g 0 - g 1
        + g (N : ℤ) + g ((N : ℤ) + 1) := by
  have hstep := sum_shift_succ N hN (fun x => g (x + 1))
  have hbase := sum_shift_succ N hN g
  have hfun : ∑ t ∈ Finset.range N, g ((t : ℤ) + 2) =
      ∑ t ∈ Finset.range N, g ((t : ℤ) + 1 + 1) := by
    refine Finset.sum_congr rfl ?_
    intro t _
    have : (t : ℤ) + 2 = (t : ℤ) + 1 + 1 := by ring
    rw [this]
  have hone : g (0 + 1) = g 1 := by ring
  rw [hfun, hstep, hone, hbase]
  ring

lemma sum_four_stencil (N : ℕ) (g : ℤ → ℤ) :
    ∑ t ∈ Finset.range N,
        (-g ((t : ℤ) - 1) + 9 * g (t : ℤ) + 9 * g ((t : ℤ) + 1) - g ((t : ℤ) + 2)) =
      -(∑ t ∈ Finset.range N, g ((t : ℤ) - 1)) + 9 * ∑ t ∈ Finset.range N, g (t : ℤ)
        + 9 * ∑ t ∈ Finset.range N, g ((t : ℤ) + 1)
        - ∑ t ∈ Finset.range N, g ((t : ℤ) + 2) := by
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_neg_distrib,
    Finset.mul_sum]

def centerSum (j : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (2 ^ (j + 1)), cascadeInt j (k : ℤ)

lemma centerSum_zero : centerSum 0 = 25 := by
  unfold centerSum
  decide

lemma centerSum_succ (j : ℕ) :
    centerSum (j + 1) =
      32 * centerSum j - 8 * cascadeInt j 0 + edgeQ j + edgeF j := by
  unfold centerSum
  have hpow : 2 ^ (j + 1 + 1) = 2 * 2 ^ (j + 1) := by rw [pow_succ]; ring
  rw [hpow]
  have hNpos : 0 < 2 ^ (j + 1) := Nat.two_pow_pos _
  set N : ℕ := 2 ^ (j + 1) with hNdef
  have hN : 0 < N := by rw [hNdef]; exact hNpos
  have hNcast : (N : ℤ) = (2 : ℤ) ^ (j + 1) := by
    rw [hNdef, Nat.cast_pow]
    simp
  set g : ℤ → ℤ := cascadeInt j
  rw [sum_range_even_odd N (fun k => cascadeInt (j + 1) (k : ℤ))]
  have heven : ∑ t ∈ Finset.range N, cascadeInt (j + 1) ((2 * t : ℕ) : ℤ) =
      16 * ∑ t ∈ Finset.range N, g (t : ℤ) := by
    have hpt : ∀ t ∈ Finset.range N,
        cascadeInt (j + 1) ((2 * t : ℕ) : ℤ) = 16 * g (t : ℤ) := by
      intro t _
      rw [cast_two_mul t, cascadeInt_even j (t : ℤ)]
    rw [Finset.sum_congr rfl hpt, Finset.mul_sum]
  have hodd : ∑ t ∈ Finset.range N, cascadeInt (j + 1) ((2 * t + 1 : ℕ) : ℤ) =
      ∑ t ∈ Finset.range N,
        (-g ((t : ℤ) - 1) + 9 * g (t : ℤ) + 9 * g ((t : ℤ) + 1) - g ((t : ℤ) + 2)) := by
    refine Finset.sum_congr rfl ?_
    intro t _
    rw [cast_two_mul_succ t, cascadeInt_odd j (t : ℤ)]
  rw [heven, hodd, sum_four_stencil N g, sum_shift_pred N hN g, sum_shift_succ N hN g,
    sum_shift_add_two N hN g]
  have hsym : g (-1) = g 1 := cascadeInt_symm j 1
  have hzeroN : g (N : ℤ) = 0 := by
    rw [hNcast]
    exact cascadeInt_dyadic j
  have hq : g (((N - 1) : ℕ) : ℤ) = edgeQ j := by
    have hN1 : 1 ≤ N := by omega
    unfold edgeQ
    rw [show (((N - 1) : ℕ) : ℤ) = (2 : ℤ) ^ (j + 1) - 1 by
      rw [Nat.cast_sub hN1, hNcast, Nat.cast_one]]
  have hf : g ((N : ℤ) + 1) = -edgeF j := by
    unfold edgeF
    rw [show (N : ℤ) + 1 = (2 : ℤ) ^ (j + 1) + 1 by rw [hNcast]]
    ring
  rw [hsym, hzeroN, hq, hf]
  ring

lemma centerSum_one : centerSum 1 = 682 := by
  rw [centerSum_succ 0, centerSum_zero]
  have h0 : cascadeInt 0 0 = 16 := by decide
  have hq : edgeQ 0 = 9 := edge_base_values.2.1
  have hf : edgeF 0 = 1 := edge_base_values.2.2.1
  rw [h0, hq, hf]
  norm_num

/-- Full central signed mass, `A_j(-R)` through `A_j(R)` inside the dyadic gap. -/
def centerFull (j : ℕ) : ℤ :=
  2 * centerSum j - cascadeInt j 0

lemma centerFull_succ (j : ℕ) :
    centerFull (j + 1) = 32 * centerFull j + 2 * (edgeQ j + edgeF j) := by
  unfold centerFull
  have h0 : cascadeInt (j + 1) 0 = 16 * cascadeInt j 0 := by
    rw [cascadeInt_origin, cascadeInt_origin, pow_succ]
    ring
  rw [centerSum_succ, h0]
  ring

def sideSum (j : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (2 ^ (j + 1)),
    cascadeInt j ((2 : ℤ) ^ (j + 1) + (k : ℤ))

lemma sideSum_zero : sideSum 0 = -1 := by
  unfold sideSum
  decide

lemma sideSum_one : sideSum 1 = -43 := by
  unfold sideSum
  decide

lemma sideSum_succ {j : ℕ} (hj : 1 ≤ j) :
    sideSum (j + 1) =
      32 * sideSum j - (edgeQ j + edgeF j) - (edgeQ (j - 1) + edgeF (j - 1)) := by
  unfold sideSum
  have hpow : 2 ^ (j + 1 + 1) = 2 * 2 ^ (j + 1) := by rw [pow_succ]; ring
  have hpowZ : (2 : ℤ) ^ (j + 1 + 1) = 2 * (2 : ℤ) ^ (j + 1) := by rw [pow_succ]; ring
  have hexp : j + 1 + 1 = j + 2 := by omega
  rw [hpow]
  have hNpos : 0 < 2 ^ (j + 1) := Nat.two_pow_pos _
  set N : ℕ := 2 ^ (j + 1) with hNdef
  have hN : 0 < N := by rw [hNdef]; exact hNpos
  have hNcast : (N : ℤ) = (2 : ℤ) ^ (j + 1) := by
    rw [hNdef, Nat.cast_pow]
    simp
  set g : ℤ → ℤ := fun x => cascadeInt j ((2 : ℤ) ^ (j + 1) + x)
  rw [sum_range_even_odd N (fun k =>
    cascadeInt (j + 1) ((2 : ℤ) ^ (j + 1 + 1) + (k : ℤ)))]
  have heven : ∑ t ∈ Finset.range N,
      cascadeInt (j + 1) ((2 : ℤ) ^ (j + 1 + 1) + ((2 * t : ℕ) : ℤ)) =
      16 * ∑ t ∈ Finset.range N, g (t : ℤ) := by
    have hpt : ∀ t ∈ Finset.range N,
        cascadeInt (j + 1) ((2 : ℤ) ^ (j + 1 + 1) + ((2 * t : ℕ) : ℤ)) =
          16 * g (t : ℤ) := by
      intro t _
      have hidx : (2 : ℤ) ^ (j + 1 + 1) + ((2 * t : ℕ) : ℤ) =
          2 * ((2 : ℤ) ^ (j + 1) + (t : ℤ)) := by
        rw [cast_two_mul t, hpowZ]
        ring
      rw [hidx, cascadeInt_even j ((2 : ℤ) ^ (j + 1) + (t : ℤ))]
    rw [Finset.sum_congr rfl hpt, Finset.mul_sum]
  have hodd : ∑ t ∈ Finset.range N,
      cascadeInt (j + 1) ((2 : ℤ) ^ (j + 1 + 1) + ((2 * t + 1 : ℕ) : ℤ)) =
      ∑ t ∈ Finset.range N,
        (-g ((t : ℤ) - 1) + 9 * g (t : ℤ) + 9 * g ((t : ℤ) + 1) - g ((t : ℤ) + 2)) := by
    refine Finset.sum_congr rfl ?_
    intro t _
    rw [hexp]
    rw [sideAbs_odd_raw j t]
    have h1 : (2 : ℤ) ^ (j + 1) + (t : ℤ) - 1 =
        (2 : ℤ) ^ (j + 1) + ((t : ℤ) - 1) := by ring
    have h2 : (2 : ℤ) ^ (j + 1) + (t : ℤ) + 1 =
        (2 : ℤ) ^ (j + 1) + ((t : ℤ) + 1) := by ring
    have h3 : (2 : ℤ) ^ (j + 1) + (t : ℤ) + 2 =
        (2 : ℤ) ^ (j + 1) + ((t : ℤ) + 2) := by ring
    rw [h1, h2, h3]
  rw [heven, hodd, sum_four_stencil N g, sum_shift_pred N hN g, sum_shift_succ N hN g,
    sum_shift_add_two N hN g]
  have hg0 : g 0 = 0 := by
    dsimp [g]
    rw [add_zero, cascadeInt_dyadic]
  have hgN : g (N : ℤ) = 0 := by
    dsimp [g]
    rw [hNcast]
    have hidx : (2 : ℤ) ^ (j + 1) + (2 : ℤ) ^ (j + 1) = (2 : ℤ) ^ (j + 2) := by
      have h2 : (2 : ℤ) ^ (j + 2) = 2 * (2 : ℤ) ^ (j + 1) := by rw [pow_succ]; ring
      rw [h2]
      ring
    rw [hidx, cascadeInt_four]
  have hgNeg : g (-1) = edgeQ j := by
    dsimp [g]
    unfold edgeQ
    have : (2 : ℤ) ^ (j + 1) + -1 = (2 : ℤ) ^ (j + 1) - 1 := by ring
    rw [this]
  have hg1 : g 1 = -edgeF j := by
    dsimp [g]
    unfold edgeF
    ring
  have hgNm1 : g (((N - 1) : ℕ) : ℤ) = -edgeQ (j - 1) := by
    dsimp [g]
    have hN1 : 1 ≤ N := by omega
    have hidx : (2 : ℤ) ^ (j + 1) + (((N - 1) : ℕ) : ℤ) = (2 : ℤ) ^ (j + 2) - 1 := by
      have h2 : (2 : ℤ) ^ (j + 2) = 2 * (2 : ℤ) ^ (j + 1) := by rw [pow_succ]; ring
      rw [Nat.cast_sub hN1, hNcast, Nat.cast_one, h2]
      ring
    rw [hidx, cascadeInt_tail_last j hj]
  have hgNp1 : g ((N : ℤ) + 1) = edgeF (j - 1) := by
    dsimp [g]
    have hidx : (2 : ℤ) ^ (j + 1) + ((N : ℤ) + 1) = (2 : ℤ) ^ (j + 2) + 1 := by
      have h2 : (2 : ℤ) ^ (j + 2) = 2 * (2 : ℤ) ^ (j + 1) := by rw [pow_succ]; ring
      rw [hNcast, h2]
      ring
    rw [hidx, cascadeInt_tail_next j hj]
  rw [hg0, hgN, hgNeg, hg1, hgNm1, hgNp1]
  ring

lemma sideSum_two : sideSum 2 = -1470 := by
  rw [sideSum_succ (j := 1) (by omega), sideSum_one]
  have he0 : edgeQ 0 + edgeF 0 = 10 := by
    rw [edge_base_values.2.1, edge_base_values.2.2.1]
    norm_num
  have he1 : edgeQ 1 + edgeF 1 = 84 := by
    have h := edge_sum_formula 1
    norm_num at h
    have hmul : 3 * (edgeQ 1 + edgeF 1) = 3 * 84 := by simpa using h
    exact mul_left_cancel₀ (by norm_num : (3 : ℤ) ≠ 0) hmul
  rw [he0, he1]
  norm_num

/-- Absolute mass of one signed first side: `F_j = -sideSum j`. -/
def sideMass (j : ℕ) : ℤ :=
  -sideSum j

lemma sideMass_succ {j : ℕ} (hj : 1 ≤ j) :
    sideMass (j + 1) =
      32 * sideMass j + (edgeQ j + edgeF j) + (edgeQ (j - 1) + edgeF (j - 1)) := by
  unfold sideMass
  rw [sideSum_succ hj]
  ring

lemma centerFull_formula (j : ℕ) :
    45 * centerFull j =
      1568 * (32 : ℤ) ^ j - 40 * (8 : ℤ) ^ j + 2 * (2 : ℤ) ^ j := by
  induction j with
  | zero =>
    unfold centerFull
    rw [centerSum_zero]
    have h0 : cascadeInt 0 0 = 16 := by decide
    rw [h0]
    norm_num
  | succ j ih =>
    rw [centerFull_succ]
    have hmul :
        45 * (32 * centerFull j + 2 * (edgeQ j + edgeF j)) =
          32 * (45 * centerFull j) + 30 * (3 * (edgeQ j + edgeF j)) := by
      ring
    rw [hmul, ih, edge_sum_formula j]
    simp only [pow_succ]
    ring

lemma sideMass_formula (j : ℕ) :
    30 * sideMass j = 44 * (32 : ℤ) ^ j - 15 * (8 : ℤ) ^ j + (2 : ℤ) ^ j := by
  induction j with
  | zero =>
    unfold sideMass
    rw [sideSum_zero]
    norm_num
  | succ n ih =>
    cases n with
    | zero =>
      unfold sideMass
      rw [sideSum_one]
      norm_num
    | succ m =>
      have hm : 1 ≤ m + 1 := by omega
      rw [sideMass_succ hm]
      have hsub : (m + 1) - 1 = m := by omega
      rw [hsub]
      have hmul :
          30 * (32 * sideMass (m + 1) + (edgeQ (m + 1) + edgeF (m + 1))
              + (edgeQ m + edgeF m)) =
            32 * (30 * sideMass (m + 1))
              + 10 * (3 * (edgeQ (m + 1) + edgeF (m + 1)))
              + 10 * (3 * (edgeQ m + edgeF m)) := by
        ring
      rw [hmul, ih, edge_sum_formula (m + 1), edge_sum_formula m]
      simp only [pow_succ]
      ring

/-! ## Absolute mass

On `0 ≤ n < 2^{j+1}` the cascade is positive, so the absolute sum is
`centerSum`. On the next block it is negative, so the absolute sum is
`sideMass`. Past `2^{j+2}` the tail copies the previous level. Therefore

`oneAbs j = centerSum j + sideMass j + oneAbs (j-1) - centerSum (j-1)`

for `j ≥ 1`, and the full symmetric mass is `centerFull j + 2 * ∑_{i≤j} sideMass i`. -/

lemma sum_range_add (a b : ℕ) (f : ℕ → ℤ) :
    ∑ n ∈ Finset.range (a + b), f n =
      (∑ n ∈ Finset.range a, f n) + ∑ k ∈ Finset.range b, f (a + k) := by
  induction b with
  | zero => simp
  | succ b ih =>
    have hstep : a + (b + 1) = a + b + 1 := by omega
    rw [hstep, Finset.sum_range_succ, ih, Finset.sum_range_succ]
    ring

lemma center_natAbs (j k : ℕ) (hk : k < 2 ^ (j + 1)) :
    ((cascadeInt j (k : ℤ)).natAbs : ℤ) = cascadeInt j (k : ℤ) := by
  exact Int.natAbs_of_nonneg (le_of_lt (cascadeInt_center_pos j k hk))

lemma oneAbs_center (j : ℕ) :
    ∑ n ∈ Finset.range (2 ^ (j + 1)), ((cascadeInt j (n : ℤ)).natAbs : ℤ) =
      centerSum j := by
  unfold centerSum
  refine Finset.sum_congr rfl ?_
  intro n hn
  exact center_natAbs j n (Finset.mem_range.mp hn)

lemma side_nonpos (j k : ℕ) (hk : k < 2 ^ (j + 1)) :
    cascadeInt j ((2 : ℤ) ^ (j + 1) + (k : ℤ)) ≤ 0 := by
  by_cases hk0 : k = 0
  · subst hk0
    simp only [Nat.cast_zero, add_zero]
    rw [cascadeInt_dyadic]
  · have hS := (sideOK_all j).1 k (by omega) hk
    unfold sideAbs at hS
    linarith

lemma side_natAbs (j k : ℕ) (hk : k < 2 ^ (j + 1)) :
    ((cascadeInt j ((2 : ℤ) ^ (j + 1) + (k : ℤ))).natAbs : ℤ) =
      -cascadeInt j ((2 : ℤ) ^ (j + 1) + (k : ℤ)) := by
  have hnn : 0 ≤ -cascadeInt j ((2 : ℤ) ^ (j + 1) + (k : ℤ)) := by
    linarith [side_nonpos j k hk]
  rw [← Int.natAbs_neg]
  exact Int.natAbs_of_nonneg hnn

lemma oneAbs_side (j : ℕ) :
    ∑ k ∈ Finset.range (2 ^ (j + 1)),
        ((cascadeInt j ((2 : ℤ) ^ (j + 1) + (k : ℤ))).natAbs : ℤ) =
      sideMass j := by
  unfold sideMass sideSum
  have hpt : ∀ k ∈ Finset.range (2 ^ (j + 1)),
      ((cascadeInt j ((2 : ℤ) ^ (j + 1) + (k : ℤ))).natAbs : ℤ) =
        -cascadeInt j ((2 : ℤ) ^ (j + 1) + (k : ℤ)) := by
    intro k hk
    exact side_natAbs j k (Finset.mem_range.mp hk)
  rw [Finset.sum_congr rfl hpt, Finset.sum_neg_distrib]

lemma tail_natAbs {j : ℕ} (hj : 1 ≤ j) (k : ℕ) :
    ((cascadeInt j ((2 : ℤ) ^ (j + 2) + (k : ℤ))).natAbs : ℤ) =
      ((cascadeInt (j - 1) ((2 : ℤ) ^ j + (k : ℤ))).natAbs : ℤ) := by
  have hsum : (j - 1) + 1 = j := Nat.sub_add_cancel hj
  have hn : 4 * (2 : ℤ) ^ ((j - 1) + 1) - 2 ≤ (2 : ℤ) ^ (j + 2) + (k : ℤ) := by
    rw [hsum, two_pow_add_two j]
    have hk : (0 : ℤ) ≤ (k : ℤ) := Int.natCast_nonneg k
    linarith
  have htail := cascadeInt_tail (j - 1) hn
  rw [hsum] at htail
  have harg : (2 : ℤ) ^ (j + 2) + (k : ℤ) - 3 * (2 : ℤ) ^ j =
      (2 : ℤ) ^ j + (k : ℤ) := by
    rw [two_pow_add_two j]
    ring
  rw [htail, harg, Int.natAbs_neg]

def oneAbs (j : ℕ) : ℤ :=
  ∑ n ∈ Finset.range (cascadeRadius j + 1), ((cascadeInt j (n : ℤ)).natAbs : ℤ)

lemma cascadeRadius_split (j : ℕ) (hj : 1 ≤ j) :
    cascadeRadius j + 1 = 2 ^ (j + 2) + (2 ^ (j + 1) - 2) := by
  unfold cascadeRadius
  have hpow : 2 ^ (j + 2) = 2 * 2 ^ (j + 1) := by rw [pow_succ]; ring
  have hge : 2 ≤ 2 ^ (j + 1) := by
    have hle : 2 ^ 1 ≤ 2 ^ (j + 1) :=
      Nat.pow_le_pow_right (by decide : (1 : ℕ) ≤ 2) (by omega : 1 ≤ j + 1)
    simpa using hle
  rw [hpow]
  omega

lemma cascadeRadius_prev_split {j : ℕ} (hj : 1 ≤ j) :
    cascadeRadius (j - 1) + 1 = 2 ^ j + (2 ^ (j + 1) - 2) := by
  have hsum : (j - 1) + 1 = j := Nat.sub_add_cancel hj
  unfold cascadeRadius
  have hpow : 2 ^ (j + 1) = 2 * 2 ^ j := by rw [pow_succ]; ring
  have hge : 2 ≤ 2 ^ (j + 1) := by
    have hle : 2 ^ 1 ≤ 2 ^ (j + 1) :=
      Nat.pow_le_pow_right (by decide : (1 : ℕ) ≤ 2) (by omega : 1 ≤ j + 1)
    simpa using hle
  rw [hsum, hpow]
  omega

lemma nat_add_cast (a b : ℕ) : ((a + b : ℕ) : ℤ) = (a : ℤ) + (b : ℤ) := Nat.cast_add _ _

lemma oneAbs_zero_split : oneAbs 0 = centerSum 0 + sideMass 0 := by
  unfold oneAbs cascadeRadius
  have hlen : 3 * (2 ^ (0 + 1) - 1) + 1 = 2 ^ (0 + 1) + 2 ^ (0 + 1) := by decide
  rw [hlen, sum_range_add]
  have hcenter := oneAbs_center 0
  have hside := oneAbs_side 0
  have hidx : ∀ k, ((2 ^ (0 + 1) + k : ℕ) : ℤ) = (2 : ℤ) ^ (0 + 1) + (k : ℤ) := by
    intro k
    rw [nat_add_cast, Nat.cast_pow]
    simp
  have hside' : ∑ k ∈ Finset.range (2 ^ (0 + 1)),
      ((cascadeInt 0 (((2 ^ (0 + 1) + k : ℕ) : ℤ))).natAbs : ℤ) = sideMass 0 := by
    rw [Finset.sum_congr rfl (fun k _ => by rw [hidx k]), hside]
  rw [hcenter, hside']

lemma oneAbs_decompose {j : ℕ} (hj : 1 ≤ j) :
    oneAbs j = centerSum j + sideMass j + oneAbs (j - 1) - centerSum (j - 1) := by
  have hsum : (j - 1) + 1 = j := Nat.sub_add_cancel hj
  have hdouble : 2 ^ (j + 2) = 2 ^ (j + 1) + 2 ^ (j + 1) := by
    have hpow : 2 ^ (j + 2) = 2 * 2 ^ (j + 1) := by rw [pow_succ]; ring
    rw [hpow]
    ring
  unfold oneAbs
  rw [cascadeRadius_split j hj, sum_range_add, hdouble, sum_range_add]
  have hidxN : ∀ k, ((2 ^ (j + 1) + k : ℕ) : ℤ) = (2 : ℤ) ^ (j + 1) + (k : ℤ) := by
    intro k
    rw [nat_add_cast, Nat.cast_pow]
    simp
  have hside : ∑ k ∈ Finset.range (2 ^ (j + 1)),
      ((cascadeInt j (((2 ^ (j + 1) + k : ℕ) : ℤ))).natAbs : ℤ) = sideMass j := by
    rw [Finset.sum_congr rfl (fun k _ => by rw [hidxN k]), oneAbs_side j]
  have houter : ∑ k ∈ Finset.range (2 ^ (j + 1) - 2),
      ((cascadeInt j (((2 ^ (j + 1) + 2 ^ (j + 1) + k : ℕ) : ℤ))).natAbs : ℤ) =
      ∑ k ∈ Finset.range (2 ^ (j + 1) - 2),
        ((cascadeInt (j - 1) ((2 : ℤ) ^ j + (k : ℤ))).natAbs : ℤ) := by
    refine Finset.sum_congr rfl ?_
    intro k _
    have hidx : ((2 ^ (j + 1) + 2 ^ (j + 1) + k : ℕ) : ℤ) =
        (2 : ℤ) ^ (j + 2) + (k : ℤ) := by
      rw [← hdouble, nat_add_cast, Nat.cast_pow]
      simp
    rw [hidx, tail_natAbs hj k]
  have hprev : oneAbs (j - 1) =
      centerSum (j - 1) + ∑ k ∈ Finset.range (2 ^ (j + 1) - 2),
        ((cascadeInt (j - 1) ((2 : ℤ) ^ j + (k : ℤ))).natAbs : ℤ) := by
    unfold oneAbs
    rw [cascadeRadius_prev_split hj, sum_range_add]
    have hNp : 2 ^ ((j - 1) + 1) = 2 ^ j := by rw [hsum]
    have hcenter := oneAbs_center (j - 1)
    rw [hNp] at hcenter
    have hidxp : ∀ k, ((2 ^ j + k : ℕ) : ℤ) = (2 : ℤ) ^ j + (k : ℤ) := by
      intro k
      rw [nat_add_cast, Nat.cast_pow]
      simp
    rw [hcenter]
    have hrest : ∑ k ∈ Finset.range (2 ^ (j + 1) - 2),
        ((cascadeInt (j - 1) (((2 ^ j + k : ℕ) : ℤ))).natAbs : ℤ) =
        ∑ k ∈ Finset.range (2 ^ (j + 1) - 2),
          ((cascadeInt (j - 1) ((2 : ℤ) ^ j + (k : ℤ))).natAbs : ℤ) := by
      refine Finset.sum_congr rfl ?_
      intro k _
      rw [hidxp k]
    rw [hrest]
  have hraw : ∑ n ∈ Finset.range (cascadeRadius (j - 1) + 1),
      ((cascadeInt (j - 1) (n : ℤ)).natAbs : ℤ) =
      centerSum (j - 1) + ∑ k ∈ Finset.range (2 ^ (j + 1) - 2),
        ((cascadeInt (j - 1) ((2 : ℤ) ^ j + (k : ℤ))).natAbs : ℤ) := by
    simpa [oneAbs] using hprev
  rw [oneAbs_center j, hside, houter, hraw]
  ring

def absMass (j : ℕ) : ℤ :=
  2 * oneAbs j - cascadeInt j 0

lemma absMass_zero : absMass 0 = centerFull 0 + 2 * sideMass 0 := by
  unfold absMass centerFull
  rw [oneAbs_zero_split]
  ring

lemma absMass_step {j : ℕ} (hj : 1 ≤ j) :
    absMass j = centerFull j + 2 * sideMass j + absMass (j - 1) - centerFull (j - 1) := by
  unfold absMass centerFull
  rw [oneAbs_decompose hj]
  ring

def sideMassSum (j : ℕ) : ℤ :=
  ∑ i ∈ Finset.range (j + 1), sideMass i

lemma absMass_signed (j : ℕ) :
    absMass j = centerFull j + 2 * sideMassSum j := by
  induction j with
  | zero =>
    unfold sideMassSum
    rw [Finset.sum_range_one]
    exact absMass_zero
  | succ j ih =>
    have hj : 1 ≤ j + 1 := by omega
    unfold sideMassSum
    rw [absMass_step hj]
    have hsub : (j + 1) - 1 = j := by omega
    rw [hsub, ih, sideMassSum, Finset.sum_range_succ (fun i => sideMass i) (j + 1)]
    ring

lemma geom_sum_mul (x : ℤ) (n : ℕ) :
    (∑ i ∈ Finset.range n, x ^ i) * (x - 1) = x ^ n - 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, add_mul, ih, pow_succ]
    ring

lemma sideMassSum_closed (j : ℕ) :
    30 * sideMassSum j =
      44 * (∑ i ∈ Finset.range (j + 1), (32 : ℤ) ^ i)
        - 15 * ∑ i ∈ Finset.range (j + 1), (8 : ℤ) ^ i
        + ∑ i ∈ Finset.range (j + 1), (2 : ℤ) ^ i := by
  unfold sideMassSum
  induction j with
  | zero =>
    rw [Finset.sum_range_one, Finset.sum_range_one, Finset.sum_range_one, Finset.sum_range_one,
      sideMass_formula 0]
  | succ j ih =>
    rw [Finset.sum_range_succ (fun i => sideMass i) (j + 1),
      Finset.sum_range_succ (fun i => (32 : ℤ) ^ i) (j + 1),
      Finset.sum_range_succ (fun i => (8 : ℤ) ^ i) (j + 1),
      Finset.sum_range_succ (fun i => (2 : ℤ) ^ i) (j + 1)]
    have hstep : 30 * ((∑ i ∈ Finset.range (j + 1), sideMass i) + sideMass (j + 1)) =
        30 * ∑ i ∈ Finset.range (j + 1), sideMass i
          + (44 * (32 : ℤ) ^ (j + 1) - 15 * (8 : ℤ) ^ (j + 1) + (2 : ℤ) ^ (j + 1)) := by
      have hdist : 30 * ((∑ i ∈ Finset.range (j + 1), sideMass i) + sideMass (j + 1)) =
          30 * ∑ i ∈ Finset.range (j + 1), sideMass i + 30 * sideMass (j + 1) := by
        ring
      rw [hdist, sideMass_formula (j + 1)]
    rw [hstep, ih]
    ring

lemma absMass_closed (j : ℕ) :
    9765 * absMass j =
      4 * (92456 * (32 : ℤ) ^ j - 4960 * (8 : ℤ) ^ j + 434 * (2 : ℤ) ^ j - 45) := by
  rw [absMass_signed]
  have hsplit : (9765 : ℤ) * (centerFull j + 2 * sideMassSum j) =
      217 * (45 * centerFull j) + 651 * (30 * sideMassSum j) := by
    ring
  rw [hsplit, centerFull_formula, sideMassSum_closed]
  set S32 : ℤ := ∑ i ∈ Finset.range (j + 1), (32 : ℤ) ^ i
  set S8 : ℤ := ∑ i ∈ Finset.range (j + 1), (8 : ℤ) ^ i
  set S2 : ℤ := ∑ i ∈ Finset.range (j + 1), (2 : ℤ) ^ i
  have h32 := geom_sum_mul (32 : ℤ) (j + 1)
  have h8 := geom_sum_mul (8 : ℤ) (j + 1)
  have h2 := geom_sum_mul (2 : ℤ) (j + 1)
  have h32n : (32 : ℤ) - 1 = 31 := by norm_num
  have h8n : (8 : ℤ) - 1 = 7 := by norm_num
  have h2n : (2 : ℤ) - 1 = 1 := by norm_num
  rw [h32n] at h32
  rw [h8n] at h8
  rw [h2n] at h2
  have hS32 : 651 * S32 = 21 * ((32 : ℤ) ^ (j + 1) - 1) := by
    have hcoe : (651 : ℤ) = 21 * 31 := by norm_num
    calc
      651 * S32 = (21 * 31) * S32 := by rw [hcoe]
      _ = 21 * (S32 * 31) := by ring
      _ = 21 * ((32 : ℤ) ^ (j + 1) - 1) := by
            rw [show S32 * 31 = (32 : ℤ) ^ (j + 1) - 1 by simpa [S32] using h32]
  have hS8 : 651 * S8 = 93 * ((8 : ℤ) ^ (j + 1) - 1) := by
    have hcoe : (651 : ℤ) = 93 * 7 := by norm_num
    calc
      651 * S8 = (93 * 7) * S8 := by rw [hcoe]
      _ = 93 * (S8 * 7) := by ring
      _ = 93 * ((8 : ℤ) ^ (j + 1) - 1) := by
            rw [show S8 * 7 = (8 : ℤ) ^ (j + 1) - 1 by simpa [S8] using h8]
  have hS2 : S2 = (2 : ℤ) ^ (j + 1) - 1 := by
    simpa [S2] using h2
  have hlin : 651 * (44 * S32 - 15 * S8 + S2) =
      44 * (651 * S32) - 15 * (651 * S8) + 651 * S2 := by
    ring
  rw [hlin, hS32, hS8, hS2]
  simp only [pow_succ]
  ring

lemma sum_shift_reflect (R : ℕ) (f : ℤ → ℤ) :
    ∑ i ∈ Finset.range R, f ((i : ℤ) - (R : ℤ)) =
      ∑ t ∈ Finset.range R, f (-((t + 1 : ℕ) : ℤ)) := by
  induction R with
  | zero => simp
  | succ R ih =>
    rw [Finset.sum_range_succ' (fun i => f ((i : ℤ) - ((R + 1 : ℕ) : ℤ))),
      Finset.sum_range_succ (fun t => f (-((t + 1 : ℕ) : ℤ)))]
    have hfun : ∑ i ∈ Finset.range R,
        f (((i + 1 : ℕ) : ℤ) - ((R + 1 : ℕ) : ℤ)) =
        ∑ i ∈ Finset.range R, f ((i : ℤ) - (R : ℤ)) := by
      refine Finset.sum_congr rfl ?_
      intro i _
      have : ((i + 1 : ℕ) : ℤ) - ((R + 1 : ℕ) : ℤ) = (i : ℤ) - (R : ℤ) := by
        rw [Nat.cast_add, Nat.cast_add, Nat.cast_one]
        ring
      rw [this]
    rw [hfun, ih]
    have hz : ((0 : ℕ) : ℤ) - ((R + 1 : ℕ) : ℤ) = -((R + 1 : ℕ) : ℤ) := by
      simp only [Nat.cast_zero]
      ring
    rw [hz]

lemma oneAbs_reflect (j : ℕ) :
    ∑ i ∈ Finset.range (cascadeRadius j),
        ((cascadeInt j ((i : ℤ) - (cascadeRadius j : ℤ))).natAbs : ℤ) =
      oneAbs j - ((cascadeInt j 0).natAbs : ℤ) := by
  have hrefl := sum_shift_reflect (cascadeRadius j)
      (fun n => ((cascadeInt j n).natAbs : ℤ))
  have hsym : ∑ t ∈ Finset.range (cascadeRadius j),
      ((cascadeInt j (-((t + 1 : ℕ) : ℤ))).natAbs : ℤ) =
      ∑ t ∈ Finset.range (cascadeRadius j),
        ((cascadeInt j ((t + 1 : ℕ) : ℤ)).natAbs : ℤ) := by
    refine Finset.sum_congr rfl ?_
    intro t _
    rw [cascadeInt_symm]
  rw [hsym] at hrefl
  have htail : ∑ t ∈ Finset.range (cascadeRadius j),
      ((cascadeInt j ((t + 1 : ℕ) : ℤ)).natAbs : ℤ) =
      oneAbs j - ((cascadeInt j 0).natAbs : ℤ) := by
    have hsplit := Finset.sum_range_succ'
        (fun n => ((cascadeInt j (n : ℤ)).natAbs : ℤ)) (cascadeRadius j)
    unfold oneAbs
    rw [hsplit]
    ring
  rw [hrefl, htail]

lemma absMass_fin (j : ℕ) :
    (∑ i : Fin (cascadeSupport j),
        (cascadeInt j ((i.val : ℤ) - (cascadeRadius j : ℤ))).natAbs : ℤ) =
      absMass j := by
  suffices h : ∑ n ∈ Finset.range (cascadeSupport j),
      ((cascadeInt j ((n : ℤ) - (cascadeRadius j : ℤ))).natAbs : ℤ) = absMass j by
    rw [← Fin.sum_univ_eq_sum_range] at h
    exact h
  have hsupp : cascadeSupport j = cascadeRadius j + (cascadeRadius j + 1) := by
    unfold cascadeSupport
    ring
  rw [hsupp, sum_range_add]
  have hsecond : ∑ k ∈ Finset.range (cascadeRadius j + 1),
      ((cascadeInt j (((cascadeRadius j + k : ℕ) : ℤ) - (cascadeRadius j : ℤ))).natAbs : ℤ) =
      oneAbs j := by
    refine Finset.sum_congr rfl ?_
    intro k _
    have : ((cascadeRadius j + k : ℕ) : ℤ) - (cascadeRadius j : ℤ) = (k : ℤ) := by
      rw [Nat.cast_add]
      ring
    rw [this]
  rw [hsecond, oneAbs_reflect]
  unfold absMass
  have h0 : ((cascadeInt j 0).natAbs : ℤ) = cascadeInt j 0 :=
    center_natAbs j 0 (Nat.two_pow_pos _)
  rw [h0]
  ring

lemma absMass_real (j : ℕ) :
    (absMass j : ℝ) / (2 : ℝ) ^ (5 * (j + 1)) =
      ((92456 : ℝ) * (32 : ℝ) ^ j - (4960 : ℝ) * (8 : ℝ) ^ j
          + (434 : ℝ) * (2 : ℝ) ^ j - 45) /
        ((9765 : ℝ) * (2 : ℝ) ^ (5 * j + 3)) := by
  have hZ := absMass_closed j
  set P : ℝ := (92456 : ℝ) * (32 : ℝ) ^ j - (4960 : ℝ) * (8 : ℝ) ^ j
      + (434 : ℝ) * (2 : ℝ) ^ j - 45
  have hR : (9765 : ℝ) * (absMass j : ℝ) = 4 * P := by
    simpa [P] using (show (9765 : ℝ) * (absMass j : ℝ) =
      4 * ((92456 : ℝ) * (32 : ℝ) ^ j - (4960 : ℝ) * (8 : ℝ) ^ j
        + (434 : ℝ) * (2 : ℝ) ^ j - 45) by exact_mod_cast hZ)
  have hexp : 5 * (j + 1) = 2 + (5 * j + 3) := by omega
  have hpow : (2 : ℝ) ^ (5 * (j + 1)) = 4 * (2 : ℝ) ^ (5 * j + 3) := by
    rw [hexp, pow_add]
    norm_num
  have habs : (absMass j : ℝ) = 4 * P / 9765 := by
    rw [eq_div_iff (by norm_num : (9765 : ℝ) ≠ 0), mul_comm]
    exact hR
  rw [habs, hpow]
  field_simp

lemma cascade_l1_ratio (j : ℕ) :
    (absMass j : ℝ) / (cascadeScale j : ℝ) =
      ((92456 : ℝ) * (32 : ℝ) ^ j - (4960 : ℝ) * (8 : ℝ) ^ j
          + (434 : ℝ) * (2 : ℝ) ^ j - 45) /
        ((9765 : ℝ) * (2 : ℝ) ^ (5 * j + 3)) := by
  unfold cascadeScale
  simp only [Nat.cast_pow]
  exact absMass_real j

theorem cascade_l1_all (j N : ℕ) [NeZero N] (hN : cascadeSupport j ≤ N) :
    (∑ x : ZMod N, |cascadeKernel j N x|) =
      (absMass j : ℝ) / (cascadeScale j : ℝ) := by
  let num : ℕ := ∑ i : Fin (cascadeSupport j),
    (cascadeInt j ((i.val : ℤ) - (cascadeRadius j : ℤ))).natAbs
  have hnum : (num : ℤ) = absMass j := by
    simpa [num] using absMass_fin j
  have hker := cascadeKernel_l1 j N num (cascadeScale j) hN (by simp [num]) rfl
  rw [hker]
  have hcast : (num : ℝ) = (absMass j : ℝ) := by exact_mod_cast hnum
  rw [hcast]

theorem cascade_opNorm_all (j N d : ℕ) [NeZero N] (hN : cascadeSupport j ≤ N) :
    ‖cascadeOperator j N d‖ =
      ((absMass j : ℝ) / (cascadeScale j : ℝ)) ^ d := by
  unfold cascadeOperator
  rw [tensor_convolution_opNorm, cascade_l1_all j N hN]

theorem cascade_l1_closed_form (j N : ℕ) [NeZero N] (hN : cascadeSupport j ≤ N) :
    (∑ x : ZMod N, |cascadeKernel j N x|) =
      ((92456 : ℝ) * (32 : ℝ) ^ j - (4960 : ℝ) * (8 : ℝ) ^ j
          + (434 : ℝ) * (2 : ℝ) ^ j - 45) /
        ((9765 : ℝ) * (2 : ℝ) ^ (5 * j + 3)) := by
  rw [cascade_l1_all j N hN, cascade_l1_ratio j]

theorem cascade_opNorm_closed_form (j N d : ℕ) [NeZero N]
    (hN : cascadeSupport j ≤ N) :
    ‖cascadeOperator j N d‖ =
      (((92456 : ℝ) * (32 : ℝ) ^ j - (4960 : ℝ) * (8 : ℝ) ^ j
          + (434 : ℝ) * (2 : ℝ) ^ j - 45) /
        ((9765 : ℝ) * (2 : ℝ) ^ (5 * j + 3))) ^ d := by
  rw [cascade_opNorm_all j N d hN, cascade_l1_ratio j]

lemma cascade_l1_gap_formula (j : ℕ) :
    (1651 : ℝ) / 1395 - (absMass j : ℝ) / (cascadeScale j : ℝ) =
      ((4960 : ℝ) * (8 : ℝ) ^ j - (434 : ℝ) * (2 : ℝ) ^ j + 45) /
        ((9765 : ℝ) * (2 : ℝ) ^ (5 * j + 3)) := by
  have hL : (1651 : ℝ) / 1395 = (92456 : ℝ) / ((9765 : ℝ) * 8) := by norm_num
  have hpow : (2 : ℝ) ^ (5 * j + 3) = 8 * (32 : ℝ) ^ j := by
    rw [show (5 * j + 3) = 3 + 5 * j by omega, pow_add, pow_mul]
    norm_num
  rw [cascade_l1_ratio, hL, hpow]
  field_simp
  ring

lemma cascade_gap_num_pos (j : ℕ) :
    0 < (4960 : ℝ) * (8 : ℝ) ^ j - (434 : ℝ) * (2 : ℝ) ^ j + 45 := by
  have h8 : (2 : ℝ) ^ j ≤ (8 : ℝ) ^ j :=
    pow_le_pow_left₀ (by norm_num) (by norm_num) j
  have hmul : (434 : ℝ) * (2 : ℝ) ^ j ≤ 434 * (8 : ℝ) ^ j :=
    mul_le_mul_of_nonneg_left h8 (by norm_num)
  have hrest : 0 < (4526 : ℝ) * (8 : ℝ) ^ j + 45 := by positivity
  linarith

lemma cascade_gap_series (j : ℕ) :
    ((4 : ℝ) / 63) * ((1 : ℝ) / 4) ^ j
        - ((1 : ℝ) / 180) * ((1 : ℝ) / 16) ^ j
        + ((1 : ℝ) / 1736) * ((1 : ℝ) / 32) ^ j
      = ((4960 : ℝ) * (8 : ℝ) ^ j - (434 : ℝ) * (2 : ℝ) ^ j + 45) /
          ((9765 : ℝ) * (2 : ℝ) ^ (5 * j + 3)) := by
  set t : ℝ := (2 : ℝ) ^ j with ht
  have h4p : (4 : ℝ) ^ j = t ^ 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul,
      show (2 : ℕ) * j = j * 2 by omega, pow_mul, ← ht]
  have h8 : (8 : ℝ) ^ j = t ^ 3 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, ← pow_mul,
      show (3 : ℕ) * j = j * 3 by omega, pow_mul, ← ht]
  have h16 : (16 : ℝ) ^ j = t ^ 4 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, ← pow_mul,
      show (4 : ℕ) * j = j * 4 by omega, pow_mul, ← ht]
  have h32p : (32 : ℝ) ^ j = t ^ 5 := by
    rw [show (32 : ℝ) = 2 ^ 5 by norm_num, ← pow_mul,
      show (5 : ℕ) * j = j * 5 by omega, pow_mul, ← ht]
  have hdenp : (2 : ℝ) ^ (5 * j + 3) = 8 * t ^ 5 := by
    have hexp : 5 * j + 3 = 3 + j * 5 := by omega
    rw [hexp, pow_add, pow_mul, ← ht]
    norm_num
  rw [div_pow, div_pow, div_pow, h4p, h16, h32p, h8, hdenp]
  field_simp
  ring

lemma cascade_l1_series (j : ℕ) :
    (absMass j : ℝ) / (cascadeScale j : ℝ) =
      (1651 : ℝ) / 1395 - ((4 : ℝ) / 63) * ((1 : ℝ) / 4) ^ j
        + ((1 : ℝ) / 180) * ((1 : ℝ) / 16) ^ j
        - ((1 : ℝ) / 1736) * ((1 : ℝ) / 32) ^ j := by
  have h := cascade_l1_gap_formula j
  rw [← cascade_gap_series] at h
  linarith

lemma absMass_gap (j : ℕ) :
    0 < (1651 : ℝ) / 1395 - (absMass j : ℝ) / (cascadeScale j : ℝ) ∧
      (1651 : ℝ) / 1395 - (absMass j : ℝ) / (cascadeScale j : ℝ)
        ≤ ((4 : ℝ) / 63) * ((1 : ℝ) / 4) ^ j := by
  have hform := cascade_l1_gap_formula j
  refine ⟨?_, ?_⟩
  · rw [hform]
    exact div_pos (cascade_gap_num_pos j) (by positivity)
  · rw [hform, ← cascade_gap_series]
    have hpow : ((1 : ℝ) / 32) ^ j ≤ ((1 : ℝ) / 16) ^ j :=
      pow_le_pow_left₀ (by positivity) (by norm_num) j
    have hcoeff : (1 : ℝ) / 1736 ≤ (1 : ℝ) / 180 := by norm_num
    have hcmp : ((1 : ℝ) / 1736) * ((1 : ℝ) / 32) ^ j
        ≤ ((1 : ℝ) / 180) * ((1 : ℝ) / 16) ^ j :=
      mul_le_mul hcoeff hpow (by positivity) (by positivity)
    linarith

lemma absMass_succ_lt (j : ℕ) :
    (absMass j : ℝ) / (cascadeScale j : ℝ) <
      (absMass (j + 1) : ℝ) / (cascadeScale (j + 1) : ℝ) := by
  have hgap := cascade_l1_gap_formula j
  have hgap1 := cascade_l1_gap_formula (j + 1)
  suffices (1651 : ℝ) / 1395 - (absMass (j + 1) : ℝ) / (cascadeScale (j + 1) : ℝ) <
      (1651 : ℝ) / 1395 - (absMass j : ℝ) / (cascadeScale j : ℝ) by
    linarith
  rw [hgap, hgap1]
  have hpow : (2 : ℝ) ^ (5 * (j + 1) + 3) = 32 * (2 : ℝ) ^ (5 * j + 3) := by
    have hexp : 5 * (j + 1) + 3 = 5 + (5 * j + 3) := by omega
    rw [hexp, pow_add]
    norm_num
  have hden : 0 < (9765 : ℝ) * (2 : ℝ) ^ (5 * j + 3) := by positivity
  rw [hpow]
  have hassoc : (9765 : ℝ) * (32 * (2 : ℝ) ^ (5 * j + 3))
      = 32 * ((9765 : ℝ) * (2 : ℝ) ^ (5 * j + 3)) := by ring
  rw [hassoc, div_lt_div_iff₀ (mul_pos (by norm_num) hden) hden]
  have h8 : (8 : ℝ) ^ (j + 1) = 8 * (8 : ℝ) ^ j := by
    rw [pow_succ]
    ring
  have h2 : (2 : ℝ) ^ (j + 1) = 2 * (2 : ℝ) ^ j := by
    rw [pow_succ]
    ring
  have hstep : (4960 : ℝ) * (8 : ℝ) ^ (j + 1) - (434 : ℝ) * (2 : ℝ) ^ (j + 1) + 45 <
      32 * ((4960 : ℝ) * (8 : ℝ) ^ j - (434 : ℝ) * (2 : ℝ) ^ j + 45) := by
    rw [h8, h2]
    have hid : 32 * ((4960 : ℝ) * (8 : ℝ) ^ j - (434 : ℝ) * (2 : ℝ) ^ j + 45)
        - ((4960 : ℝ) * 8 * (8 : ℝ) ^ j - (434 : ℝ) * 2 * (2 : ℝ) ^ j + 45)
        = (119040 : ℝ) * (8 : ℝ) ^ j - (13020 : ℝ) * (2 : ℝ) ^ j + 1395 := by
      ring
    have h8ge : (2 : ℝ) ^ j ≤ (8 : ℝ) ^ j :=
      pow_le_pow_left₀ (by norm_num) (by norm_num) j
    have hlow : (106020 : ℝ) * (8 : ℝ) ^ j + 1395 ≤
        (119040 : ℝ) * (8 : ℝ) ^ j - (13020 : ℝ) * (2 : ℝ) ^ j + 1395 := by
      linarith
    have hpos : 0 < (106020 : ℝ) * (8 : ℝ) ^ j + 1395 := by positivity
    linarith [hid, hlow, hpos]
  have hmul := mul_lt_mul_of_pos_right hstep hden
  have hcomm : (32 * ((4960 : ℝ) * (8 : ℝ) ^ j - (434 : ℝ) * (2 : ℝ) ^ j + 45)) *
        ((9765 : ℝ) * (2 : ℝ) ^ (5 * j + 3))
      = ((4960 : ℝ) * (8 : ℝ) ^ j - (434 : ℝ) * (2 : ℝ) ^ j + 45) *
        (32 * ((9765 : ℝ) * (2 : ℝ) ^ (5 * j + 3))) := by ring
  linarith [hmul, hcomm]

lemma absMass_tendsto :
    Filter.Tendsto (fun j : ℕ => (absMass j : ℝ) / (cascadeScale j : ℝ))
      Filter.atTop (nhds ((1651 : ℝ) / 1395)) := by
  have h4 := tendsto_pow_atTop_nhds_zero_of_lt_one
    (show (0 : ℝ) ≤ (1 : ℝ) / 4 by norm_num) (show (1 : ℝ) / 4 < 1 by norm_num)
  have h16 := tendsto_pow_atTop_nhds_zero_of_lt_one
    (show (0 : ℝ) ≤ (1 : ℝ) / 16 by norm_num) (show (1 : ℝ) / 16 < 1 by norm_num)
  have h32 := tendsto_pow_atTop_nhds_zero_of_lt_one
    (show (0 : ℝ) ≤ (1 : ℝ) / 32 by norm_num) (show (1 : ℝ) / 32 < 1 by norm_num)
  have hlim :
      Filter.Tendsto
        (fun j : ℕ =>
          (1651 : ℝ) / 1395 - ((4 : ℝ) / 63) * ((1 : ℝ) / 4) ^ j
            + ((1 : ℝ) / 180) * ((1 : ℝ) / 16) ^ j
            - ((1 : ℝ) / 1736) * ((1 : ℝ) / 32) ^ j)
        Filter.atTop
        (nhds ((1651 : ℝ) / 1395 - ((4 : ℝ) / 63) * 0
          + ((1 : ℝ) / 180) * 0 - ((1 : ℝ) / 1736) * 0)) :=
    (((tendsto_const_nhds.sub (tendsto_const_nhds.mul h4)).add
        (tendsto_const_nhds.mul h16)).sub (tendsto_const_nhds.mul h32))
  have hzero : (1651 : ℝ) / 1395 - ((4 : ℝ) / 63) * 0 + ((1 : ℝ) / 180) * 0
      - ((1 : ℝ) / 1736) * 0 = (1651 : ℝ) / 1395 := by ring
  rw [hzero] at hlim
  exact hlim.congr fun j => (cascade_l1_series j).symm

lemma free_l1 (j : ℕ) :
    (∑ i : Fin (cascadeSupport j), |cascadeTap j i|) =
      (absMass j : ℝ) / (cascadeScale j : ℝ) := by
  let num : ℕ := ∑ i : Fin (cascadeSupport j),
    (cascadeInt j ((i.val : ℤ) - (cascadeRadius j : ℤ))).natAbs
  have hnum : (num : ℤ) = absMass j := by
    simpa [num] using absMass_fin j
  have htaps := cascadeTap_l1 j num (cascadeScale j) (by simp [num]) rfl
  have hcast : (num : ℝ) = (absMass j : ℝ) := by exact_mod_cast hnum
  rw [htaps, hcast]

theorem cascade_l1_gap (j : ℕ) :
    0 < (1651 : ℝ) / 1395 - (∑ i : Fin (cascadeSupport j), |cascadeTap j i|) ∧
      (1651 : ℝ) / 1395 - (∑ i : Fin (cascadeSupport j), |cascadeTap j i|)
        ≤ ((4 : ℝ) / 63) * ((1 : ℝ) / 4) ^ j := by
  rw [free_l1]
  exact absMass_gap j

theorem cascade_l1_succ_lt (j : ℕ) :
    (∑ i : Fin (cascadeSupport j), |cascadeTap j i|) <
      ∑ i : Fin (cascadeSupport (j + 1)), |cascadeTap (j + 1) i| := by
  rw [free_l1, free_l1]
  exact absMass_succ_lt j

theorem cascade_l1_tendsto :
    Filter.Tendsto (fun j : ℕ => ∑ i : Fin (cascadeSupport j), |cascadeTap j i|)
      Filter.atTop (nhds ((1651 : ℝ) / 1395)) := by
  exact absMass_tendsto.congr fun j => (free_l1 j).symm

theorem cascade_l1_formula (j N : ℕ) [NeZero N] (hN : cascadeSupport j ≤ N) :
    (∑ x : ZMod N, |cascadeKernel j N x|) =
      (1651 : ℝ) / 1395 - ((4 : ℝ) / 63) * ((1 : ℝ) / 4) ^ j
        + ((1 : ℝ) / 180) * ((1 : ℝ) / 16) ^ j
        - ((1 : ℝ) / 1736) * ((1 : ℝ) / 32) ^ j := by
  rw [cascade_l1_all j N hN, cascade_l1_series j]

theorem cascade_opNorm_formula (j N d : ℕ) [NeZero N]
    (hN : cascadeSupport j ≤ N) :
    ‖cascadeOperator j N d‖ =
      ((1651 : ℝ) / 1395 - ((4 : ℝ) / 63) * ((1 : ℝ) / 4) ^ j
        + ((1 : ℝ) / 180) * ((1 : ℝ) / 16) ^ j
        - ((1 : ℝ) / 1736) * ((1 : ℝ) / 32) ^ j) ^ d := by
  rw [cascade_opNorm_all j N d hN, cascade_l1_series j]

lemma cascade_opNorm_le_level (j N d : ℕ) [NeZero N] :
    ‖cascadeOperator j N d‖ ≤
      ((absMass j : ℝ) / (cascadeScale j : ℝ)) ^ d := by
  unfold cascadeOperator
  rw [tensor_convolution_opNorm]
  let num : ℕ := ∑ i : Fin (cascadeSupport j),
    (cascadeInt j ((i.val : ℤ) - (cascadeRadius j : ℤ))).natAbs
  have hnum : (num : ℤ) = absMass j := by
    simpa [num] using absMass_fin j
  have htaps := cascadeTap_l1 j num (cascadeScale j) (by simp [num]) rfl
  have hcast : (num : ℝ) = (absMass j : ℝ) := by exact_mod_cast hnum
  have hbase : (∑ x : ZMod N, |cascadeKernel j N x|) ≤
      (absMass j : ℝ) / (cascadeScale j : ℝ) := by
    simp only [cascadeKernel]
    calc
      (∑ x : ZMod N, |foldKernel (cascadeTap j) (cascadeOffset j N) x|)
          ≤ ∑ i : Fin (cascadeSupport j), |cascadeTap j i| :=
        foldKernel_l1_le (cascadeTap j) (cascadeOffset j N)
      _ = (num : ℝ) / (cascadeScale j : ℝ) := htaps
      _ = (absMass j : ℝ) / (cascadeScale j : ℝ) := by rw [hcast]
  have hnn : 0 ≤ ∑ x : ZMod N, |cascadeKernel j N x| :=
    Finset.sum_nonneg fun _ _ => abs_nonneg _
  exact pow_le_pow_left₀ hnn hbase d

theorem cascade_opNorm_uniform (j N d : ℕ) [NeZero N] :
    ‖cascadeOperator j N d‖ ≤ ((1651 : ℝ) / 1395) ^ d := by
  have hlevel := cascade_opNorm_le_level j N d
  have hlt : (absMass j : ℝ) / (cascadeScale j : ℝ) < (1651 : ℝ) / 1395 := by
    have hgap := (absMass_gap j).1
    linarith
  have hnnZ : 0 ≤ absMass j := by
    rw [← absMass_fin j]
    exact Finset.sum_nonneg fun i _ =>
      Nat.cast_nonneg ((cascadeInt j ((i.val : ℤ) - (cascadeRadius j : ℤ))).natAbs)
  have hnn : 0 ≤ (absMass j : ℝ) / (cascadeScale j : ℝ) :=
    div_nonneg (Int.cast_nonneg hnnZ) (Nat.cast_nonneg (cascadeScale j))
  exact hlevel.trans (pow_le_pow_left₀ hnn hlt.le d)

/-- For each fixed dimension, `L^d` with `L = 1651/1395` is a lower bound on
every common upper bound of the cascade operators. The period `N` may grow
with the level. This does not say that one fixed `N` attains `L^d`. At `d = 0`
both sides are `1`. -/
theorem cascade_uniform_constant_least (d : ℕ) {B : ℝ}
    (hB : ∀ j N : ℕ, (hN : NeZero N) → ‖cascadeOperator j N d‖ ≤ B) :
    ((1651 : ℝ) / 1395) ^ d ≤ B := by
  have hpow := (continuous_pow d).tendsto ((1651 : ℝ) / 1395) |>.comp absMass_tendsto
  have hle : ∀ j, ((absMass j : ℝ) / (cascadeScale j : ℝ)) ^ d ≤ B := by
    intro j
    have hne : NeZero (cascadeSupport j) := ⟨by
      unfold cascadeSupport
      omega⟩
    have hnorm := hB j (cascadeSupport j) hne
    rw [cascade_opNorm_all j (cascadeSupport j) d le_rfl] at hnorm
    exact hnorm
  exact le_of_tendsto' hpow hle

/-- At dimension zero the separable convolution is the identity on a one-point
space, so the operator norm is 1 for every level and every positive period. -/
theorem cascade_opNorm_d_zero (j N : ℕ) [NeZero N] :
    ‖cascadeOperator j N 0‖ = 1 := by
  unfold cascadeOperator
  rw [tensor_convolution_opNorm, pow_zero]

end
end TWSPeriodic
