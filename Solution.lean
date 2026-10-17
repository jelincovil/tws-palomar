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

end
end TWSPeriodic
