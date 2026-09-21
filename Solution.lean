import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Rat.Cast.Order
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic

/-!
# Solution — closed proofs (Mathlib-only)

Same inlined definitions as `Challenge.lean`; closed proofs for the
seven compared declarations. Import closure contains only Lean core
and Mathlib.

Proof tactics are adapted from the companion `TWS.DaubechiesOpNorm`
and `TWS.Skeleton` developments (vendored under `TWS/`).
-/

open Finset Real
open scoped BigOperators

namespace Palomar

/-! ## Inlined definitions (identical to Challenge.lean) -/

def kernel1d : Fin 7 → ℚ
  | ⟨0, _⟩ => -1 / 32
  | ⟨1, _⟩ => 0
  | ⟨2, _⟩ => 9 / 32
  | ⟨3, _⟩ => 16 / 32
  | ⟨4, _⟩ => 9 / 32
  | ⟨5, _⟩ => 0
  | ⟨6, _⟩ => -1 / 32

noncomputable def c : ℝ := 1 / (4 * sqrt 2)

noncomputable def h : ℕ → ℝ
  | 0 => c * (1 + sqrt 3)
  | 1 => c * (3 + sqrt 3)
  | 2 => c * (3 - sqrt 3)
  | 3 => c * (1 - sqrt 3)
  | _ => 0

noncomputable def autocorr (k : ℕ) : ℝ :=
  ∑ n ∈ range 4, h n * h (n + k)

noncomputable def L2Norm (g : ℝ → ℝ) (U : Set ℝ) : ℝ :=
  (MeasureTheory.eLpNorm (U.indicator g) 2).toReal

/-! ## Helper lemmas -/

lemma c_sq : c ^ 2 = 1 / 32 := by
  unfold c
  have ht : (4 * sqrt 2) ^ 2 = (32 : ℝ) := by
    rw [mul_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  field_simp
  rw [← mul_pow]
  exact ht.symm

lemma h0 : h 0 = c * (1 + sqrt 3) := by simp [h]
lemma h1 : h 1 = c * (3 + sqrt 3) := by simp [h]
lemma h2 : h 2 = c * (3 - sqrt 3) := by simp [h]
lemma h3 : h 3 = c * (1 - sqrt 3) := by simp [h]

lemma R3 : h 0 * h 3 = (-1 : ℝ) / 16 := by
  rw [h0, h3]
  have : c * (1 + sqrt 3) * (c * (1 - sqrt 3)) = c ^ 2 * (1 - (sqrt 3) ^ 2) := by ring
  rw [this, c_sq, sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  norm_num

lemma R2 : h 0 * h 2 + h 1 * h 3 = 0 := by
  rw [h0, h1, h2, h3]
  have : (1 + sqrt 3) * (3 - sqrt 3) + (3 + sqrt 3) * (1 - sqrt 3) = 0 := by
    ring_nf
    rw [sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    ring
  have hfac :
      c * (1 + sqrt 3) * (c * (3 - sqrt 3)) + c * (3 + sqrt 3) * (c * (1 - sqrt 3)) =
        c ^ 2 * ((1 + sqrt 3) * (3 - sqrt 3) + (3 + sqrt 3) * (1 - sqrt 3)) := by
    ring
  rw [hfac, this]
  ring

lemma R1 : h 0 * h 1 + h 1 * h 2 + h 2 * h 3 = (9 : ℝ) / 16 := by
  rw [h0, h1, h2, h3]
  have h18 :
      (1 + sqrt 3) * (3 + sqrt 3) + (3 + sqrt 3) * (3 - sqrt 3) +
        (3 - sqrt 3) * (1 - sqrt 3) = 18 := by
    ring_nf
    rw [sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    ring
  have hfac :
      c * (1 + sqrt 3) * (c * (3 + sqrt 3)) + c * (3 + sqrt 3) * (c * (3 - sqrt 3)) +
        c * (3 - sqrt 3) * (c * (1 - sqrt 3)) =
        c ^ 2 * ((1 + sqrt 3) * (3 + sqrt 3) + (3 + sqrt 3) * (3 - sqrt 3) +
          (3 - sqrt 3) * (1 - sqrt 3)) := by
    ring
  calc
    c * (1 + sqrt 3) * (c * (3 + sqrt 3)) +
        c * (3 + sqrt 3) * (c * (3 - sqrt 3)) +
        c * (3 - sqrt 3) * (c * (1 - sqrt 3))
        = c ^ 2 * 18 := by rw [hfac, h18]
    _ = (1 / 32) * 18 := by rw [c_sq]
    _ = 9 / 16 := by norm_num

lemma R0 : h 0 ^ 2 + h 1 ^ 2 + h 2 ^ 2 + h 3 ^ 2 = 1 := by
  rw [h0, h1, h2, h3]
  have h32 :
      (1 + sqrt 3) ^ 2 + (3 + sqrt 3) ^ 2 + (3 - sqrt 3) ^ 2 + (1 - sqrt 3) ^ 2 = 32 := by
    ring_nf
    rw [sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    ring
  have hfac :
      (c * (1 + sqrt 3)) ^ 2 + (c * (3 + sqrt 3)) ^ 2 + (c * (3 - sqrt 3)) ^ 2 +
        (c * (1 - sqrt 3)) ^ 2 =
        c ^ 2 * ((1 + sqrt 3) ^ 2 + (3 + sqrt 3) ^ 2 + (3 - sqrt 3) ^ 2 +
          (1 - sqrt 3) ^ 2) := by
    ring
  calc
    (c * (1 + sqrt 3)) ^ 2 + (c * (3 + sqrt 3)) ^ 2 + (c * (3 - sqrt 3)) ^ 2 +
        (c * (1 - sqrt 3)) ^ 2
        = c ^ 2 * 32 := by rw [hfac, h32]
    _ = (1 / 32) * 32 := by rw [c_sq]
    _ = 1 := by norm_num

lemma autocorr_zero : autocorr 0 = 1 := by
  unfold autocorr
  simp [sum_range_succ]
  simpa [pow_two] using R0

lemma autocorr_one : autocorr 1 = (9 : ℝ) / 16 := by
  unfold autocorr
  simp [sum_range_succ, h]
  simpa [h] using R1

lemma autocorr_two : autocorr 2 = 0 := by
  unfold autocorr
  simp [sum_range_succ, h]
  simpa [h] using R2

lemma autocorr_three : autocorr 3 = (-1 : ℝ) / 16 := by
  unfold autocorr
  simp [sum_range_succ, h]
  simpa [h] using R3

/-! ## Proofs -/

theorem kernel1d_l1 :
    ∑ i : Fin 7, |kernel1d i| = (9 : ℚ) / 8 := by
  simp [kernel1d, Fin.sum_univ_succ]
  norm_num

theorem kernel1d_l1_real :
    ∑ i : Fin 7, |(kernel1d i : ℝ)| = (9 : ℝ) / 8 := by
  trans ((∑ i : Fin 7, |kernel1d i| : ℚ) : ℝ)
  · simp [Rat.cast_abs]
  · rw [kernel1d_l1]; norm_num

theorem outer_l1 {n : ℕ} (v : Fin n → ℝ) :
    ∑ i : Fin n, ∑ j : Fin n, |v i * v j| = (∑ i : Fin n, |v i|) ^ 2 := by
  simp_rw [abs_mul]
  calc
    ∑ i : Fin n, ∑ j : Fin n, |v i| * |v j|
        = ∑ i : Fin n, |v i| * ∑ j : Fin n, |v j| := by simp [mul_sum]
    _ = (∑ i : Fin n, |v i|) * (∑ j : Fin n, |v j|) := by simp [sum_mul]
    _ = (∑ i : Fin n, |v i|) ^ 2 := by ring

theorem db2_level1_opnorm_d2 :
    ∑ i : Fin 7, ∑ j : Fin 7, |((kernel1d i : ℝ) * (kernel1d j : ℝ))| =
      ((9 : ℝ) / 8) ^ 2 := by
  rw [outer_l1 (fun i : Fin 7 => (kernel1d i : ℝ)), kernel1d_l1_real]

theorem db2_level1_opnorm_d2_num :
    ((9 : ℝ) / 8) ^ 2 = 81 / 64 := by
  norm_num

theorem half_autocorr_l1 :
    |autocorr 3 / 2| + |autocorr 2 / 2| + |autocorr 1 / 2| + |autocorr 0 / 2| +
      |autocorr 1 / 2| + |autocorr 2 / 2| + |autocorr 3 / 2| = (9 : ℝ) / 8 := by
  rw [autocorr_zero, autocorr_one, autocorr_two, autocorr_three]
  norm_num

theorem l2_norm_rev_tri (f g : ℝ → ℝ) (U : Set ℝ)
    (hf : MeasureTheory.MemLp (U.indicator f) 2)
    (hg : MeasureTheory.MemLp (U.indicator g) 2) :
    |L2Norm f U - L2Norm g U| ≤ L2Norm (fun t => f t - g t) U := by
  unfold L2Norm
  have hsub : U.indicator (fun t => f t - g t) = U.indicator f - U.indicator g := by
    ext t
    by_cases ht : t ∈ U <;> simp [Set.indicator, ht]
  rw [hsub]
  rw [← MeasureTheory.Lp.norm_toLp (U.indicator f) hf,
      ← MeasureTheory.Lp.norm_toLp (U.indicator g) hg,
      ← MeasureTheory.Lp.norm_toLp (U.indicator f - U.indicator g) (hf.sub hg)]
  rw [MeasureTheory.MemLp.toLp_sub hf hg]
  exact abs_norm_sub_norm_le _ _

theorem energy_stability (a b Γ : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : |a - b| ≤ Γ) :
    |a ^ 2 - b ^ 2| ≤ Γ * (a + b) := by
  have hfactor : a ^ 2 - b ^ 2 = (a - b) * (a + b) := by ring
  have hab : 0 ≤ a + b := by linarith
  calc
    |a ^ 2 - b ^ 2| = |(a - b) * (a + b)| := by rw [hfactor]
    _ = |a - b| * |a + b| := abs_mul _ _
    _ = |a - b| * (a + b) := by rw [abs_of_nonneg hab]
    _ ≤ Γ * (a + b) := by gcongr

end Palomar
