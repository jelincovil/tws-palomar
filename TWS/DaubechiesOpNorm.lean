import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic

/-!
# Exact `ℓ¹` norm of the undecimated db2 approximation kernel

Certificate for the paper's Proposition: the one-dimensional level-1
undecimated D4 / db2 kernel is `½ R_h = [-1,0,9,16,9,0,-1]/32`, with
`ℓ¹` norm `9/8`, and the separable two-dimensional row-sum norm is
`(9/8)^2`. The QMF identities for the orthonormal db2 low-pass filter
are closed below.

This does not formalize bottleneck stability or landscapes.
-/

namespace TWS
namespace Daubechies

open Real Finset

/-! ## Rational kernel (half autocorrelation) -/

/-- Taps of `½ R_h` on `{-3,-2,-1,0,1,2,3}`. -/
def kernel1d : Fin 7 → ℚ
  | ⟨0, _⟩ => -1 / 32
  | ⟨1, _⟩ => 0
  | ⟨2, _⟩ => 9 / 32
  | ⟨3, _⟩ => 16 / 32
  | ⟨4, _⟩ => 9 / 32
  | ⟨5, _⟩ => 0
  | ⟨6, _⟩ => -1 / 32

theorem kernel1d_l1 :
    ∑ i : Fin 7, |kernel1d i| = (9 : ℚ) / 8 := by
  simp [kernel1d, Fin.sum_univ_succ]
  norm_num

theorem kernel1d_l1_real :
    ∑ i : Fin 7, |(kernel1d i : ℝ)| = (9 : ℝ) / 8 := by
  trans ((∑ i : Fin 7, |kernel1d i| : ℚ) : ℝ)
  · simp [Rat.cast_abs]
  · rw [kernel1d_l1]; norm_num

/-! ## Tensorization of row-sum (`ℓ¹`) norms -/

theorem outer_l1 {n : ℕ} (v : Fin n → ℝ) :
    ∑ i : Fin n, ∑ j : Fin n, |v i * v j| = (∑ i : Fin n, |v i|) ^ 2 := by
  simp_rw [abs_mul]
  calc
    ∑ i : Fin n, ∑ j : Fin n, |v i| * |v j|
        = ∑ i : Fin n, |v i| * ∑ j : Fin n, |v j| := by
          simp [mul_sum]
    _ = (∑ i : Fin n, |v i|) * (∑ j : Fin n, |v j|) := by
          simp [sum_mul]
    _ = (∑ i : Fin n, |v i|) ^ 2 := by ring

theorem db2_level1_opnorm_d2 :
    ∑ i : Fin 7, ∑ j : Fin 7, |((kernel1d i : ℝ) * (kernel1d j : ℝ))| =
      ((9 : ℝ) / 8) ^ 2 := by
  rw [outer_l1 (fun i : Fin 7 => (kernel1d i : ℝ)), kernel1d_l1_real]

theorem db2_level1_opnorm_d2_num :
    ((9 : ℝ) / 8) ^ 2 = 81 / 64 := by
  norm_num

/-! ## QMF expansion of the orthonormal db2 low-pass filter -/

noncomputable def c : ℝ := 1 / (4 * sqrt 2)

lemma c_sq : c ^ 2 = 1 / 32 := by
  unfold c
  have ht : (4 * sqrt 2) ^ 2 = (32 : ℝ) := by
    rw [mul_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  field_simp
  rw [← mul_pow]
  exact ht.symm

noncomputable def h : ℕ → ℝ
  | 0 => c * (1 + sqrt 3)
  | 1 => c * (3 + sqrt 3)
  | 2 => c * (3 - sqrt 3)
  | 3 => c * (1 - sqrt 3)
  | _ => 0

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

/-- Autocorrelation of `h` at nonnegative lag `k`. -/
noncomputable def autocorr (k : ℕ) : ℝ :=
  ∑ n ∈ range 4, h n * h (n + k)

theorem autocorr_zero : autocorr 0 = 1 := by
  unfold autocorr
  simp [sum_range_succ]
  simpa [pow_two] using R0

theorem autocorr_one : autocorr 1 = (9 : ℝ) / 16 := by
  unfold autocorr
  simp [sum_range_succ, h]
  -- n+1 for n=3 is h 4 = 0
  simpa [h] using R1

theorem autocorr_two : autocorr 2 = 0 := by
  unfold autocorr
  simp [sum_range_succ, h]
  simpa [h] using R2

theorem autocorr_three : autocorr 3 = (-1 : ℝ) / 16 := by
  unfold autocorr
  simp [sum_range_succ, h]
  simpa [h] using R3

/-- Half-autocorrelation `ℓ¹` (even kernel) equals `9/8`. -/
theorem half_autocorr_l1 :
    |autocorr 3 / 2| + |autocorr 2 / 2| + |autocorr 1 / 2| + |autocorr 0 / 2| +
      |autocorr 1 / 2| + |autocorr 2 / 2| + |autocorr 3 / 2| = (9 : ℝ) / 8 := by
  rw [autocorr_zero, autocorr_one, autocorr_two, autocorr_three]
  norm_num

end Daubechies
end TWS
