module

public import ThresholdExtension.NonperiodicDb2Certificate

/-!
# Conservation of constants for the endpoint-replicated db2 cascade

This module closes the last mathematical obligation of the threshold-certificate phase:

* `cascadeTap_sum_one`: the **signed** sum of the level-`j` taps is `1`, for every `j`;
* `directOp_const`: `directOp j n` fixes constant signals, for every `j` and every `n ≥ 1`;
* `directOp_one_eq_id`: at `n = 1` the operator is the identity, for every `j`.

The signed sum is not the `ℓ¹` mass `c_j`: the latter is the sum of absolute values and is
strictly larger than `1` in general.  The proof below works with the integer numerators
`cascadeInt j` and never uses the absolute-value bounds.

Route.  `cascadeInt j` is supported in `[-r_j, r_j]` (`cascadeInt_vanish`) and satisfies the
five-tap recurrence with weights `16, 9, 9, -1, -1`, whose sum is `32`.  Summing the
recurrence over the symmetric interval and reindexing each of the five shifted copies (a
finite translation, valid because the support stays inside the interval) gives
`∑ cascadeInt (j+1) = 32 * ∑ cascadeInt j`, and `cascadeScale (j+1) = 32 * cascadeScale j`.
The base case is `16 + 9 + 9 - 1 - 1 = 32 = cascadeScale 0`.  Dividing by the positive
scale and reindexing `Fin s → [-r, r]` yields the tap sum.
-/

@[expose] public section

open TWSPeriodic

namespace ThresholdCert.Nonperiodic

/-! ## Integer mass of the free cascade kernel -/

private lemma cascadeScale_succ (j : ℕ) : cascadeScale (j + 1) = 32 * cascadeScale j := by
  unfold cascadeScale
  rw [show 5 * (j + 1 + 1) = 5 * (j + 1) + 5 by ring, pow_add]
  ring

/-- Finite translation of a sum over a symmetric integer interval. -/
private lemma sum_Icc_shift (F : ℤ → ℤ) (R' d : ℤ) :
    ∑ n ∈ Finset.Icc (-R') R', F (n - d) = ∑ m ∈ Finset.Icc (-R' - d) (R' - d), F m := by
  refine Finset.sum_bij (fun n _ => n - d) ?_ ?_ ?_ ?_
  · intro n hn
    simp only [Finset.mem_Icc] at hn ⊢
    omega
  · intro n₁ _ n₂ _ h
    omega
  · intro m hm
    exact ⟨m + d, by simp only [Finset.mem_Icc] at hm ⊢; omega, by ring⟩
  · intro n _
    rfl

/-- Shrinking an interval to the true support of `cascadeInt j`. -/
private lemma sum_Icc_shrink (j : ℕ) {a b : ℤ}
    (h1 : a ≤ -(cascadeRadius j : ℤ)) (h2 : (cascadeRadius j : ℤ) ≤ b) :
    ∑ m ∈ Finset.Icc a b, cascadeInt j m
      = ∑ m ∈ Finset.Icc (-(cascadeRadius j : ℤ)) (cascadeRadius j : ℤ), cascadeInt j m := by
  refine (Finset.sum_subset ?_ ?_).symm
  · intro m hm
    simp only [Finset.mem_Icc] at hm ⊢
    omega
  · intro m _ hm
    apply cascadeInt_vanish
    have h : (cascadeRadius j : ℤ) < (m.natAbs : ℤ) := by
      rw [Int.natCast_natAbs]
      simp only [Finset.mem_Icc, not_and_or, not_le] at hm
      rcases hm with hm | hm
      · rw [abs_of_neg (by omega)]
        omega
      · rw [abs_of_pos (by omega)]
        omega
    exact_mod_cast h

/-- Sum of one shifted copy of the kernel over the next-level interval. -/
private lemma sum_shifted (j : ℕ) (d : ℤ)
    (hd1 : -3 * 2 ^ (j + 1) ≤ d) (hd2 : d ≤ 3 * 2 ^ (j + 1)) :
    ∑ n ∈ Finset.Icc (-((cascadeRadius j : ℤ) + 3 * 2 ^ (j + 1)))
        ((cascadeRadius j : ℤ) + 3 * 2 ^ (j + 1)), cascadeInt j (n - d)
      = ∑ m ∈ Finset.Icc (-(cascadeRadius j : ℤ)) (cascadeRadius j : ℤ), cascadeInt j m := by
  have hp : (0 : ℤ) < 2 ^ (j + 1) := by positivity
  rw [sum_Icc_shift (cascadeInt j) ((cascadeRadius j : ℤ) + 3 * 2 ^ (j + 1)) d]
  exact sum_Icc_shrink j (by omega) (by omega)

/-- Inductive step: the integer mass is multiplied by `32` at each cascade level. -/
private lemma cascadeInt_sum_succ (j : ℕ)
    (ih : ∑ n ∈ Finset.Icc (-(cascadeRadius j : ℤ)) (cascadeRadius j : ℤ), cascadeInt j n
      = (cascadeScale j : ℤ)) :
    ∑ n ∈ Finset.Icc (-(cascadeRadius (j + 1) : ℤ)) (cascadeRadius (j + 1) : ℤ),
        cascadeInt (j + 1) n
      = (cascadeScale (j + 1) : ℤ) := by
  have hp : (0 : ℤ) < 2 ^ (j + 1) := by positivity
  have hR' : (cascadeRadius (j + 1) : ℤ) = (cascadeRadius j : ℤ) + 3 * 2 ^ (j + 1) := by
    rw [cascadeRadius_succ]
    push_cast
    ring
  rw [hR']
  rw [Finset.sum_congr rfl fun n (_ : n ∈ Finset.Icc _ _) => cascadeInt.eq_2 n j]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  have h0 : ∑ n ∈ Finset.Icc (-((cascadeRadius j : ℤ) + 3 * 2 ^ (j + 1)))
        ((cascadeRadius j : ℤ) + 3 * 2 ^ (j + 1)), cascadeInt j n
      = ∑ m ∈ Finset.Icc (-(cascadeRadius j : ℤ)) (cascadeRadius j : ℤ), cascadeInt j m :=
    sum_Icc_shrink j (by omega) (by omega)
  have h1 := sum_shifted j (2 ^ (j + 1)) (by omega) (by omega)
  have h2 :
      ∑ n ∈ Finset.Icc (-((cascadeRadius j : ℤ) + 3 * 2 ^ (j + 1)))
          ((cascadeRadius j : ℤ) + 3 * 2 ^ (j + 1)), cascadeInt j (n + 2 ^ (j + 1))
        = ∑ m ∈ Finset.Icc (-(cascadeRadius j : ℤ)) (cascadeRadius j : ℤ), cascadeInt j m := by
    simpa using sum_shifted j (-(2 ^ (j + 1))) (by omega) (by omega)
  have h3 := sum_shifted j (3 * 2 ^ (j + 1)) (by omega) (by omega)
  have h4 :
      ∑ n ∈ Finset.Icc (-((cascadeRadius j : ℤ) + 3 * 2 ^ (j + 1)))
          ((cascadeRadius j : ℤ) + 3 * 2 ^ (j + 1)), cascadeInt j (n + 3 * 2 ^ (j + 1))
        = ∑ m ∈ Finset.Icc (-(cascadeRadius j : ℤ)) (cascadeRadius j : ℤ), cascadeInt j m := by
    simpa using sum_shifted j (-(3 * 2 ^ (j + 1))) (by omega) (by omega)
  rw [h0, h1, h2, h3, h4, ih, cascadeScale_succ]
  push_cast
  ring

/-- **Integer mass.** The signed integer coefficients of level `j` sum to `cascadeScale j`;
this is the numerator of `cascadeTap_sum_one`. -/
theorem cascadeInt_sum (j : ℕ) :
    ∑ n ∈ Finset.Icc (-(cascadeRadius j : ℤ)) (cascadeRadius j : ℤ), cascadeInt j n
      = (cascadeScale j : ℤ) := by
  induction j with
  | zero => decide
  | succ j ih => exact cascadeInt_sum_succ j ih

/-! ## Reindexing the taps on `Fin (cascadeSupport j)` -/

/-- The `Fin`-indexed tap sum is the integer sum over the symmetric support interval. -/
private lemma sum_fin_eq_sum_Icc (j : ℕ) :
    ∑ a : Fin (cascadeSupport j), cascadeInt j ((a.val : ℤ) - (cascadeRadius j : ℤ))
      = ∑ n ∈ Finset.Icc (-(cascadeRadius j : ℤ)) (cascadeRadius j : ℤ), cascadeInt j n := by
  have hsupp : cascadeSupport j = 2 * cascadeRadius j + 1 := rfl
  rw [hsupp]
  refine Finset.sum_bij (fun a _ => (a.val : ℤ) - (cascadeRadius j : ℤ)) ?_ ?_ ?_ ?_
  · intro a _
    simp only [Finset.mem_Icc]
    have := a.isLt
    omega
  · intro a₁ _ a₂ _ h
    have : a₁.val = a₂.val := by omega
    exact Fin.ext this
  · intro n hn
    simp only [Finset.mem_Icc] at hn
    have h0 : 0 ≤ n + (cascadeRadius j : ℤ) := by omega
    refine ⟨⟨(n + (cascadeRadius j : ℤ)).toNat, ?_⟩, Finset.mem_univ _, ?_⟩
    · have hlt : ((n + (cascadeRadius j : ℤ)).toNat : ℤ) < ((2 * cascadeRadius j + 1 : ℕ) : ℤ) := by
        rw [Int.toNat_of_nonneg h0]
        push_cast
        omega
      exact_mod_cast hlt
    · rw [Int.toNat_of_nonneg h0]
      ring
  · intro a _
    rfl

/-! ## The three closing theorems -/

/-- **Signed tap sum.** For every level `j`, the signed sum of the cascade taps is `1`.
This is the conservation of mass of the cascade kernel, not its `ℓ¹` mass `c_j`. -/
theorem cascadeTap_sum_one (j : ℕ) : ∑ a : Fin (cascadeSupport j), cascadeTap j a = 1 := by
  have hpos : (0 : ℝ) < (cascadeScale j : ℝ) := by
    unfold cascadeScale
    positivity
  have hInt : ∑ a : Fin (cascadeSupport j),
      cascadeInt j ((a.val : ℤ) - (cascadeRadius j : ℤ)) = (cascadeScale j : ℤ) := by
    rw [sum_fin_eq_sum_Icc, cascadeInt_sum]
  calc ∑ a : Fin (cascadeSupport j), cascadeTap j a
      = ∑ a : Fin (cascadeSupport j),
          ((cascadeInt j ((a.val : ℤ) - (cascadeRadius j : ℤ)) : ℝ) / (cascadeScale j : ℝ)) := rfl
    _ = (∑ a : Fin (cascadeSupport j),
          ((cascadeInt j ((a.val : ℤ) - (cascadeRadius j : ℤ)) : ℤ) : ℝ)) /
          (cascadeScale j : ℝ) := by rw [Finset.sum_div]
    _ = ((∑ a : Fin (cascadeSupport j),
          cascadeInt j ((a.val : ℤ) - (cascadeRadius j : ℤ)) : ℤ) : ℝ) /
          (cascadeScale j : ℝ) := by rw [Int.cast_sum]
    _ = (cascadeScale j : ℝ) / (cascadeScale j : ℝ) := by
      rw [hInt, Int.cast_natCast]
    _ = 1 := div_self hpos.ne'

/-- **Conservation of constants.** The endpoint-replicated level-`j` cascade fixes every
constant signal, for every `j` and every `n ≥ 1`, with no hypothesis `n ≥ cascadeSupport j`. -/
theorem directOp_const (j n : ℕ) [NeZero n] (c : ℝ) :
    directOp j n (fun _ => c) = fun _ => c := by
  ext i
  rw [directOp_apply]
  rw [← Finset.sum_mul, cascadeTap_sum_one, one_mul]

/-- **The operator at `n = 1` is the identity**, for every level `j`. -/
theorem directOp_one_eq_id (j : ℕ) :
    directOp j 1 = ContinuousLinearMap.id ℝ (Fin 1 → ℝ) := by
  ext x i
  rw [directOp_n_one, cascadeTap_sum_one, one_mul]
  rfl

end ThresholdCert.Nonperiodic
