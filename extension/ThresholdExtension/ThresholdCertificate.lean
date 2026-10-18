module

public import Mathlib

/-!
# Certified threshold decisions after a bounded linear smoothing operator

Abstract, operator-agnostic layer.  Nothing here refers to the db2 cascade; a concrete
operator and its norm bound are supplied as hypotheses `hT : ‖T‖ ≤ B`.

All signal spaces are `I → ℝ` / `J → ℝ` with Mathlib's product (supremum) norm.
-/

@[expose] public section

namespace ThresholdCert

variable {I J : Type*} [Fintype I] [Fintype J]

/-- Coordinate `i` of `T y` is certified above the threshold: `(T y) i > τ + B ε`. -/
def CertifiedAbove (T : (I → ℝ) →L[ℝ] (J → ℝ)) (B ε τ : ℝ) (y : I → ℝ) (i : J) : Prop :=
  τ + B * ε < T y i

/-- Coordinate `i` of `T y` is certified not above the threshold: `(T y) i ≤ τ - B ε`. -/
def CertifiedNotAbove (T : (I → ℝ) →L[ℝ] (J → ℝ)) (B ε τ : ℝ) (y : I → ℝ) (i : J) : Prop :=
  T y i ≤ τ - B * ε

/-- Coordinate `i` is uncertified: `τ - B ε < (T y) i ≤ τ + B ε`. -/
def Uncertified (T : (I → ℝ) →L[ℝ] (J → ℝ)) (B ε τ : ℝ) (y : I → ℝ) (i : J) : Prop :=
  τ - B * ε < T y i ∧ T y i ≤ τ + B * ε

/-- Strict superlevel set `{i | τ < (T z) i}` (used for both `z = y` and `z = x`). -/
def superlevel (T : (I → ℝ) →L[ℝ] (J → ℝ)) (τ : ℝ) (z : I → ℝ) : Set J :=
  {i | τ < T z i}

/-- Uncertainty band: the half-open band `τ - B ε < (T y) i ≤ τ + B ε`. -/
def uncertaintyBand (T : (I → ℝ) →L[ℝ] (J → ℝ)) (B ε τ : ℝ) (y : I → ℝ) : Set J :=
  {i | Uncertified T B ε τ y i}

variable {T : (I → ℝ) →L[ℝ] (J → ℝ)} {B ε τ : ℝ} {x y : I → ℝ}

/-- Coordinatewise perturbation bound. (`0 ≤ B` and `0 ≤ ε` are implied by the hypotheses.) -/
theorem coord_perturbation (hT : ‖T‖ ≤ B) (hxy : ‖y - x‖ ≤ ε) (i : J) :
    |T y i - T x i| ≤ B * ε := by
  have h1 : |T y i - T x i| ≤ ‖T (y - x)‖ := by
    rw [map_sub]
    simpa [Real.norm_eq_abs] using norm_le_pi_norm (T y - T x) i
  have hB : 0 ≤ B := (norm_nonneg _).trans hT
  calc |T y i - T x i| ≤ ‖T (y - x)‖ := h1
    _ ≤ ‖T‖ * ‖y - x‖ := T.le_opNorm _
    _ ≤ B * ε := mul_le_mul hT hxy (norm_nonneg _) hB

theorem certifiedAbove_sound (hT : ‖T‖ ≤ B) (hxy : ‖y - x‖ ≤ ε) {i : J}
    (h : CertifiedAbove T B ε τ y i) : τ < T x i := by
  have := coord_perturbation hT hxy i
  unfold CertifiedAbove at h
  linarith [le_abs_self (T y i - T x i)]

theorem certifiedNotAbove_sound (hT : ‖T‖ ≤ B) (hxy : ‖y - x‖ ≤ ε) {i : J}
    (h : CertifiedNotAbove T B ε τ y i) : T x i ≤ τ := by
  have := coord_perturbation hT hxy i
  unfold CertifiedNotAbove at h
  linarith [neg_abs_le (T y i - T x i)]

omit [Fintype I] [Fintype J] in
/-- The three categories partition the coordinates whenever `0 ≤ B * ε`. -/
theorem trichotomy (hBε : 0 ≤ B * ε) (i : J) :
    (CertifiedAbove T B ε τ y i ∧ ¬ CertifiedNotAbove T B ε τ y i ∧ ¬ Uncertified T B ε τ y i) ∨
    (¬ CertifiedAbove T B ε τ y i ∧ CertifiedNotAbove T B ε τ y i ∧ ¬ Uncertified T B ε τ y i) ∨
    (¬ CertifiedAbove T B ε τ y i ∧ ¬ CertifiedNotAbove T B ε τ y i ∧ Uncertified T B ε τ y i) := by
  unfold CertifiedAbove CertifiedNotAbove Uncertified
  rcases lt_or_ge (τ + B * ε) (T y i) with h | h
  · left; refine ⟨h, ?_, ?_⟩ <;> intro h' <;> [linarith; linarith [h'.2]]
  · rcases le_or_gt (T y i) (τ - B * ε) with h2 | h2
    · right; left; refine ⟨by linarith, h2, ?_⟩; intro h'; linarith [h'.1]
    · right; right; exact ⟨by linarith, by linarith, h2, h⟩

/-- The partition, with `0 ≤ B * ε` derived from the two norm hypotheses. -/
theorem trichotomy_of_bounds (hT : ‖T‖ ≤ B) (hxy : ‖y - x‖ ≤ ε) (i : J) :
    (CertifiedAbove T B ε τ y i ∧ ¬ CertifiedNotAbove T B ε τ y i ∧ ¬ Uncertified T B ε τ y i) ∨
    (¬ CertifiedAbove T B ε τ y i ∧ CertifiedNotAbove T B ε τ y i ∧ ¬ Uncertified T B ε τ y i) ∨
    (¬ CertifiedAbove T B ε τ y i ∧ ¬ CertifiedNotAbove T B ε τ y i ∧ Uncertified T B ε τ y i) :=
  trichotomy (mul_nonneg ((norm_nonneg _).trans hT) ((norm_nonneg _).trans hxy)) i

/-- Refined containment: one-sided errors lie in the two halves of the band. -/
theorem diff_subsets (hT : ‖T‖ ≤ B) (hxy : ‖y - x‖ ≤ ε) :
    superlevel T τ y \ superlevel T τ x ⊆ {i | τ < T y i ∧ T y i ≤ τ + B * ε} ∧
    superlevel T τ x \ superlevel T τ y ⊆ {i | τ - B * ε < T y i ∧ T y i ≤ τ} := by
  constructor
  · rintro i ⟨hy, hx⟩
    simp only [superlevel, Set.mem_ofPred_eq, not_lt] at hy hx ⊢
    have := coord_perturbation hT hxy i
    exact ⟨hy, by linarith [le_abs_self (T y i - T x i)]⟩
  · rintro i ⟨hx, hy⟩
    simp only [superlevel, Set.mem_ofPred_eq, not_lt] at hy hx ⊢
    have := coord_perturbation hT hxy i
    exact ⟨by linarith [neg_abs_le (T y i - T x i)], hy⟩

/-- Symmetric difference of observed and reference superlevel sets lies in the
half-open uncertainty band. -/
theorem symmDiff_subset_band (hT : ‖T‖ ≤ B) (hxy : ‖y - x‖ ≤ ε) :
    symmDiff (superlevel T τ y) (superlevel T τ x) ⊆ uncertaintyBand T B ε τ y := by
  have hBε : 0 ≤ B * ε :=
    mul_nonneg ((norm_nonneg _).trans hT) ((norm_nonneg _).trans hxy)
  obtain ⟨h1, h2⟩ := diff_subsets (τ := τ) hT hxy
  rintro i (hi | hi)
  · obtain ⟨a, b⟩ := h1 hi; exact ⟨by linarith, b⟩
  · obtain ⟨a, b⟩ := h2 hi; exact ⟨a, by linarith⟩

omit [Fintype I] [Fintype J] in
/-- When `B * ε = 0` the uncertainty band is empty. -/
theorem uncertaintyBand_eq_empty_of_mul_eq_zero (h0 : B * ε = 0) :
    uncertaintyBand T B ε τ y = ∅ := by
  ext i; simp only [uncertaintyBand, Uncertified, h0, sub_zero, add_zero,
    Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and, not_le]
  intro h; exact h

/-- Exact recovery when `B * ε = 0`: the superlevel sets coincide. -/
theorem superlevel_eq_of_mul_eq_zero (hT : ‖T‖ ≤ B) (hxy : ‖y - x‖ ≤ ε) (h0 : B * ε = 0) :
    superlevel T τ y = superlevel T τ x := by
  have h := symmDiff_subset_band (τ := τ) hT hxy
  rw [uncertaintyBand_eq_empty_of_mul_eq_zero h0, Set.subset_empty_iff] at h
  exact symmDiff_eq_bot.mp h

/-- Decisions about `x` itself (requires `I = J`) need an extra modelling assumption
`‖T x - x‖ ≤ δ`; the margin becomes `B ε + δ`. -/
theorem raw_above_sound {T : (I → ℝ) →L[ℝ] (I → ℝ)} {δ : ℝ} (hT : ‖T‖ ≤ B)
    (hxy : ‖y - x‖ ≤ ε) (hδ : ‖T x - x‖ ≤ δ) {i : I} (h : τ + B * ε + δ < T y i) :
    τ < x i := by
  have h1 := coord_perturbation hT hxy i
  have h2 : |T x i - x i| ≤ δ := by
    simpa [Real.norm_eq_abs] using (norm_le_pi_norm (T x - x) i).trans hδ
  linarith [le_abs_self (T y i - T x i), le_abs_self (T x i - x i)]

theorem raw_notAbove_sound {T : (I → ℝ) →L[ℝ] (I → ℝ)} {δ : ℝ} (hT : ‖T‖ ≤ B)
    (hxy : ‖y - x‖ ≤ ε) (hδ : ‖T x - x‖ ≤ δ) {i : I} (h : T y i ≤ τ - B * ε - δ) :
    x i ≤ τ := by
  have h1 := coord_perturbation hT hxy i
  have h2 : |T x i - x i| ≤ δ := by
    simpa [Real.norm_eq_abs] using (norm_le_pi_norm (T x - x) i).trans hδ
  linarith [neg_abs_le (T y i - T x i), neg_abs_le (T x i - x i)]

/-! ## Counterexamples to tempting variants (one-coordinate identity operator) -/

/-- Non-strict "certified above" (`τ + B ε ≤ (T y) i`) is unsound:
`T = id`, `B = ε = 1`, `τ = 0`, `x = 0`, `y = 1`. -/
theorem nonstrict_above_unsound :
    ¬ ∀ (T : (Fin 1 → ℝ) →L[ℝ] (Fin 1 → ℝ)) (B ε τ : ℝ) (x y : Fin 1 → ℝ) (i : Fin 1),
      ‖T‖ ≤ B → ‖y - x‖ ≤ ε → τ + B * ε ≤ T y i → τ < T x i := by
  intro h
  have := h (ContinuousLinearMap.id ℝ _) 1 1 0 0 1 0 ContinuousLinearMap.norm_id_le
    (by simp) (by simp)
  simp at this

/-- The open band `τ - B ε < (T y) i < τ + B ε` does NOT contain the symmetric difference:
same data, coordinate observed above (`(T y) 0 = 1 = τ + B ε`) but reference not above. -/
theorem open_band_fails :
    ¬ ∀ (T : (Fin 1 → ℝ) →L[ℝ] (Fin 1 → ℝ)) (B ε τ : ℝ) (x y : Fin 1 → ℝ),
      ‖T‖ ≤ B → ‖y - x‖ ≤ ε →
      symmDiff (superlevel T τ y) (superlevel T τ x) ⊆
        {i | τ - B * ε < T y i ∧ T y i < τ + B * ε} := by
  intro h
  have := h (ContinuousLinearMap.id ℝ _) 1 1 0 0 1 ContinuousLinearMap.norm_id_le (by simp)
  have hmem : (0 : Fin 1) ∈ symmDiff (superlevel (ContinuousLinearMap.id ℝ (Fin 1 → ℝ)) 0 1)
      (superlevel (ContinuousLinearMap.id ℝ (Fin 1 → ℝ)) 0 0) := by
    left; simp [superlevel]
  have := this hmem
  simp at this

/-- Uncertified does not mean wrong (incompleteness of a loose global bound):
the zero operator with the valid bound `B = 1`, `ε = 1`, `τ = 0`. Every coordinate is
uncertified, yet for every admissible `x` the decision "not above" is correct. -/
theorem uncertified_not_wrong :
    let T : (Fin 1 → ℝ) →L[ℝ] (Fin 1 → ℝ) := 0
    ‖T‖ ≤ 1 ∧ Uncertified T 1 1 0 0 0 ∧ ∀ x : Fin 1 → ℝ, ¬ (0 : ℝ) < T x 0 := by
  refine ⟨by simp, ?_, ?_⟩ <;> simp [Uncertified]

/-- Without an assumption linking `T x` to `x`, a certificate about `T x` says nothing about
`x`: zero operator, `ε = 0`, `y = x = 1`, `τ = 0`. The coordinate is certified not above for
`T x`, yet `x 0 = 1 > τ`. -/
theorem smoothed_cert_not_raw_cert :
    let T : (Fin 1 → ℝ) →L[ℝ] (Fin 1 → ℝ) := 0
    ‖T‖ ≤ 0 ∧ CertifiedNotAbove T 0 0 0 1 0 ∧ (0 : ℝ) < (1 : Fin 1 → ℝ) 0 := by
  refine ⟨by simp, ?_, ?_⟩ <;> simp [CertifiedNotAbove]

end ThresholdCert
