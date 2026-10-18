module

public import ThresholdExtension.EndpointReplication
public import ThresholdExtension.Db2ThresholdCertificate

/-!
# Threshold certificates for the endpoint-replicated (nonperiodic) db2 cascade

Operator: `A = ThresholdCert.Nonperiodic.directOp j n` on `Fin n → ℝ` (sup norm), for every
`n ≥ 1` (as `[NeZero n]`) and every level `j ≥ 0`. No assumption `n ≥ cascadeSupport j`.

* Norm bounds `‖A‖ ≤ cascadeC j` and `‖A‖ ≤ cascadeL` are derived from the identification
  `A = R ∘ C_{j,M,1} ∘ E` (proved in `EndpointReplication`), `‖R‖ ≤ 1`, `‖E‖ ≤ 1`, and the
  baseline periodic norm results (through the existing db2 bridge). They are upper bounds
  only; no exactness or optimality is claimed for the nonperiodic operator.
* The threshold certificate concerns the smoothed reference `A x`, not `x`.
-/

@[expose] public section

open TWSPeriodic ThresholdCert.Db2

namespace ThresholdCert.Nonperiodic

/-! ## Norm bounds -/

/-- Abstract composition bound: `‖R ∘ C ∘ E‖ ≤ ‖C‖` because `‖R‖, ‖E‖ ≤ 1`. -/
theorem directOp_norm_le_periodic (j n : ℕ) [NeZero n] :
    ‖directOp j n‖ ≤ ‖cascadeOperator j (padLen j n) 1‖ := by
  rw [directOp_eq_comp]
  calc ‖(restrictOp j n).comp ((cascadeOperator j (padLen j n) 1).comp (padOp j n))‖
      ≤ ‖restrictOp j n‖ * (‖cascadeOperator j (padLen j n) 1‖ * ‖padOp j n‖) :=
        ((restrictOp j n).opNorm_comp_le _).trans
          (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ 1 * (‖cascadeOperator j (padLen j n) 1‖ * 1) := by
        gcongr
        · exact restrictOp_norm_le j n
        · exact padOp_norm_le j n
    _ = ‖cascadeOperator j (padLen j n) 1‖ := by ring

/-- `‖A_{j,n}‖ ≤ c_j` for every `n ≥ 1` and every `j`. Uses the baseline exact periodic
norm at period `M = n + 2 r ≥ cascadeSupport j`. Upper bound only. -/
theorem directOp_norm_le_C (j n : ℕ) [NeZero n] : ‖directOp j n‖ ≤ cascadeC j :=
  (directOp_norm_le_periodic j n).trans
    (cascade1_opNorm_eq_C j (padLen j n) (cascadeSupport_le_padLen j n)).le

/-- `‖A_{j,n}‖ ≤ L = 1651/1395` for every `n ≥ 1` and every `j`. Upper bound only. -/
theorem directOp_norm_le_L (j n : ℕ) [NeZero n] : ‖directOp j n‖ ≤ cascadeL :=
  (directOp_norm_le_periodic j n).trans (cascade1_opNorm_le_L j (padLen j n))

/-! ## Perturbation bounds -/

section Perturbation

variable {j n : ℕ} [NeZero n] {ε : ℝ} {x y : Fin n → ℝ}

theorem directOp_perturbation_C (hxy : ‖y - x‖ ≤ ε) :
    ‖directOp j n y - directOp j n x‖ ≤ cascadeC j * ε := by
  rw [← map_sub]
  exact ((directOp j n).le_opNorm _).trans
    (mul_le_mul (directOp_norm_le_C j n) hxy (norm_nonneg _) (cascadeC_nonneg j))

theorem directOp_perturbation_L (hxy : ‖y - x‖ ≤ ε) :
    ‖directOp j n y - directOp j n x‖ ≤ cascadeL * ε := by
  rw [← map_sub]
  exact ((directOp j n).le_opNorm _).trans
    (mul_le_mul (directOp_norm_le_L j n) hxy (norm_nonneg _)
      ((cascadeC_nonneg j).trans (cascadeC_le_L j)))

theorem directOp_coord_perturbation_C (hxy : ‖y - x‖ ≤ ε) (i : Fin n) :
    |directOp j n y i - directOp j n x i| ≤ cascadeC j * ε :=
  coord_perturbation (directOp_norm_le_C j n) hxy i

theorem directOp_coord_perturbation_L (hxy : ‖y - x‖ ≤ ε) (i : Fin n) :
    |directOp j n y i - directOp j n x i| ≤ cascadeL * ε :=
  coord_perturbation (directOp_norm_le_L j n) hxy i

end Perturbation

/-! ## Threshold certificate: exact-level margin `m = c_j ε` -/

section CertC

variable {j n : ℕ} [NeZero n] {ε τ : ℝ} {x y : Fin n → ℝ}

theorem above_sound_C (hxy : ‖y - x‖ ≤ ε) {i : Fin n}
    (h : τ + cascadeC j * ε < directOp j n y i) : τ < directOp j n x i :=
  certifiedAbove_sound (directOp_norm_le_C j n) hxy h

theorem notAbove_sound_C (hxy : ‖y - x‖ ≤ ε) {i : Fin n}
    (h : directOp j n y i ≤ τ - cascadeC j * ε) : directOp j n x i ≤ τ :=
  certifiedNotAbove_sound (directOp_norm_le_C j n) hxy h

/-- Symmetric difference of the observed and reference strict superlevel sets lies in the
half-open band `τ - c_j ε < (A y) i ≤ τ + c_j ε`. -/
theorem symmDiff_subset_band_C (hxy : ‖y - x‖ ≤ ε) :
    symmDiff {i : Fin n | τ < directOp j n y i} {i : Fin n | τ < directOp j n x i} ⊆
      {i : Fin n | τ - cascadeC j * ε < directOp j n y i ∧
        directOp j n y i ≤ τ + cascadeC j * ε} :=
  symmDiff_subset_band (τ := τ) (directOp_norm_le_C j n) hxy

end CertC

/-! ## Threshold certificate: uniform margin `m = L ε` -/

section CertL

variable {j n : ℕ} [NeZero n] {ε τ : ℝ} {x y : Fin n → ℝ}

theorem above_sound_L (hxy : ‖y - x‖ ≤ ε) {i : Fin n}
    (h : τ + cascadeL * ε < directOp j n y i) : τ < directOp j n x i :=
  certifiedAbove_sound (directOp_norm_le_L j n) hxy h

theorem notAbove_sound_L (hxy : ‖y - x‖ ≤ ε) {i : Fin n}
    (h : directOp j n y i ≤ τ - cascadeL * ε) : directOp j n x i ≤ τ :=
  certifiedNotAbove_sound (directOp_norm_le_L j n) hxy h

theorem symmDiff_subset_band_L (hxy : ‖y - x‖ ≤ ε) :
    symmDiff {i : Fin n | τ < directOp j n y i} {i : Fin n | τ < directOp j n x i} ⊆
      {i : Fin n | τ - cascadeL * ε < directOp j n y i ∧
        directOp j n y i ≤ τ + cascadeL * ε} :=
  symmDiff_subset_band (τ := τ) (directOp_norm_le_L j n) hxy

end CertL

/-! ## Edge cases and small exact checks -/

/-- `n = 1`: every clamped index is the single sample, so `A_{j,1}` multiplies by the total
tap mass. (All levels `j`.) -/
theorem directOp_n_one (j : ℕ) (x : Fin 1 → ℝ) (i : Fin 1) :
    directOp j 1 x i = (∑ a : Fin (cascadeSupport j), cascadeTap j a) * x i := by
  rw [directOp_apply, Finset.sum_mul]
  exact Finset.sum_congr rfl fun a _ => by rw [Subsingleton.elim (clamp 1 _) i]

/-- The level-0 taps (`cascadeRadius 0 = 3`, `cascadeSupport 0 = 7`) are
`[-1, 0, 9, 16, 9, 0, -1] / 32`. -/
theorem cascadeTap_zero_values :
    cascadeTap 0 ⟨0, by decide⟩ = -1 / 32 ∧ cascadeTap 0 ⟨1, by decide⟩ = 0 ∧
    cascadeTap 0 ⟨2, by decide⟩ = 9 / 32 ∧ cascadeTap 0 ⟨3, by decide⟩ = 16 / 32 ∧
    cascadeTap 0 ⟨4, by decide⟩ = 9 / 32 ∧ cascadeTap 0 ⟨5, by decide⟩ = 0 ∧
    cascadeTap 0 ⟨6, by decide⟩ = -1 / 32 := by
  simp [cascadeTap, cascadeInt, cascadeRadius, cascadeScale]

/-- `n = 1`, `j = 0`: the taps sum to `1`, so `A_{0,1}` is the identity. -/
theorem directOp_zero_one (x : Fin 1 → ℝ) : directOp 0 1 x = x := by
  ext i
  rw [directOp_n_one]
  have hs : (∑ a : Fin (cascadeSupport 0), cascadeTap 0 a) = 1 := by
    show (∑ a : Fin 7, cascadeTap 0 a) = 1
    simp [Fin.sum_univ_seven, cascadeTap, cascadeInt, cascadeRadius, cascadeScale]
    norm_num
  rw [hs, one_mul]

/-! ### Small exact checks (supplements to the universal identity, not replacements)

In every check below the periodic side is evaluated from the baseline operator by the
generic unfolding `cascadeOperator_one_apply` and finite `ZMod` arithmetic; it does not use
the identification theorem `directOp_eq_restrict_cascade_pad`. All checks have
`n < cascadeSupport j`. -/

/-- The signal `(1, 0)` of length `n = 2`. -/
noncomputable def stepSignal2 : Fin 2 → ℝ := fun i => if i.val = 0 then 1 else 0

/-- The signal `(0, 1, 0)` of length `n = 3`. -/
noncomputable def spikeSignal3 : Fin 3 → ℝ := fun i => if i.val = 1 then 1 else 0

/-- `j = 0`, `n = 2` (support 7), direct stencil: `A (1, 0) = (3/4, 1/4)`. -/
theorem check_direct_j0_n2 : directOp 0 2 stepSignal2 = ![3 / 4, 1 / 4] := by
  ext i
  fin_cases i <;>
  · rw [directOp_apply]
    show (∑ a : Fin 7, _) = _
    simp +decide [Fin.sum_univ_seven, cascadeTap, cascadeInt, cascadeRadius, cascadeScale,
      stepSignal2]
    norm_num

/-- Same data through padding (period `M = 8`), the baseline operator, and restriction. -/
theorem check_periodic_j0_n2 :
    restrictOp 0 2 (cascadeOperator 0 (padLen 0 2) 1 (padOp 0 2 stepSignal2)) =
      ![3 / 4, 1 / 4] := by
  ext i
  fin_cases i <;>
  · rw [restrictOp_apply, cascadeOperator_one_apply]
    show (∑ a : Fin 7, _) = _
    simp only [padOp_apply, Pi.sub_apply, stepSignal2]
    simp +decide [Fin.sum_univ_seven, cascadeTap, cascadeInt, cascadeRadius, cascadeScale,
      cascadeOffset, padLen]
    norm_num

/-- `j = 0`, `n = 3`, direct stencil: `A (0, 1, 0) = (9/32, 1/2, 9/32)`. -/
theorem check_direct_j0_n3 : directOp 0 3 spikeSignal3 = ![9 / 32, 1 / 2, 9 / 32] := by
  ext i
  fin_cases i <;>
  · rw [directOp_apply]
    show (∑ a : Fin 7, _) = _
    simp +decide [Fin.sum_univ_seven, cascadeTap, cascadeInt, cascadeRadius, cascadeScale,
      spikeSignal3]
    all_goals norm_num

/-- Same data through padding (period `M = 9`), the baseline operator, and restriction. -/
theorem check_periodic_j0_n3 :
    restrictOp 0 3 (cascadeOperator 0 (padLen 0 3) 1 (padOp 0 3 spikeSignal3)) =
      ![9 / 32, 1 / 2, 9 / 32] := by
  ext i
  fin_cases i <;>
  · rw [restrictOp_apply, cascadeOperator_one_apply]
    show (∑ a : Fin 7, _) = _
    simp only [padOp_apply, Pi.sub_apply, spikeSignal3]
    simp +decide [Fin.sum_univ_seven, cascadeTap, cascadeInt, cascadeRadius, cascadeScale,
      cascadeOffset, padLen]
    all_goals norm_num

/-- `j = 1`, `n = 2` (support 19), direct stencil: `A (1, 0) = (5/8, 3/8)`. -/
theorem check_direct_j1_n2 : directOp 1 2 stepSignal2 = ![5 / 8, 3 / 8] := by
  ext i
  fin_cases i <;>
  · rw [directOp_apply]
    show (∑ a : Fin 19, _) = _
    simp +decide [Fin.sum_univ_succ, cascadeTap, cascadeInt, cascadeRadius, cascadeScale,
      stepSignal2]
    norm_num

/-- Same data through padding (period `M = 20`), the baseline operator, and restriction. -/
theorem check_periodic_j1_n2 :
    restrictOp 1 2 (cascadeOperator 1 (padLen 1 2) 1 (padOp 1 2 stepSignal2)) =
      ![5 / 8, 3 / 8] := by
  ext i
  fin_cases i <;>
  · rw [restrictOp_apply, cascadeOperator_one_apply]
    show (∑ a : Fin 19, _) = _
    simp only [padOp_apply, Pi.sub_apply, stepSignal2]
    simp +decide [Fin.sum_univ_succ, cascadeTap, cascadeInt, cascadeRadius, cascadeScale,
      cascadeOffset, padLen]
    norm_num

/-- The period-2 wrap of `(1, 0)` (no endpoint padding). -/
noncomputable def wrapSignal2 : (Fin 1 → ZMod 2) → ℝ := fun u => if (u 0).val = 0 then 1 else 0

/-- Padding is essential: applying the baseline periodic operator directly at period `N = n = 2`
gives `1/2` at the first coordinate, whereas endpoint replication gives `3/4`. -/
theorem unpadded_periodic_differs :
    cascadeOperator 0 2 1 wrapSignal2 (fun _ => 0) = 1 / 2 ∧
      cascadeOperator 0 2 1 wrapSignal2 (fun _ => 0) ≠ directOp 0 2 stepSignal2 0 := by
  have h : cascadeOperator 0 2 1 wrapSignal2 (fun _ => 0) = 1 / 2 := by
    rw [cascadeOperator_one_apply]
    show (∑ a : Fin 7, _) = _
    simp only [Pi.sub_apply, wrapSignal2]
    simp +decide [Fin.sum_univ_seven, cascadeTap, cascadeInt, cascadeRadius, cascadeScale,
      cascadeOffset]
    norm_num
  refine ⟨h, ?_⟩
  rw [h, check_direct_j0_n2]
  norm_num

end ThresholdCert.Nonperiodic
