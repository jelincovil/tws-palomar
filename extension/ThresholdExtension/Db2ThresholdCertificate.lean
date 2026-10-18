module

public import ThresholdExtension.ThresholdCertificate
public import Solution

/-!
# Threshold certificates for the one-dimensional periodic db2 cascade

Bridge between the abstract certificate in `ThresholdExtension.ThresholdCertificate`
(namespace `ThresholdCert`) and the baseline cascade operator
`TWSPeriodic.cascadeOperator j N 1` from the baseline module `Solution`.

* The signal index type is the baseline's own `Fin 1 → ZMod N`; it is not replaced by
  `ZMod N`.
* Positivity of the period is expressed by the baseline's own convention `[NeZero N]`.
* The norm bound `B = 1651/1395` is *derived* from the baseline theorem
  `TWSPeriodic.cascade_opNorm_uniform` (with `d = 1`); it is never assumed.
* The exact-level bound `B = c_j` is derived from `TWSPeriodic.cascade_opNorm_formula`
  under `TWSPeriodic.cascadeSupport j ≤ N`.

Everything certifies decisions about the smoothed reference `C x`, not about `x`.
-/

@[expose] public section

namespace ThresholdCert.Db2

open TWSPeriodic

/-- The uniform db2 cascade constant `L = 1651/1395` (as a real number). -/
noncomputable def cascadeL : ℝ := (1651 : ℝ) / 1395

/-- The exact one-dimensional cascade norm constant
`c_j = 1651/1395 - (4/63)(1/4)^j + (1/180)(1/16)^j - (1/1736)(1/32)^j`. -/
noncomputable def cascadeC (j : ℕ) : ℝ :=
  (1651 : ℝ) / 1395 - ((4 : ℝ) / 63) * ((1 : ℝ) / 4) ^ j
    + ((1 : ℝ) / 180) * ((1 : ℝ) / 16) ^ j
    - ((1 : ℝ) / 1736) * ((1 : ℝ) / 32) ^ j

variable {j N : ℕ} [NeZero N]

/-! ## Norm bounds obtained from the baseline theorems -/

/-- `‖C_{j,N,1}‖ ≤ 1651/1395`, from `TWSPeriodic.cascade_opNorm_uniform` with `d = 1`. -/
theorem cascade1_opNorm_le_L (j N : ℕ) [NeZero N] :
    ‖cascadeOperator j N 1‖ ≤ cascadeL := by
  simpa [cascadeL] using cascade_opNorm_uniform j N 1

/-- `‖C_{j,N,1}‖ = c_j` when `cascadeSupport j ≤ N`, from
`TWSPeriodic.cascade_opNorm_formula` with `d = 1`. -/
theorem cascade1_opNorm_eq_C (j N : ℕ) [NeZero N] (hN : cascadeSupport j ≤ N) :
    ‖cascadeOperator j N 1‖ = cascadeC j := by
  simpa [cascadeC] using cascade_opNorm_formula j N 1 hN

/-- `0 ≤ c_j`, derived from the baseline norm identity (at the period
`N = cascadeSupport j`) and nonnegativity of the operator norm. -/
theorem cascadeC_nonneg (j : ℕ) : 0 ≤ cascadeC j := by
  have : NeZero (cascadeSupport j) := ⟨by unfold cascadeSupport; omega⟩
  rw [← cascade1_opNorm_eq_C j (cascadeSupport j) le_rfl]
  exact norm_nonneg _

/-- `c_j ≤ L`: the exact-level band is never wider than the uniform band. Derived by
combining the two baseline theorems at the period `N = cascadeSupport j`. -/
theorem cascadeC_le_L (j : ℕ) : cascadeC j ≤ cascadeL := by
  have : NeZero (cascadeSupport j) := ⟨by unfold cascadeSupport; omega⟩
  rw [← cascade1_opNorm_eq_C j (cascadeSupport j) le_rfl]
  exact cascade1_opNorm_le_L j (cascadeSupport j)

/-! ## Uniform-level certificate: `B = 1651/1395`, any positive period -/

section Uniform

variable {ε τ : ℝ} {x y : (Fin 1 → ZMod N) → ℝ}

theorem coord_perturbation_uniform (hxy : ‖y - x‖ ≤ ε) (i : Fin 1 → ZMod N) :
    |cascadeOperator j N 1 y i - cascadeOperator j N 1 x i| ≤ cascadeL * ε :=
  coord_perturbation (cascade1_opNorm_le_L j N) hxy i

theorem certifiedAbove_sound_uniform (hxy : ‖y - x‖ ≤ ε) {i : Fin 1 → ZMod N}
    (h : CertifiedAbove (cascadeOperator j N 1) cascadeL ε τ y i) :
    τ < cascadeOperator j N 1 x i :=
  certifiedAbove_sound (cascade1_opNorm_le_L j N) hxy h

theorem certifiedNotAbove_sound_uniform (hxy : ‖y - x‖ ≤ ε) {i : Fin 1 → ZMod N}
    (h : CertifiedNotAbove (cascadeOperator j N 1) cascadeL ε τ y i) :
    cascadeOperator j N 1 x i ≤ τ :=
  certifiedNotAbove_sound (cascade1_opNorm_le_L j N) hxy h

theorem symmDiff_subset_band_uniform (hxy : ‖y - x‖ ≤ ε) :
    symmDiff (superlevel (cascadeOperator j N 1) τ y) (superlevel (cascadeOperator j N 1) τ x)
      ⊆ uncertaintyBand (cascadeOperator j N 1) cascadeL ε τ y :=
  symmDiff_subset_band (cascade1_opNorm_le_L j N) hxy

/-- Noise-free case: with `ε = 0` the observed and reference superlevel sets coincide. -/
theorem superlevel_eq_uniform_of_eps_zero (hxy : ‖y - x‖ ≤ 0) :
    superlevel (cascadeOperator j N 1) τ y = superlevel (cascadeOperator j N 1) τ x :=
  superlevel_eq_of_mul_eq_zero (cascade1_opNorm_le_L j N) hxy (mul_zero _)

end Uniform

/-! ## Exact-level certificate: `B = c_j`, periods `N ≥ cascadeSupport j` -/

section Exact

variable {ε τ : ℝ} {x y : (Fin 1 → ZMod N) → ℝ}

theorem coord_perturbation_exact (hN : cascadeSupport j ≤ N) (hxy : ‖y - x‖ ≤ ε)
    (i : Fin 1 → ZMod N) :
    |cascadeOperator j N 1 y i - cascadeOperator j N 1 x i| ≤ cascadeC j * ε :=
  coord_perturbation (cascade1_opNorm_eq_C j N hN).le hxy i

theorem certifiedAbove_sound_exact (hN : cascadeSupport j ≤ N) (hxy : ‖y - x‖ ≤ ε)
    {i : Fin 1 → ZMod N}
    (h : CertifiedAbove (cascadeOperator j N 1) (cascadeC j) ε τ y i) :
    τ < cascadeOperator j N 1 x i :=
  certifiedAbove_sound (cascade1_opNorm_eq_C j N hN).le hxy h

theorem certifiedNotAbove_sound_exact (hN : cascadeSupport j ≤ N) (hxy : ‖y - x‖ ≤ ε)
    {i : Fin 1 → ZMod N}
    (h : CertifiedNotAbove (cascadeOperator j N 1) (cascadeC j) ε τ y i) :
    cascadeOperator j N 1 x i ≤ τ :=
  certifiedNotAbove_sound (cascade1_opNorm_eq_C j N hN).le hxy h

theorem symmDiff_subset_band_exact (hN : cascadeSupport j ≤ N) (hxy : ‖y - x‖ ≤ ε) :
    symmDiff (superlevel (cascadeOperator j N 1) τ y) (superlevel (cascadeOperator j N 1) τ x)
      ⊆ uncertaintyBand (cascadeOperator j N 1) (cascadeC j) ε τ y :=
  symmDiff_subset_band (cascade1_opNorm_eq_C j N hN).le hxy

/-- The exact-level uncertainty band is contained in the uniform-level band. -/
theorem band_exact_subset_uniform (hε : 0 ≤ ε) :
    uncertaintyBand (cascadeOperator j N 1) (cascadeC j) ε τ y
      ⊆ uncertaintyBand (cascadeOperator j N 1) cascadeL ε τ y := by
  have h := mul_le_mul_of_nonneg_right (cascadeC_le_L j) hε
  rintro i ⟨h1, h2⟩
  exact ⟨by linarith, by linarith⟩

end Exact

end ThresholdCert.Db2
