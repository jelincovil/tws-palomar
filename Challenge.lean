import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Rat.Cast.Order
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic

/-!
# Challenge — statements only (Mathlib-only)

Statement surface for the Palomar Registry entry. The transitive
import closure of this file contains only Lean core and Mathlib,
per the Palomar Challenge dependency rule.

Definitions needed to state the results are inlined below, with the
same bodies as in the companion TWS development (vendored under `TWS/`).

Paper labels in the docstrings. Compared declarations (see
`comparator.json`): `Palomar.kernel1d_l1`, `Palomar.kernel1d_l1_real`,
`Palomar.db2_level1_opnorm_d2`, `Palomar.db2_level1_opnorm_d2_num`,
`Palomar.half_autocorr_l1`, `Palomar.l2_norm_rev_tri`,
`Palomar.energy_stability`.

The paper's Theorem A composition (`TWS.stability_Linf`) is not part of
this entry: it is a chained inequality under named hypotheses, not a
kernel-checked TDA theorem. See `formalization.yaml`.
-/

open Finset Real
open scoped BigOperators

namespace Palomar

/-! ## Inlined definitions -/

/-- Taps of the half-autocorrelation `½ R_h` on `{-3,…,3}`. -/
def kernel1d : Fin 7 → ℚ
  | ⟨0, _⟩ => -1 / 32
  | ⟨1, _⟩ => 0
  | ⟨2, _⟩ => 9 / 32
  | ⟨3, _⟩ => 16 / 32
  | ⟨4, _⟩ => 9 / 32
  | ⟨5, _⟩ => 0
  | ⟨6, _⟩ => -1 / 32

/-- Coefficient `c = 1/(4√2)` of the orthonormal db2 low-pass filter. -/
noncomputable def c : ℝ := 1 / (4 * sqrt 2)

/-- Orthonormal db2 low-pass filter, as a finitely supported `ℕ → ℝ`. -/
noncomputable def h : ℕ → ℝ
  | 0 => c * (1 + sqrt 3)
  | 1 => c * (3 + sqrt 3)
  | 2 => c * (3 - sqrt 3)
  | 3 => c * (1 - sqrt 3)
  | _ => 0

/-- Autocorrelation of `h` at nonnegative lag `k`. -/
noncomputable def autocorr (k : ℕ) : ℝ :=
  ∑ n ∈ range 4, h n * h (n + k)

/-- `L²` seminorm on `U`, as the `eLpNorm` of the indicated function. -/
noncomputable def L2Norm (g : ℝ → ℝ) (U : Set ℝ) : ℝ :=
  (MeasureTheory.eLpNorm (U.indicator g) 2).toReal

/-! ## Statements -/

/-- Paper `prop:opnorm`, kernel only: `ℓ¹(k₀) = 9/8` in `ℚ`. -/
theorem kernel1d_l1 :
    ∑ i : Fin 7, |kernel1d i| = (9 : ℚ) / 8 := by
  sorry

/-- Same identity in `ℝ`. -/
theorem kernel1d_l1_real :
    ∑ i : Fin 7, |(kernel1d i : ℝ)| = (9 : ℝ) / 8 := by
  sorry

/-- Separable 2-D row-sum of `|k_i k_j|`, equal to `(9/8)²`. -/
theorem db2_level1_opnorm_d2 :
    ∑ i : Fin 7, ∑ j : Fin 7,
        |((kernel1d i : ℝ) * (kernel1d j : ℝ))| =
      ((9 : ℝ) / 8) ^ 2 := by
  sorry

/-- Arithmetic identity `(9/8)² = 81/64`. -/
theorem db2_level1_opnorm_d2_num :
    ((9 : ℝ) / 8) ^ 2 = 81 / 64 := by
  sorry

/-- QMF half-autocorrelation `ℓ¹` equals `9/8`. -/
theorem half_autocorr_l1 :
    |autocorr 3 / 2| + |autocorr 2 / 2| + |autocorr 1 / 2| + |autocorr 0 / 2| +
      |autocorr 1 / 2| + |autocorr 2 / 2| + |autocorr 3 / 2| = (9 : ℝ) / 8 := by
  sorry

/-- Paper `lem:revtri`: reverse triangle for `L2Norm` on `U`. -/
theorem l2_norm_rev_tri (f g : ℝ → ℝ) (U : Set ℝ)
    (hf : MeasureTheory.MemLp (U.indicator f) 2)
    (hg : MeasureTheory.MemLp (U.indicator g) 2) :
    |L2Norm f U - L2Norm g U| ≤ L2Norm (fun t => f t - g t) U := by
  sorry

/-- Algebraic core of `cor:energy`: `|a²−b²| ≤ Γ(a+b)` when `|a−b| ≤ Γ`. -/
theorem energy_stability (a b Γ : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : |a - b| ≤ Γ) :
    |a ^ 2 - b ^ 2| ≤ Γ * (a + b) := by
  sorry

end Palomar
