import TWS.DaubechiesOpNorm
import TWS.Skeleton

/-!
# Solution — closed proofs from the companion `tws` package

Each declaration matches `Challenge.lean` definitionally. Bodies are
the existing theorems in `TWS.Daubechies` and `TWS` (no new `sorry`).
-/

open Finset Real
open scoped BigOperators

namespace Palomar

theorem kernel1d_l1 :
    ∑ i : Fin 7, |TWS.Daubechies.kernel1d i| = (9 : ℚ) / 8 :=
  TWS.Daubechies.kernel1d_l1

theorem kernel1d_l1_real :
    ∑ i : Fin 7, |(TWS.Daubechies.kernel1d i : ℝ)| = (9 : ℝ) / 8 :=
  TWS.Daubechies.kernel1d_l1_real

theorem db2_level1_opnorm_d2 :
    ∑ i : Fin 7, ∑ j : Fin 7,
        |((TWS.Daubechies.kernel1d i : ℝ) * (TWS.Daubechies.kernel1d j : ℝ))| =
      ((9 : ℝ) / 8) ^ 2 :=
  TWS.Daubechies.db2_level1_opnorm_d2

theorem db2_level1_opnorm_d2_num :
    ((9 : ℝ) / 8) ^ 2 = 81 / 64 :=
  TWS.Daubechies.db2_level1_opnorm_d2_num

theorem half_autocorr_l1 :
    |TWS.Daubechies.autocorr 3 / 2| + |TWS.Daubechies.autocorr 2 / 2| +
      |TWS.Daubechies.autocorr 1 / 2| + |TWS.Daubechies.autocorr 0 / 2| +
      |TWS.Daubechies.autocorr 1 / 2| + |TWS.Daubechies.autocorr 2 / 2| +
      |TWS.Daubechies.autocorr 3 / 2| = (9 : ℝ) / 8 :=
  TWS.Daubechies.half_autocorr_l1

theorem l2_norm_rev_tri (f g : ℝ → ℝ) (U : Set ℝ)
    (hf : MeasureTheory.MemLp (U.indicator f) 2)
    (hg : MeasureTheory.MemLp (U.indicator g) 2) :
    |TWS.L2Norm f U - TWS.L2Norm g U| ≤ TWS.L2Norm (fun t => f t - g t) U :=
  TWS.l2_norm_rev_tri f g U hf hg

theorem energy_stability (a b Γ : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : |a - b| ≤ Γ) :
    |a ^ 2 - b ^ 2| ≤ Γ * (a + b) :=
  TWS.energy_stability a b Γ ha hb h

end Palomar
