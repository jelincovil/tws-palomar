import TWS.DaubechiesOpNorm
import TWS.Skeleton

/-!
# Solution — closed proofs from the companion `tws` package

Comparator compiles Challenge and Solution as *separate* environments.
This file does **not** `import Challenge`. Signatures match Challenge
exactly. Bodies are the existing TWS theorems.

Compared constants (see `comparator.json`):
`Palomar.stability_Linf`, `Palomar.kernel1d_l1`, `Palomar.kernel1d_l1_real`,
`Palomar.db2_level1_opnorm_d2`, `Palomar.db2_level1_opnorm_d2_num`,
`Palomar.half_autocorr_l1`, `Palomar.l2_norm_rev_tri`,
`Palomar.energy_stability`.
-/

open Finset Real
open scoped BigOperators

namespace Palomar

theorem stability_Linf {d : Nat} (Psi : TWS.WaveletFrame d)
    (h_bounds : TWS.frame_bounds_pos Psi)
    (Lk Cfp : ℝ)
    (Z1 Z2 : (Fin d → ℝ) → ℝ) (j j0 : Int) (k n : Nat)
    (U : Set ℝ) (D : Set (Fin d → ℝ))
    (hU : Bornology.IsBounded U)
    (h_landscape : TWS.landscape_stability_hyp Psi Lk Z1 Z2 j j0 k n U D)
    (h_proj : TWS.frame_proj_bound_hyp Psi Cfp (Z1 - Z2) j j0 D) :
    TWS.L2Norm (fun t => TWS.landscape n (TWS.projDgmK Psi j j0 Z1 k) t
                    - TWS.landscape n (TWS.projDgmK Psi j j0 Z2 k) t) U
      ≤ (Lk * Cfp) * TWS.LinfNorm (Z1 - Z2) D * Real.sqrt (Metric.diam U) :=
  TWS.stability_Linf Psi h_bounds Lk Cfp Z1 Z2 j j0 k n U D hU h_landscape h_proj

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
