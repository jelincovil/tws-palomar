import TWS.DaubechiesOpNorm
import TWS.Skeleton

/-!
# Challenge — statements only

Each theorem is a `sorry` copy of a closed declaration in the companion
package `tws` (`tws-repro/formalization`). Headers name the corresponding
`\label{...}` in `tws-persistence-stability/paper/main.tex`.

This module does **not** claim Lean proofs of Theorem A, Lemma
`lem:landscapeU`, Lemma `lem:proj`, Proposition `prop:sharp`, or
Corollary `cor:global`. Those either remain informal or are Lean
composition lemmas under named analytic hypotheses (see README).
-/

open Finset Real
open scoped BigOperators

namespace Palomar

/-- Paper `\label{prop:opnorm}` (level \(j=0\), one dimension):
the \(\ell^1\) norm of the seven-tap kernel \(\tfrac12 R_h\) is \(9/8\). -/
theorem kernel1d_l1 :
    ∑ i : Fin 7, |TWS.Daubechies.kernel1d i| = (9 : ℚ) / 8 := by
  sorry

/-- Paper `\label{prop:opnorm}` over \(\mathbb{R}\): same \(\ell^1\) identity. -/
theorem kernel1d_l1_real :
    ∑ i : Fin 7, |(TWS.Daubechies.kernel1d i : ℝ)| = (9 : ℝ) / 8 := by
  sorry

/-- Paper `\label{prop:opnorm}`, \(d=2\): separable row-sum
\(\|k_0\|_{\ell^1}^2 = (9/8)^2\). -/
theorem db2_level1_opnorm_d2 :
    ∑ i : Fin 7, ∑ j : Fin 7,
        |((TWS.Daubechies.kernel1d i : ℝ) * (TWS.Daubechies.kernel1d j : ℝ))| =
      ((9 : ℝ) / 8) ^ 2 := by
  sorry

/-- Paper `\label{eq:opnorm}` in \(d=2\): \((9/8)^2 = 81/64\). -/
theorem db2_level1_opnorm_d2_num :
    ((9 : ℝ) / 8) ^ 2 = 81 / 64 := by
  sorry

/-- Paper `\label{prop:opnorm}` via the db2 QMF: half-autocorrelation
\(\ell^1\) equals \(9/8\). -/
theorem half_autocorr_l1 :
    |TWS.Daubechies.autocorr 3 / 2| + |TWS.Daubechies.autocorr 2 / 2| +
      |TWS.Daubechies.autocorr 1 / 2| + |TWS.Daubechies.autocorr 0 / 2| +
      |TWS.Daubechies.autocorr 1 / 2| + |TWS.Daubechies.autocorr 2 / 2| +
      |TWS.Daubechies.autocorr 3 / 2| = (9 : ℝ) / 8 := by
  sorry

/-- Paper `\label{lem:revtri}`: reverse triangle for the \(L^2(U)\)
seminorm (mathlib `MemLp` encoding of square-integrability on \(U\)). -/
theorem l2_norm_rev_tri (f g : ℝ → ℝ) (U : Set ℝ)
    (hf : MeasureTheory.MemLp (U.indicator f) 2)
    (hg : MeasureTheory.MemLp (U.indicator g) 2) :
    |TWS.L2Norm f U - TWS.L2Norm g U| ≤ TWS.L2Norm (fun t => f t - g t) U := by
  sorry

/-- Algebraic core of paper `\label{cor:energy}`:
\(|a^2-b^2|\le\Gamma(a+b)\) when \(|a-b|\le\Gamma\). -/
theorem energy_stability (a b Γ : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : |a - b| ≤ Γ) :
    |a ^ 2 - b ^ 2| ≤ Γ * (a + b) := by
  sorry

end Palomar
