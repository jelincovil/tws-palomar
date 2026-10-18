# Threshold certificates after a bounded smoothing operator, with a db2-cascade bridge

This file specifies the extension and maps every claim to a Lean declaration.

* Abstract layer: `ThresholdExtension/ThresholdCertificate.lean`, namespace `ThresholdCert`.
* db2 bridge: `ThresholdExtension/Db2ThresholdCertificate.lean`, namespace `ThresholdCert.Db2`.

Paths are relative to the `extension/` directory. Build and verification details are in
`INTEGRATION.md` and `VERIFICATION.txt`.

## 0. Provenance of the abstract module: recovered, with listed edits

The previous session's file `RequestProject/ThresholdCertificate.lean` and its spec
`docs/THRESHOLD_CERTIFICATE_SPEC.md` were still present in the project, so they were read and
reused, not reconstructed. The abstract module was moved, under git, to
`extension/ThresholdExtension/ThresholdCertificate.lean`. Every theorem and counterexample from
the earlier file is kept. The edits are:

1. Deprecation fix: `Set.mem_setOf_eq` became `Set.mem_ofPred_eq`, the replacement named by the
   pinned Mathlib. This changes no statement.
2. `certifiedNotAbove_sound` now concludes `T x i ≤ τ` instead of `¬ τ < T x i`, to match the
   requested form. The two are logically equivalent. `raw_notAbove_sound` was changed the
   same way, to `x i ≤ τ`.
3. Added `trichotomy_of_bounds`, the partition with `0 ≤ B * ε` derived from `‖T‖ ≤ B` and
   `‖y - x‖ ≤ ε`.
4. Added `uncertaintyBand_eq_empty_of_mul_eq_zero`, split out of the proof of
   `superlevel_eq_of_mul_eq_zero`, so that "band empty" is a theorem in its own right.

**Correction to the previous report.** It said the abstract file compiled with "Lean 4.28.0".
The Lean binary actually installed here is 4.35.0-rc2 (see `VERIFICATION.txt`), and the earlier
session very likely used the same binary. That earlier version claim should be read as
unverified. All checks reported now were run under Lean 4.35.0-rc2 with Mathlib at the pinned
commit `065356127b1dc0016f66b7283ce0ce2c4055aa55`.

## A. Definitions

Setting: `I` and `J` are `Fintype`s. The spaces `I → ℝ` and `J → ℝ` carry Mathlib's finite Pi
norm, the supremum norm \(\|z\| = \max_k |z_k|\). We have
`T : (I → ℝ) →L[ℝ] (J → ℝ)`, `B ε τ : ℝ` and `x y : I → ℝ`, and we write \(m = B\varepsilon\).

| Concept | Lean (namespace `ThresholdCert`) | Meaning |
|---|---|---|
| certified above | `CertifiedAbove T B ε τ y i` | `τ + B * ε < T y i` |
| certified not above | `CertifiedNotAbove T B ε τ y i` | `T y i ≤ τ - B * ε` |
| uncertified | `Uncertified T B ε τ y i` | `τ - B * ε < T y i ∧ T y i ≤ τ + B * ε` |
| superlevel set | `superlevel T τ z` | `{i | τ < T z i}`; \(S_y\) = `superlevel T τ y`, \(S_x\) = `superlevel T τ x` |
| uncertainty band | `uncertaintyBand T B ε τ y` | `{i | Uncertified T B ε τ y i}` |

The target is `τ < T x i`, a statement about the smoothed reference \(Tx\). It is **not** `τ < x i`.

**Choice of hypotheses.** No theorem assumes `0 ≤ B` or `0 ≤ ε`. Both follow from `‖T‖ ≤ B`
and `‖y - x‖ ≤ ε`, and the proofs derive them. The one exception is `trichotomy`, which is a
pure order fact about three predicates and takes `0 ≤ B * ε` explicitly.
`trichotomy_of_bounds` is the same result with that hypothesis derived. Nonemptiness of
`I` and `J` is not needed.

## B. Theorems and informal proofs

All theorems below assume `hT : ‖T‖ ≤ B` and `hxy : ‖y - x‖ ≤ ε` unless stated otherwise.

1. **Coordinatewise perturbation.** `coord_perturbation : |T y i - T x i| ≤ B * ε`.
   *Proof.* By linearity, \((Ty)_i-(Tx)_i = (T(y-x))_i\). Then
   \(|(T(y-x))_i| \le \|T(y-x)\| \le \|T\|\,\|y-x\| \le B\varepsilon\). The last step uses
   \(0\le\|y-x\|\) and \(0\le\|T\|\le B\).
2. **Soundness of "certified above".** `certifiedAbove_sound : CertifiedAbove … → τ < T x i`.
   *Proof.* \((Tx)_i \ge (Ty)_i - m > \tau\).
3. **Soundness of "certified not above".** `certifiedNotAbove_sound : CertifiedNotAbove … → T x i ≤ τ`.
   *Proof.* \((Tx)_i \le (Ty)_i + m \le \tau\).
4. **Partition.** `trichotomy (hBε : 0 ≤ B * ε)` and `trichotomy_of_bounds hT hxy`: at every
   `i`, exactly one of the three predicates holds. The statement is a three-way disjunction,
   and each disjunct asserts one predicate and negates the other two.
   *Proof.* Since \(\tau-m\le\tau+m\), the conditions \(v>\tau+m\), \(v\le\tau-m\) and
   \(\tau-m<v\le\tau+m\) split \(\mathbb R\) into three disjoint pieces.
5. **Symmetric difference lies in the band.**
   `symmDiff_subset_band : symmDiff (superlevel T τ y) (superlevel T τ x) ⊆ uncertaintyBand T B ε τ y`.
   A refined directional version, `diff_subsets`, gives:
   * false positives: \(S_y\setminus S_x \subseteq \{\tau < (Ty)_i \le \tau+m\}\);
   * false negatives: \(S_x\setminus S_y \subseteq \{\tau-m < (Ty)_i \le \tau\}\).

   *Proof.* If \((Ty)_i>\tau\ge(Tx)_i\), then \((Ty)_i\le(Tx)_i+m\le\tau+m\). If
   \((Tx)_i>\tau\ge(Ty)_i\), then \((Ty)_i\ge(Tx)_i-m>\tau-m\). Since \(m\ge0\), both cases lie
   in the band.
6. **The case \(B\varepsilon=0\).** `uncertaintyBand_eq_empty_of_mul_eq_zero (h0 : B * ε = 0)`
   shows the band is empty; this needs no norm hypotheses. `superlevel_eq_of_mul_eq_zero hT hxy h0`
   shows \(S_y=S_x\).
   *Proof.* The band becomes \(\{\tau<v\le\tau\}=\emptyset\); then apply 5.

**Additional results kept from the previous session:**

* **Decisions about `x` itself** require the extra modelling assumption `I = J` and
  `hδ : ‖T x - x‖ ≤ δ`. Under it the margin becomes \(B\varepsilon+\delta\):
  * `raw_above_sound`: `τ + B*ε + δ < T y i → τ < x i`;
  * `raw_notAbove_sound`: `T y i ≤ τ - B*ε - δ → x i ≤ τ`.

  Nothing in the baseline supplies δ, and no denoising-accuracy claim is made.
* **Counterexamples, proved in Lean** (one coordinate, `T = id`, `B = ε = 1`, `τ = 0`, `x = 0`,
  `y = 1`, unless stated otherwise):
  * `nonstrict_above_unsound`: certifying "above" when `τ + B ε ≤ T y i` is unsound.
  * `open_band_fails`: the band open at both ends, `τ - Bε < T y i < τ + Bε`, does not contain
    the symmetric difference.
  * `uncertified_not_wrong`: with `T = 0`, the valid loose bound `B = 1`, `ε = 1` and `τ = 0`,
    the coordinate is uncertified even though "not above" is correct for every `x`.
    "Uncertified" means "the certificate cannot decide", not "known wrong".
  * `smoothed_cert_not_raw_cert`: a certificate about `T x` says nothing about `x`. Take
    `T = 0`, `ε = 0`, `x = y = 1`, `τ = 0`: the coordinate is certified not above for `T x`,
    yet `x 0 = 1 > τ`.

## C. Boundary conventions and why they are forced

Let \(v=(Ty)_i\). Given only \(|v-(Tx)_i|\le m\), the possible values of \((Tx)_i\) form the
closed interval \([v-m,v+m]\), and with `T = id` every value in it occurs. The target is strict
(\(>\tau\)), so:

* "above" is guaranteed iff \(v-m>\tau\). The inequality must be **strict**: with `≥` it is
  unsound (`nonstrict_above_unsound`).
* "not above" is guaranteed iff \(v+m\le\tau\). The inequality can be **non-strict**: the
  lower boundary \(v=\tau-m\) gives \((Tx)_i\le\tau\), which is correct.
* The remaining band, \(\tau-m<v\le\tau+m\), is **open on the left and closed on the right**.
  Closing the left end as well is sound but wasteful: at \(m=0\) it would flag \(v=\tau\) even
  with exact data. Opening the right end is unsound (`open_band_fails`).

Special cases:

* `ε = 0` or `B = 0`: then `B * ε = 0`, the band is empty, and \(S_y=S_x\).
* `B = 0` forces `‖T‖ = 0`, i.e. `T = 0`. Then \(Ty=Tx=0\), and every coordinate is "above" iff
  \(0>\tau\).
* Zero operator with a loose bound: see `uncertified_not_wrong`.

**Soundness versus completeness.** The certificate is sound: certified verdicts are correct
for every `x` with `‖y - x‖ ≤ ε`. It is not claimed complete for a fixed operator under a loose
global `B`. *Informal, not formalized:* the exact worst case at row `i` is \(r_i\varepsilon\),
where \(r_i=\sum_k|T_{ik}|\). The global margin \(B\varepsilon\ge r_i\varepsilon\) can be strictly
wider.

## D. db2 bridge (namespace `ThresholdCert.Db2`)

The operator is `TWSPeriodic.cascadeOperator j N 1` from the baseline `Solution.lean`. Its
type is `((Fin 1 → ZMod N) → ℝ) →L[ℝ] ((Fin 1 → ZMod N) → ℝ)`, and the signal index type
`Fin 1 → ZMod N` is used unchanged. A positive period is expressed by the baseline's own
instance argument `[NeZero N]`.

| Lean declaration | Statement | Derived from (baseline) |
|---|---|---|
| `cascadeL` (def) | `(1651 : ℝ) / 1395` | — |
| `cascadeC j` (def) | `1651/1395 - (4/63)(1/4)^j + (1/180)(1/16)^j - (1/1736)(1/32)^j`, in `ℝ` | — |
| `cascade1_opNorm_le_L j N` | `‖cascadeOperator j N 1‖ ≤ cascadeL` | `TWSPeriodic.cascade_opNorm_uniform j N 1`, with `pow_one` by `simp` |
| `cascade1_opNorm_eq_C j N hN` | `cascadeSupport j ≤ N → ‖cascadeOperator j N 1‖ = cascadeC j` | `TWSPeriodic.cascade_opNorm_formula j N 1 hN` |
| `cascadeC_nonneg j` | `0 ≤ cascadeC j` | the norm identity at `N = cascadeSupport j`, plus `norm_nonneg` |
| `cascadeC_le_L j` | `cascadeC j ≤ cascadeL` | both baseline theorems at `N = cascadeSupport j` |
| `coord_perturbation_uniform` | `‖y - x‖ ≤ ε → |C y i - C x i| ≤ cascadeL * ε` | abstract 1 + `cascade1_opNorm_le_L` |
| `certifiedAbove_sound_uniform` | `CertifiedAbove C cascadeL ε τ y i → τ < C x i` | abstract 2 |
| `certifiedNotAbove_sound_uniform` | `CertifiedNotAbove C cascadeL ε τ y i → C x i ≤ τ` | abstract 3 |
| `symmDiff_subset_band_uniform` | `symmDiff (superlevel C τ y) (superlevel C τ x) ⊆ uncertaintyBand C cascadeL ε τ y` | abstract 5 |
| `superlevel_eq_uniform_of_eps_zero` | `‖y - x‖ ≤ 0 → superlevel C τ y = superlevel C τ x` | abstract 6 |
| `coord_perturbation_exact` | with `hN : cascadeSupport j ≤ N`: `|C y i - C x i| ≤ cascadeC j * ε` | abstract 1 + `cascade1_opNorm_eq_C` |
| `certifiedAbove_sound_exact` | with `hN`: `CertifiedAbove C (cascadeC j) ε τ y i → τ < C x i` | abstract 2 |
| `certifiedNotAbove_sound_exact` | with `hN`: `CertifiedNotAbove C (cascadeC j) ε τ y i → C x i ≤ τ` | abstract 3 |
| `symmDiff_subset_band_exact` | with `hN`: the symmetric difference lies in `uncertaintyBand C (cascadeC j) ε τ y` | abstract 5 |
| `band_exact_subset_uniform` | `0 ≤ ε →` the exact-level band is contained in the uniform-level band | `cascadeC_le_L` |

Here `C` stands for `cascadeOperator j N 1`.

**What is and is not assumed.** No specialised theorem has a norm hypothesis. The bounds
`‖C‖ ≤ 1651/1395` and `‖C‖ = c_j` are obtained inside the proofs from the imported baseline
theorems. The only remaining hypotheses are:

* the noise bound `‖y - x‖ ≤ ε`;
* `cascadeSupport j ≤ N`, for the exact level only;
* the instance `[NeZero N]`, which the baseline operator itself requires.

**Nonnegativity of \(c_j\)** comes from the norm identity, not from new arithmetic. The
abstract theorems do not need it anyway, because they derive `0 ≤ B` from `‖T‖ ≤ B`.

**Informal remark, not formalized.** The inequality \(c_j<L\) is strict, since
\((4/63)4^{-j} > (1/180)16^{-j}\). Only `c_j ≤ L` is proved in Lean.

## E. Scope statement

* Only periodic, one-dimensional signals (`d = 1`) are covered.
* The result certifies decisions about `T x`, not about the unsmoothed `x`. It establishes no
  denoising accuracy and is not a research result. It is an elementary threshold lemma that
  applies the existing cascade theorems.
* The nonperiodic operator additionally preserves constants and is the identity at `n = 1`
  (`ThresholdCert.Nonperiodic.directOp_const`, `directOp_one_eq_id`, in
  `ThresholdExtension.ConstantPreservation`). Those facts are not used by the abstract
  certificates below; they are recorded because they are part of the closed formal phase.
* No boundary extension, persistence diagrams, adaptive scale selection, noise estimation or
  floating-point reasoning is involved.
