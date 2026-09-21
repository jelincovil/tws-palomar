# Palomar surface for two Lean-checked facts of the TWS note

Comparator wrapper for closed Lean 4 results accompanying

> J. E. Lincovil Curivil, C. D. Reinoso Reinoso, N. Pacheco-Barrios.
> *Explicit \(L^\infty\) stability bounds for undecimated Daubechies
> smoothing and wavelet-filtered persistence landscapes*.
> **arXiv:XXXX.XXXXX** *(placeholder)*.

This repository is **not** the paper and **not** the full reproducibility
package. Manuscript: `tws-persistence-stability/paper/main.tex` (CC BY 4.0).
Python/CSV live in https://github.com/jelincovil/tws-repro (MIT).
Proof bodies live in that repo under `formalization/` (Lake package `tws`).

## Licence

**Apache-2.0** for this wrapper (Palomar SPDX, matches `LICENSE`).
Companion `tws-repro` remains MIT. The manuscript is CC BY 4.0.

## What Lean actually checks (and what it does not)

Two facts, matching the paper's Results item on Lean (`sec:lean`):

1. **Composition of the bound** (`Palomar.stability_Linf`). Given named
   hypotheses for landscape \(L^\infty\)-Lipschitz behaviour and an
   \(L^\infty\) operator bound, the \(L^2(U)\) inequality follows.
   Bottleneck stability and landscapes are **not** proved.
2. **Kernel \(\ell^1\)** (`Palomar.kernel1d_l1` and related). The
   seven-tap \(k_0=\tfrac12 R_h\) has \(\ell^1\) norm \(9/8\); the
   separable 2-D row-sum of \(|k_i k_j|\) is \((9/8)^2\).

Lean does **not** prove
\(\|P_{0,N}^\Psi\|_{L^\infty\to L^\infty}=\|k_0\|_{\ell^1}^d\). That step
(no-cancellation under periodization, \(N\ge 7\)) is a paper argument.

| Paper | Lean constant | What is proved |
|-------|----------------|----------------|
| `thm:A` composition | `Palomar.stability_Linf` | chaining under hypotheses |
| `prop:opnorm` kernel | `Palomar.kernel1d_l1` | \(\sum\|k_i\|=9/8\) in \(\mathbb{Q}\) |
| same, \(\mathbb{R}\) | `Palomar.kernel1d_l1_real` | same in \(\mathbb{R}\) |
| 2-D row-sum | `Palomar.db2_level1_opnorm_d2` | \(\sum_{i,j}\|k_i k_j\|=(9/8)^2\) |
| arithmetic | `Palomar.db2_level1_opnorm_d2_num` | \((9/8)^2=81/64\) |
| QMF form | `Palomar.half_autocorr_l1` | same \(\ell^1\) via autocorrelation |
| `lem:revtri` | `Palomar.l2_norm_rev_tri` | reverse triangle for `L2Norm` |
| `cor:energy` algebra | `Palomar.energy_stability` | \(\|a^2-b^2\|\le\Gamma(a+b)\) |

The eight Comparator names are eight Lean constants; they encode four
mathematical claims (composition, kernel \(\ell^1\), reverse triangle,
energy algebra), with \(\ell^1\) stated in several equivalent forms.

`Challenge.lean` imports `TWS.Skeleton` because Fact 1 lives there, not
because the Challenge re-proves the skeleton.

## Build

Toolchain: `leanprover/lean4:v4.33.0`.  
mathlib: `db584cd6d46c92f209a44c0f1c829460d327499d`.  
Companion: https://github.com/jelincovil/tws-repro  
commit `6f11e6e37039c40fd924146e2d5efdd531950179` (`subDir = formalization`).

```bash
cd tws-palomar
lake exe cache get
lake update
lake build
```

## Comparator

Local verification **was run** on this machine (Darwin) with
`./scripts/verify-comparator.sh`. Output:

```
Nanoda kernel accepts the solution
Lean default kernel accepts the solution
Your solution is okay!
```

Re-run after changing Challenge/Solution:

```bash
./scripts/verify-comparator.sh
```

Pins: Comparator `68a0641`, lean4export `15f6055` (v4.33.0), NanoDa
`68d5ca9`, Landrun `811cfff`. A bare `lake build` is not a NanoDa replay.
`enable_nanoda` is `true`.
