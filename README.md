# Palomar surface for the Lean-checked kernel identities and two auxiliary lemmas of the TWS note

Comparator wrapper for closed Lean 4 results accompanying

> J. E. Lincovil Curivil, C. D. Reinoso Reinoso, N. Pacheco-Barrios.
> *Explicit \(L^\infty\) stability bounds for undecimated Daubechies
> smoothing and wavelet-filtered persistence landscapes*.
> **arXiv:XXXX.XXXXX** *(placeholder)*.

This repository is **not** the paper and **not** the full reproducibility
package. Manuscript: `tws-persistence-stability/paper/main.tex` (CC BY 4.0).
Python/CSV live in https://github.com/jelincovil/tws-repro (MIT).
The Lean library `TWS/` is **vendored** from that companion at commit
`6f11e6e37039c40fd924146e2d5efdd531950179` so Palomar's isolated `lean`
run can find `TWS.olean`.

## Licence

- **`tws-palomar`** (original work: `Challenge.lean`, `Solution.lean`,
  `comparator.json`, `formalization.yaml`, scripts, this README):
  **Apache-2.0**. See `LICENSE`.
- **`TWS/`** (vendored Lean sources from `jelincovil/tws-repro`):
  **MIT**. See `TWS/LICENSE`.
- **Manuscript** (`tws-persistence-stability/paper/main.tex`, not in this
  repository): **CC BY 4.0**.

See `NOTICE` for the full attribution of vendored sources.

## What Lean actually checks (and what it does not)

Seven declarations, matching the paper's Results item on Lean
(`sec:lean`):

1. **Kernel \(\ell^1\)** (`Palomar.kernel1d_l1` and related). The
   seven-tap \(k_0=\tfrac12 R_h\) has \(\ell^1\) norm \(9/8\); the
   separable 2-D row-sum of \(|k_i k_j|\) is \((9/8)^2\).
2. **Two auxiliary lemmas**: the reverse triangle inequality for the
   \(L^2\) seminorm (`Palomar.l2_norm_rev_tri`) and the algebraic core
   of the paper's energy corollary (`Palomar.energy_stability`).

The paper's Theorem A composition (`TWS.stability_Linf`) is **not** part of
this entry: it is a chained inequality under named hypotheses rather than a
kernel-checked TDA theorem, so it is not registered.

Lean does **not** prove
\(\|P_{0,N}^\Psi\|_{L^\infty\to L^\infty}=\|k_0\|_{\ell^1}^d\). That step
(no-cancellation under periodization, \(N\ge 7\)) is a paper argument.

| Paper | Lean constant | What is proved |
|-------|----------------|----------------|
| `prop:opnorm` kernel | `Palomar.kernel1d_l1` | \(\sum\|k_i\|=9/8\) in \(\mathbb{Q}\) |
| same, \(\mathbb{R}\) | `Palomar.kernel1d_l1_real` | same in \(\mathbb{R}\) |
| 2-D row-sum | `Palomar.db2_level1_opnorm_d2` | \(\sum_{i,j}\|k_i k_j\|=(9/8)^2\) |
| arithmetic | `Palomar.db2_level1_opnorm_d2_num` | \((9/8)^2=81/64\) |
| QMF form | `Palomar.half_autocorr_l1` | same \(\ell^1\) via autocorrelation |
| `lem:revtri` | `Palomar.l2_norm_rev_tri` | reverse triangle for `L2Norm` |
| `cor:energy` algebra | `Palomar.energy_stability` | \(\|a^2-b^2\|\le\Gamma(a+b)\) |

The seven Comparator names are seven Lean constants; they encode three
mathematical claims (kernel \(\ell^1\), reverse triangle, energy algebra),
with \(\ell^1\) stated in several equivalent forms.

`Challenge.lean` and `Solution.lean` are **Mathlib-only**: they inline the
definitions they need, so the Challenge's transitive import closure contains
no project-specific code. `TWS/` is kept as the provenance of those inlined
definitions and proof tactics.

## Build

Toolchain: `leanprover/lean4:v4.33.0`.  
mathlib: `db584cd6d46c92f209a44c0f1c829460d327499d`.  
Vendored `TWS/` from https://github.com/jelincovil/tws-repro
commit `6f11e6e37039c40fd924146e2d5efdd531950179`.

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
