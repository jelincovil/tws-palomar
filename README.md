# Palomar surface for the TWS db2 kernel certificate

Comparator wrapper for closed Lean 4 results accompanying

> J. E. Lincovil Curivil, C. D. Reinoso Reinoso, N. Pacheco-Barrios.
> *Explicit \(L^\infty\) stability bounds for undecimated Daubechies
> smoothing and wavelet-filtered persistence landscapes*.
> **arXiv:XXXX.XXXXX** *(placeholder)*.

This repository is **not** the paper and **not** the full reproducibility
package. The manuscript lives in `tws-persistence-stability/paper/main.tex`.
Python/CSV/medical artefacts live in the sibling companion `tws-repro/`.
Proof bodies live in `tws-repro/formalization/` (Lake package `tws`).

## Licence

**Apache-2.0** (Palomar template SPDX). The companion `tws-repro` remains
MIT; Apache-2.0 may depend on MIT. Relicensing applies only to this
wrapper (`Challenge.lean`, `Solution.lean`, metadata), not to a copy of
the TWS sources (those are not vendored).

## What is compared

| Paper label | Lean (Challenge / Solution) | Companion proof |
|-------------|-----------------------------|-----------------|
| `prop:opnorm` \(\ell^1=9/8\) | `Palomar.kernel1d_l1` | `TWS.Daubechies.kernel1d_l1` |
| `prop:opnorm` over \(\mathbb{R}\) | `Palomar.kernel1d_l1_real` | `TWS.Daubechies.kernel1d_l1_real` |
| `prop:opnorm` \(d=2\) | `Palomar.db2_level1_opnorm_d2` | `TWS.Daubechies.db2_level1_opnorm_d2` |
| `eq:opnorm` \(81/64\) | `Palomar.db2_level1_opnorm_d2_num` | `TWS.Daubechies.db2_level1_opnorm_d2_num` |
| `prop:opnorm` QMF | `Palomar.half_autocorr_l1` | `TWS.Daubechies.half_autocorr_l1` |
| `lem:revtri` | `Palomar.l2_norm_rev_tri` | `TWS.l2_norm_rev_tri` |
| `cor:energy` (algebra) | `Palomar.energy_stability` | `TWS.energy_stability` |

**Not compared:** `thm:A`, `lem:landscapeU`, `lem:proj`, `prop:sharp`,
`cor:global`. Lean `TWS.stability_Linf` is a composition *under named
hypotheses*, not a kernel proof of bottleneck stability.

## Build

Toolchain: `leanprover/lean4:v4.33.0`. mathlib: `db584cd6`. Companion pin:
`tws-repro` commit `6f11e6e37039c40fd924146e2d5efdd531950179`.

Until `tws-repro` has a public Git URL, `lakefile.toml` uses

```toml
[[require]]
name = "tws"
path = "../tws-repro/formalization"
```

Palomar CI will **not** resolve that path. After you publish `tws-repro`,
replace it by a `git` + `rev` + `subDir = "formalization"` require (do not
invent the URL).

```bash
cd tws-palomar
lake exe cache get
lake update
lake build
```

## Comparator (Linux; Landrun + NanoDa)

Not run in this packaging step unless the tools are on `PATH`. Upstream:

- https://github.com/leanprover/comparator
- Palomar pins: see PalomarRegistry/PalomarTemplate `scripts/verify-comparator.sh`

```bash
# after installing comparator, lean4export, nanoda, landrun at Palomar revisions:
comparator comparator.json
```

`enable_nanoda` is `true` in `comparator.json`. A local `lake build` is
**not** a NanoDa replay.
