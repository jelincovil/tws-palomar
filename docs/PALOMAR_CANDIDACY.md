# Palomar candidacy note

Date: 2026-10-19. Status: **prepared, not submitted** (`NO_SOMETIDA`).

## Rejection being answered

The facilitated message reports the following. It is recorded here as reported; the
repository contains no receipt for this review.

- Date of the facilitated decision: `2026-10-19T00:46:22Z`.
- Mechanical verification: passed.
- Automated editorial review: the research interest of the conditional summary-stability
  group was rejected. The Lipschitz and seminorm-comparison bounds are hypotheses that the
  results only propagate through the smoothing operator.
- Submitted SHA and Palomar submission identifier: **unknown**. No receipt is present, and
  the SHA is not inferred from the local HEAD.

The September 2026 files in `palomar-feedback/` belong to an earlier submission with seven
selected statements. They are not evidence for this review.

## What changed in the candidacy

The selection goes from 22 to **19** statements. Exactly three were withdrawn from
`comparator.json` and from `Challenge.lean`:

- `TWSPeriodic.summary_bound_propagation`
- `TWSPeriodic.db2_summary_stability`
- `TWSPeriodic.db2_squared_summary_stability`

They remain in `Solution.lean` unchanged, as auxiliaries outside the selected surface.
No theorem, hypothesis, axiom or proof script was added, removed or weakened. `Solution.lean`,
the Mathlib pin and the toolchain are byte-identical to the closure
`59799c3c08c7b763c58a35e9af40a35ee5bfd1b5`.

## Contribution presented

**Main contribution.**

- `cascade_opNorm_formula`: for every level `j` and dimension `d`, and every period
  `N ≥ S_j = 6·2^{j+1} − 5` (the support condition), the operator norm is `c_j^d`, with
  `c_j = 1651/1395 − (4/63)4^{-j} + (1/180)16^{-j} − (1/1736)32^{-j}`.
- `cascade_opNorm_uniform`: for every positive period, aliasing included, the norm is at most
  `(1651/1395)^d`.
- `cascade_uniform_constant_least`: any real `B` bounding the operator at every level and
  every positive period satisfies `(1651/1395)^d ≤ B`. The witnessing periods are the
  supports and may grow with the level; no single fixed period is claimed to attain the
  constant.

**Supporting results.**

- The standard finite theory: `convolution_opNorm`, `periodization_norm`,
  `tensor_convolution_opNorm`.
- The level-one db2 computation and its least constant: `db2_filter_identification`,
  `db2_opNorm`, `db2_attains`, `db2_lipschitz`, `db2_opNorm_least`.
- Finite cascade levels: `cascade_level1_opNorm`, `cascade_level2_opNorm`,
  `cascade_level3_opNorm`.
- The free-mass analysis behind the constant: `cascade_l1_formula`, `cascade_l1_gap`,
  `cascade_l1_succ_lt`, `cascade_l1_tendsto`.
- Dimension zero: `cascade_opNorm_d_zero`, where every norm is `1` and the least-constant
  theorem concludes only `1 ≤ B`.

**Auxiliaries, not selected.** The three conditional summary results above. They assume
bottleneck stability and landscape non-expansiveness through named hypotheses; they do not
prove persistence stability, and they are not presented as a contribution.

**Separate work, not part of this candidacy.** The nonperiodic endpoint-replication
extension in `extension/` (certificates for `directOp`, constant preservation, its own axiom
audit and workflow). Palomar's comparator reads only `Challenge` and `Solution`, so the
extension is not part of the verified surface of this submission.

## Claims kept precise

- The norm formula requires the support condition `N ≥ S_j`; sufficiency of that condition is
  not claimed to be necessary.
- The uniform bound holds for every `N ≥ 1`; aliasing can only lower the folded mass.
- Optimality quantifies over all levels and all positive periods simultaneously.
- The free (unsigned) mass `c_j`, the absolute mass and the periodized mass are distinct
  objects; only the identities proved in `Solution.lean` are claimed.
- At dimension zero the least-constant statement is `1 ≤ B`, not `B = 1`.
- No bibliographic priority, absolute novelty or editorial acceptance is claimed.

## Verification state

Local checks are recorded in `docs/evidence/` and in `verification-logs/candidacy/`.
The Linux sandboxed Comparator run is pending; it is provided by the existing GitHub Actions
workflow on push, not by a local sandbox. `CIERRE.md` records the extension verification
separately.

Palomar status: **NO_SOMETIDA**. No submission identifier is recorded.
