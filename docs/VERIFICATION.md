# Verification status

This is not a release certificate or a Palomar registration. A successful
Comparator run accepts the proofs of one commit. It does not review the
mathematical interest of a later commit, and it does not register anything.

## Chronology

The counts below are the counts at the time of each check. The current
selection has **nineteen** statements; the revisions described below had
fourteen or twenty-two. Calling an earlier check a check of the current
nineteen would be false. The three conditional summary results are retained
in `Solution.lean` but are no longer selected; see
`docs/PALOMAR_CANDIDACY.md`.

1. **Darwin, no sandbox, 2026-10-17.** `lake build`, `#print axioms`, and
   `lake comparator --inadvisably-no-sandbox` on the fourteen statements then
   selected. `bwrap` was absent, so `scripts/verify-comparator.sh` was not
   the command. The log warns that a sandbox-disabled run is not the Palomar
   isolation check.
2. **Linux, with sandbox, on `e6698f3`.** GitHub Actions run
   [39040759159](https://github.com/jelincovil/tws-palomar/actions/runs/39040759159)
   executed `scripts/verify-all.sh` on Ubuntu for
   `e6698f352a4362e01ed84e4e6ece13d0cf431d6d` and printed
   `Your solution is okay!`.
3. **Palomar mechanical review of that same commit.** Verification run
   `39042287485` reported success at 2026-10-17T14:51:48Z. The automated
   editorial review of 2026-10-17T18:57:26Z did not offer registration.
   Neither Palomar step saw the closed form, which was not in the tree.
4. **Closed form, 2026-10-18.** Commit
   `7295c00346b8295d4857a3b2f24a6ad0c037d256` adds the eight cascade-formula
   statements. An unsandboxed Darwin replay accepted all twenty-two.
   GitHub Actions run
   [39093434816](https://github.com/jelincovil/tws-palomar/actions/runs/39093434816)
   ran the sandboxed script on that commit and printed
   `Your solution is okay!`. The docs-only child
   `b9fd1a87127c80bd4099c8f509abfa201fef8ea1` was sandboxed again as run
   [39093722987](https://github.com/jelincovil/tws-palomar/actions/runs/39093722987),
   with the same mechanical result. Those runs are not a Palomar review of
   the closed form.
5. **Comment revision, Linux sandbox.** Commit
   `1121b6d5d00ab04be218fea36a4eb36d5990f287` was pushed and sandboxed by
   GitHub Actions run
   [39096555323](https://github.com/jelincovil/tws-palomar/actions/runs/39096555323).
   The log records bubblewrap, `PASS: static packaging checks; 22 selected
   statements; Challenge 329 lines / 14384 bytes`, and `Your solution is
   okay!`. That run is not a Palomar review. A later commit that only
   records this fact is not run 39096555323.

The table that follows is the 2026-10-17 record. It is kept so that the
earlier claims stay attached to the commit they actually concern.

## Record of 2026-10-17

This table describes the fourteen-statement tree. It is not a description
of the current nineteen statements.

| Check | Result actually obtained |
|---|---|
| JSON, TOML and YAML parsing | Passed (`scripts/preflight.py`, Python 3.14) |
| Required files, module headers and source-size limits | Passed static checks |
| Textual equality of Challenge/Solution definitions and selected signatures | Passed |
| No proof holes/custom axiom declarations in Solution by lexical scan | Passed; the axiom audit below is separate |
| Comparator selection and metadata alignment | Passed static checks |
| Immutable dependency revisions and Mathlib pin/lock agreement | Passed static checks |
| Exact symbolic half-autocorrelation in Q(sqrt(3)) | Passed independent Python check |
| Exact circulant matrices for periods 1 through 16 | Passed independent rational checks |
| Exact two-dimensional tensor matrices for N=4,5,6,7,8 | Passed, including attaining sign signals |
| Zero-dimensional singleton case | Passed exact check |
| 80 seeded generic signed stencils with collisions | Passed exact checks |
| Shell syntax of both verification scripts | Passed `bash -n` in the preparation environment |
| Lean elaboration / `lake build` | Passed locally on 2026-10-17. Toolchain `leanprover/lean4:v4.35.0-rc2`, commit `11acb17ec6b07a8f9e9173e6845197929540936b`, arm64-apple-darwin. Mathlib `065356127b1dc0016f66b7283ce0ce2c4055aa55`. That build had fourteen deliberate `sorry` holes in `Challenge`; the closed-form revision had twenty-two, one per statement then selected. The current `Challenge` has nineteen. |
| `#print axioms` on the fourteen selected theorems of that date | Passed. Each depends only on `propext`, `Classical.choice` and `Quot.sound`. The twenty-two-statement audit is in the closed-form section below. |
| Comparator and independent kernels | Passed locally without the sandbox. `lake comparator --inadvisably-no-sandbox` on Darwin, with the toolchain's `nanoda_bin` and `con-ron`, accepted all fourteen selected theorems, including the four propagation statements and `cascade_level1_opNorm`, `cascade_level2_opNorm`, `cascade_level3_opNorm`. con-ron accepted 15562 declarations. `bwrap` is absent, so `scripts/verify-comparator.sh` itself was not the command that ran. The log warns that a sandbox-disabled run is not the Palomar isolation check. |
| GitHub Actions workflow | Passed on commit `e6698f352a4362e01ed84e4e6ece13d0cf431d6d`. Run [39040759159](https://github.com/jelincovil/tws-palomar/actions/runs/39040759159), job `verify`, on `ubuntu-latest`. It installed bubblewrap and ran `scripts/verify-all.sh`, including `scripts/verify-comparator.sh`. The log records acceptance by con-ron, nanoda and the Lean kernel, then `Your solution is okay!`. |
| Human mathematical review | The Palomar editorial review was automated. No person is recorded as having read it. |
| Palomar mechanical verification | Passed for commit `e6698f352a4362e01ed84e4e6ece13d0cf431d6d`. Verification run `39042287485` reported success at 2026-10-17T14:51:48Z. |
| Palomar registration | Not offered. The automated review of 2026-10-17T18:57:26Z identified authorship wording, a conflicting Comparator account in `NOTICE`, and insufficient research interest. |

The source snapshot hashes are in `docs/evidence/SHA256SUMS.txt`.
They identify the files in this repository root. The Palomar submission
uses the full SHA from `git rev-parse HEAD` after this root is public.
Registration was not offered.
The exact checks and static-check transcripts are in `evidence/`.

## What the Lean run corrected

The first `lake build` of the preparation candidate failed in `Solution.lean`
and did not fail in `Challenge.lean`. Two scripts were changed. The selected
statements were not.

- `unit_le_opNorm` at this Mathlib revision takes the input vector before the
  unit-norm hypothesis. Both call sites now pass `signSignal k`.
- `sub_right_cancel` is not declared at this revision. `db2Offset_injective`
  unfolds the offset and cancels the shared shift with `sub_add_cancel`.

A second `lake build` then succeeded, and `lake env lean AxiomAudit.lean`
printed the axiom list above.

## Cascade levels 1, 2 and 3

The same toolchain run includes three further selected statements. Each sums
the absolute values of the integer five-tap recurrence and invokes the existing
folding and tensor theorems. The decided sums are 1196, 38652 and 1239964, at
scales 1024, 32768 and 1048576, which reduce to `299/256`, `9663/8192` and
`309991/262144`. The thresholds are `N >= 19`, `N >= 43` and `N >= 91`.
No closed form for every level was stated in that revision. The unsandboxed Darwin
replay above accepted these three statements together with the previous eleven.
The closed form was added later; its checks are in the next section.

## Environment limits that remain

The preparation container could not start the Linux Lean binary. The local
elaboration above was on Darwin, with oleans from `lake exe cache get`. The
checked-in manifest was adapted from the official template and was not
regenerated by `lake update`. On that Darwin machine `bwrap` is absent, so
`scripts/verify-comparator.sh` was not the local command. The unsandboxed
replay is recorded separately from the later sandboxed runs.

GitHub Actions run 39040759159 executed `scripts/verify-all.sh` on Ubuntu for
commit `e6698f352a4362e01ed84e4e6ece13d0cf431d6d`. Palomar verification run
39042287485 then accepted that commit. The automated editorial review did not
offer registration. Neither run covers the closed-form statements below.

## Closed form for every cascade level

Checked on 2026-10-18 on arm64-apple-darwin, Lean v4.35.0-rc2
(`11acb17ec6b07a8f9e9173e6845197929540936b`). Mathlib stayed at
`065356127b1dc0016f66b7283ce0ce2c4055aa55`. `lake update` was not run.

`lake build` completed (`BUILD_EXIT:0`, 3095 jobs). `scripts/preflight.py`
accepted 22 selected statements. On that tree Challenge was 329 lines and
14307 bytes.
`scripts/check_exact_cases.py` passed; those finite checks do not prove the
universal statements. `lake env lean AxiomAudit.lean` reported only
`propext`, `Classical.choice` and `Quot.sound` for all twenty-two theorems,
including `cascade_l1_formula`, `cascade_opNorm_formula`,
`cascade_opNorm_uniform`, `cascade_l1_gap`, `cascade_l1_succ_lt`,
`cascade_l1_tendsto`, `cascade_uniform_constant_least` and
`cascade_opNorm_d_zero`.

The Darwin Comparator replay was

```
lake comparator --config <temp> --inadvisably-no-sandbox
```

The log begins `WARNING: Sandbox disabled, this run is not trustworthy.`
con-ron accepted 16500 declarations, and nanoda and the Lean kernel accepted
the solution. The replay ended `Your solution is okay!` with
`COMPARATOR_EXIT:0`. `bwrap` is absent, so `scripts/verify-comparator.sh` was
not the command that ran. This is not a Linux sandbox check.

GitHub Actions run 39093434816 then executed `scripts/verify-all.sh` on Ubuntu
for commit `7295c00346b8295d4857a3b2f24a6ad0c037d256`. The log contains
`PASS: static packaging checks; 22 selected statements` and
`Your solution is okay!`. That run is the sandboxed Comparator check of the
closed-form statements. It does not decide Palomar registration.

## Comment revision, rechecked locally on 2026-10-18

After `b9fd1a8`, two docstrings and one Challenge comment were corrected.
`cascade_uniform_constant_least` no longer says that both sides equal 1 at
dimension zero. `cascade_l1_formula` now says that its statement is the
periodized mass, and that the free mass does not depend on `N`. The proof
terms are those of `7295c00`. The file blobs are not.

On arm64-apple-darwin, Lean `v4.35.0-rc2`
(`11acb17ec6b07a8f9e9173e6845197929540936b`), Mathlib
`065356127b1dc0016f66b7283ce0ce2c4055aa55`:

- `scripts/preflight.py` printed
  `PASS: static packaging checks; 22 selected statements; Challenge 329 lines / 14384 bytes.`
- `scripts/check_exact_cases.py` passed. Those finite checks do not prove the
  universal statements.
- `lake build` completed (`BUILD_EXIT:0`, 3095 jobs). Challenge warned on its
  twenty-two deliberate `sorry` holes.
- `lake env lean AxiomAudit.lean` reported only `propext`, `Classical.choice`
  and `Quot.sound` for all twenty-two selected theorems (`AXIOM_EXIT:0`).
- The Darwin Comparator command was
  `lake comparator --config <temp> --inadvisably-no-sandbox`.
  The log begins `WARNING: Sandbox disabled, this run is not trustworthy.`
  con-ron accepted 16500 declarations, nanoda and the Lean kernel accepted
  the solution, and the log ends `Your solution is okay!` with
  `COMPARATOR_EXIT:0`. `bwrap` is absent, so `scripts/verify-comparator.sh`
  was not the command. `external_kernels` was injected only into a temporary
  config and is not in the committed `comparator.json`.

GitHub Actions run
[39096555323](https://github.com/jelincovil/tws-palomar/actions/runs/39096555323)
then executed `scripts/verify-all.sh` on Ubuntu for commit
`1121b6d5d00ab04be218fea36a4eb36d5990f287`. Bubblewrap was installed on
that runner. The log contains `PASS: static packaging checks; 22 selected
statements; Challenge 329 lines / 14384 bytes` and `Your solution is okay!`.
Runs 39093434816 and 39093722987 remain the sandboxed checks of `7295c00`
and `b9fd1a8`. Run 39096555323 is the sandboxed check of `1121b6d`. It does
not cover a later commit that only records this paragraph, and it does not
decide Palomar registration.
