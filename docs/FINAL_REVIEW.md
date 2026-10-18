# Final review of the db2 cascade candidate

This note is the maintainer's audit record for the local revision that
follows commit `b9fd1a87127c80bd4099c8f509abfa201fef8ea1`. It is not a
Palomar registration and it does not name its own commit: the SHA of the
commit that contains this file is `git rev-parse HEAD` after that commit,
and that SHA has not been pushed.

## Base and final state

- Base of this revision: `b9fd1a87127c80bd4099c8f509abfa201fef8ea1` on
  `main`, equal to `origin/main` at the start of the review.
- Mathematical parent: `7295c00346b8295d4857a3b2f24a6ad0c037d256`, whose
  proof terms are unchanged. The only Lean edits are comments.
- The working tree is the candidate. It is a local commit on `main` when
  this review is committed. It is not on GitHub. Palomar cannot fetch it
  until it is pushed. This revision does not push and does not open
  `https://submit.palomar-registry.org/`.

## Files and why they changed

- `docs/CASCADE_THEOREM.md`, new. Exposition of the argument that is
  actually in `Solution.lean`.
- `docs/RELATED_WORK.md`, new. Literature comparison and the open
  originality conclusion.
- `docs/FINAL_REVIEW.md`, new. This record.
- `README.md`. The formula and the least uniform constant lead. Proposition
  3.4 is identified as the case `j = 0`.
- `formalization.yaml`. Alignment is mathematical correspondence.
  `partial` is reserved for the three summary statements whose landscape
  or bottleneck hypotheses stay external. The closed-form statements are
  `proved` relative to the cascade note. The manuscript levels stay
  `adapted`.
- `Challenge.lean`, `Solution.lean`. Comments only. The least-constant
  docstring now says that at `d = 0` the conclusion is `1 ≤ B`. The
  formula docstring now separates the periodized mass from the free mass.
- `docs/VERIFICATION.md`, `docs/PROVENANCE.md`, `NOTICE`,
  `AUDITORIA_ES.md`, `docs/MATHEMATICAL_AUDIT.md`. Chronology, authorship
  of the prose, and the distinction between free mass and periodized mass.
- `docs/evidence/static-checks.txt` and `docs/evidence/SHA256SUMS.txt`.
  Current static transcript and hashes. The sums file does not hash itself.
  The manuscript hash is unchanged.

Unchanged on purpose: `comparator.json`, `AxiomAudit.lean`, the theorem
statements, the definitions, the Mathlib pin, and
`docs/manuscript-source.pdf`.

## Mathematical coherence

The selection contains the general periodized formula
(`cascade_l1_formula`), the operator norm when `N` is at least the support
(`cascade_opNorm_formula`), the uniform bound (`cascade_opNorm_uniform`),
its optimality (`cascade_uniform_constant_least`), and the announced
convergence properties of the free mass (`cascade_l1_gap`,
`cascade_l1_succ_lt`, `cascade_l1_tendsto`). Dimension zero is
`cascade_opNorm_d_zero`. The finite levels remain selected and agree with
`c_1`, `c_2`, and `c_3`.

The free mass does not depend on `N`. The selected formula is the folded
sum, under the sufficient condition `N ≥ S_j`. The identity `m_j = c_j`
with no period is `cascade_l1_series`, used by the selected statements and
not itself selected. No new theorem was added to close that gap.

The least-constant proof evaluates the norm at the support, which grows
with the level, and passes to the limit. It does not assume `L^d ≤ B`.
At `d = 0` that theorem concludes `1 ≤ B` and does not conclude `B = 1`.
Each individual zero-dimensional norm is 1 by the empty product.

The definitions are still convolution, folding, and the integer cascade.
No `sorry`, `admit`, or new axiom was added to `Solution.lean`. The
twenty-two holes in `Challenge.lean` are the Comparator interface.

No discrepancy required a change of a theorem type.

## Bibliographic conclusion

**C. The originality of the closed form remains unresolved.**

The missing comparison is a reading of the full texts of Amat–Moncayo
2008 (DOI 10.1016/j.amc.2008.08.047) and Amat–Moncayo 2009
(DOI 10.1016/j.matcom.2009.04.005), checking the filter, the operator and
the norm, and whether any constant equals `9/8`, `299/256`, `9663/8192`,
`309991/262144`, or `1651/1395`. The abstracts do not settle it. A search
for `1651/1395` is not a novelty claim. Saito's coauthor on the
autocorrelation papers is Gregory Beylkin. The mask `k_0` is half of the
interpolatory four-point mask; those operators were not identified. Detail
is in `docs/RELATED_WORK.md`. Moncayo–Amat 2011 is recorded as future work
and was not pursued.

## Checks and evidence

All of the following were run in this working tree, on arm64-apple-darwin,
Lean `v4.35.0-rc2` commit `11acb17ec6b07a8f9e9173e6845197929540936b`,
Mathlib `065356127b1dc0016f66b7283ce0ce2c4055aa55`.

| Check | Result |
|---|---|
| `scripts/preflight.py` | Pass. 22 statements. Challenge 329 lines, 14384 bytes. |
| `scripts/check_exact_cases.py` | Pass. Finite checks only. |
| `lake build` | `BUILD_EXIT:0`, 3095 jobs. Twenty-two `sorry` warnings, all in Challenge. |
| `lake env lean AxiomAudit.lean` | `AXIOM_EXIT:0`. Each selected theorem depends only on `propext`, `Classical.choice`, `Quot.sound`. |
| Darwin Comparator | `lake comparator --config <temp> --inadvisably-no-sandbox`. Log starts `WARNING: Sandbox disabled, this run is not trustworthy.` con-ron accepted 16500 declarations. nanoda and the Lean kernel accepted the solution. `Your solution is okay!` and `COMPARATOR_EXIT:0`. |

`bwrap` is absent, so `scripts/verify-comparator.sh` was not the local
command. `external_kernels` was written only into a temporary config.

These local commands do not inherit an Actions run id. The sandboxed
checks that still apply to the proof terms are:

- Actions `39093434816` on `7295c00`;
- Actions `39093722987` on `b9fd1a8`, which did not contain this review.

Palomar run `39042287485` accepted only `e6698f3` and did not offer
registration. It did not see the closed form.

## What is still pending

- A Linux bubblewrap run of the commit that contains this review. It needs
  a push, which was not authorized.
- The full-text comparison named under the bibliographic conclusion.
- The maintainer's reading of the cascade note before any submission.
- Palomar's editorial decision, which is not made by a successful kernel
  check.

The separate equality "the positive-dimensional norm at period 1 equals 1"
is not proved and is not selected. The uniform inequality includes `N = 1`.

## Readiness

The repository is coherent enough for the maintainer's audit: the selected
statements match the note, the note matches the lemmas, and the
uncertainties are written down. A new submission is a later decision.
Before that submission the commit must be pushed, and the Linux sandbox
should be the one that runs on that same commit. Nothing here promises
that Palomar will offer registration.

## Four separate questions

1. **Formal correctness and verification.** The proof terms compiled and
   passed the local unsandboxed Comparator and the axiom audit. The
   sandboxed evidence for those terms is the Actions runs on `7295c00` and
   `b9fd1a8`. The comment revision itself has no Linux run yet.
2. **Correspondence with the mathematical exposition.**
   `docs/CASCADE_THEOREM.md` follows the lemmas that close the mass, the
   norm, the uniform bound, the least constant, and the convergence. The
   free mass is not given an `N` hypothesis.
3. **Scientific interest.** The specific step is the sign control that
   produces one constant for every level. The gain over `(9/8)^{(j+1)d}`
   is real inside this argument and is not, by itself, a priority claim.
   Originality relative to Amat–Moncayo remains open.
4. **Palomar's editorial decision.** Not taken. The earlier automated
   review did not offer registration. This revision does not predict the
   next one.
