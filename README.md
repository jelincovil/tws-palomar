# Exact sup norms for periodic db2 smoothing

**Corrected candidate, not a Palomar registration.** The proofs in
`Solution.lean` elaborate with Lean `v4.35.0-rc2` and the pinned Mathlib.
A local `lake build`, `#print axioms` and an unsandboxed Darwin Comparator
replay succeeded on 2026-10-17; see
[verification status](docs/VERIFICATION.md). `scripts/verify-comparator.sh`
itself did not run: it requires bubblewrap, which is absent on this Darwin
machine. See the [Spanish replacement guide](AUDITORIA_ES.md).

## Mathematical result

Let `G` be a finite abelian group and let

\[
(C_k f)(x)=\sum_{y\in G} k(y)f(x-y).
\]

Both function spaces carry the ordinary maximum absolute-value norm. We use
Mathlib's actual `ContinuousLinearMap` operator norm and finite Pi norm:

\[
\|C_k\|_{\infty\to\infty}=\sum_{y\in G}|k(y)|.
\]

The matching lower bound is witnessed by the real sign signal
`f(x) = 1` when `k(-x) >= 0`, and `f(x) = -1` otherwise.

For a finite stencil `a : I -> R` and offsets `q : I -> G`, we first **sum
colliding coefficients**. This gives the exact periodized kernel. Its l1
mass never exceeds the original stencil's l1 mass; injective offsets give
equality. Injectivity is sufficient, not necessary.

For the centered db2 level-one taps

\[
k_0=\tfrac1{32}[-1,0,9,16,9,0,-1]
\]

and the separable convolution `P` on `(Z/NZ)^d`, the main specialization is

\[
N\ge7 \quad\Longrightarrow\quad
\|P\|_{\infty\to\infty}=(9/8)^d.
\]

A unit-norm signal attains this value. Consequently,
`||P f - P g|| <= (9/8)^d ||f-g||` for all real grid signals.
The zero-dimensional case is included and is the identity on a singleton.
The seven-tap kernel is also identified with one half of the autocorrelation
of the explicitly defined orthonormal db2 low-pass filter.

The same operator-norm theorem evaluates the first three undecimated cascade
levels. Each kernel is the integer five-tap recurrence that starts from `k_0`.
When the period is at least the support length, the centered offsets do not
collide, so the free l1 mass is the periodic operator norm:

- level 1, `N >= 19`: `(299/256)^d`
- level 2, `N >= 43`: `(9663/8192)^d`
- level 3, `N >= 91`: `(309991/262144)^d`

At dimension 2 the squares are `89401/65536`, `93373569/67108864` and
`96094420081/68719476736`. Those are the exact values behind the rounded
entries `1.364151`, `1.391375` and `1.398358` of manuscript equation (10).
There is no proved closed form for every level.

If a summary satisfies a supplied Lipschitz bound `L` in one seminorm and that
seminorm compares with a second seminorm by `sqrt(mu)`, the summary of the
smoothed signals obeys the factor `L * (9/8)^d * sqrt(mu)`. No smaller constant
bounds the smoothing operator itself. The difference of the squared summary
norms obeys the corresponding product bound. These steps are the manuscript's
Theorem A and Corollary 4.2 with the stability ingredients left as hypotheses.

## Why this is the proposed research-facing statement

The intended specialist audience is researchers in wavelet preprocessing,
finite-grid stability certification, and topological signal analysis. The
point of the artifact is to make the implementation-dependent constant
precise, dimension-dependent, attained, and sensitive to periodization.
A coefficient calculation alone cannot certify that constant for an operator.

The general convolution norm formula and tensor-product calculation are
standard facts, not claimed as new mathematics. The proposed contribution
is a formally auditable realization of the specific operator statement in
Proposition 3.4 of the [source manuscript](docs/manuscript-source.pdf), supported
by reusable finite-stencil periodization lemmas. Whether this specialization
meets Palomar's research-interest threshold remains an editorial question.
No claim of novelty or guaranteed registration is made.

## Exact selected surface

`Challenge.lean` is self-contained and imports only Mathlib. Its definitions
are fully specified. `Solution.lean` duplicates those definitions and supplies
all proof scripts; it does not import `Challenge`.

| Declaration | Mathematical content |
|---|---|
| `TWSPeriodic.convolution_opNorm` | Actual convolution operator norm on any finite abelian group |
| `TWSPeriodic.periodization_norm` | Universal bound after folding; equality for injective offsets |
| `TWSPeriodic.tensor_convolution_opNorm` | Exact separable norm in every dimension |
| `TWSPeriodic.db2_filter_identification` | Seven taps equal the specified db2 half-autocorrelation |
| `TWSPeriodic.db2_opNorm` | `(9/8)^d` for every `N >= 7` |
| `TWSPeriodic.db2_attains` | A unit signal attaining the db2 operator norm |
| `TWSPeriodic.db2_lipschitz` | Deterministic perturbation bound for that smoothing operator |
| `TWSPeriodic.summary_bound_propagation` | Conditional Theorem A for an arbitrary continuous linear map |
| `TWSPeriodic.db2_summary_stability` | The same propagation with the exact db2 factor |
| `TWSPeriodic.db2_opNorm_least` | `(9/8)^d` is the least smoothing constant |
| `TWSPeriodic.db2_squared_summary_stability` | Conditional squared-summary product bound |
| `TWSPeriodic.cascade_level1_opNorm` | `(299/256)^d` for every `N >= 19` |
| `TWSPeriodic.cascade_level2_opNorm` | `(9663/8192)^d` for every `N >= 43` |
| `TWSPeriodic.cascade_level3_opNorm` | `(309991/262144)^d` for every `N >= 91` |

These are related parts of one result, not fourteen independent research contributions.
The small-period kernel is defined by genuine folding, even though the db2
specialization is only asserted for `N >= 7`.

## Scope limits

- No persistence-diagram construction, bottleneck theorem, or proof that a
  landscape is non-expansive is claimed. The composed bounds take those
  ingredients as hypotheses.
- Attainment concerns the smoothing operator alone. A downstream nonlinear
  summary need not attain the composed bound.
- The theorem concerns the explicitly defined mathematical convolution.
  Cascade levels 1, 2 and 3 are certified for periods at least 19, 43 and 91.
  It does not certify Python/PyWavelets code, floating-point arithmetic, other
  padding modes, a closed form for every wavelet level, or arbitrary wavelet
  filters.
- `N >= 7` is a transparent sufficient no-collision condition, not a claim
  that seven is the smallest period giving equality.
- The supplied manuscript is an unchanged source snapshot. Its old Lean
  section does not describe this new candidate; revise it only after audit.

## Provenance and repository role

The earlier `tws-palomar` was a Comparator wrapper around code developed in
`jelincovil/tws-repro`. This candidate changes that architecture: the new
operator, periodization, tensorization, and extremizer proofs are all supplied
here in `Solution.lean`. The old skeleton is not shipped or imported.

Thus the intended replacement is a **substantive development in this repository**,
not a wrapper that re-labels imported theorems. Under the current schema it
omits `repository`. This is justified only if the full new development is
actually committed here. The predecessor, its exact revision, its authors,
and the adapted filter algebra remain explicitly attributed in
[PROVENANCE.md](docs/PROVENANCE.md), `formalization.yaml`, and `NOTICE`.

If you instead develop these new proofs in `tws-repro` and make this repository
only a wrapper, restore `repository.substantive_formalization` and pin the
**new** underlying revision. Do not reuse an old revision that lacks the proofs.

## What this correction changes in the proofs

The selected statements are unchanged. Two scripts in `Solution.lean` were
adjusted to the pinned Mathlib API:

- `ContinuousLinearMap.unit_le_opNorm` takes the witness vector explicitly.
- `sub_right_cancel` is not in this Mathlib revision. Injectivity of the seven
  centered offsets cancels the shared shift with `sub_add_cancel`.

## Reproduce and audit

Prerequisites: a normal Linux environment with elan/Lean, Python 3, Git, and
bubblewrap for the Comparator sandbox. The toolchain is Lean `v4.35.0-rc2`;
Mathlib is pinned to `065356127b1dc0016f66b7283ce0ce2c4055aa55`.
The checked-in manifest is adapted from the official template at the exact
revision listed in `docs/PROVENANCE.md`.

```bash
python3 -m pip install -r requirements-audit.txt
python3 scripts/preflight.py
python3 scripts/check_exact_cases.py
lake exe cache get
lake build
lake env lean AxiomAudit.lean
bash scripts/verify-comparator.sh
```

A successful `lake build` alone is not a Comparator result. The last command
uses the toolchain's Comparator and bundled independent kernels through the
current official template script. It requires a working sandbox; do not
switch off the sandbox to turn an environment failure into a pass.

Do not run `lake update` as part of routine replay: it changes the dependency
lock. If deliberately changing dependencies, update and audit `lean-toolchain`,
`lakefile.toml`, and `lake-manifest.json` together.

The GitHub workflow runs the same checks on a fresh runner and preserves the
logs. It does not submit or register anything.

## Submit after audit

1. Replace the old tree using `AUDITORIA_ES.md`; remove the obsolete files.
2. Resolve compilation/Comparator failures, review the mathematical statements,
   and update `docs/VERIFICATION.md` with actual evidence.
3. Check attribution, author consent as applicable, and the truthful metadata.
4. Publish this directory as the root of a public GitHub repository. Palomar
   reads `comparator.json` from that root. Keep the predecessor commit
   `f15103f97a300cfa243991956fa2d89e9c9ab6a7` reachable in
   `jelincovil/tws-palomar`; this snapshot cites it. Obtain the full SHA with
   `git rev-parse HEAD`.
5. Submit that repository, that exact SHA, and `comparator.json` at
   <https://submit.palomar-registry.org/>. Leave the project path blank.
   For a retry of an unregistered, unsuccessful submission, leave the existing
   Palomar ID empty.
6. Read the new automated review before deciding to register.

Registration and any later public publication are actions for the maintainer.
This package neither performs them nor asserts that the review will pass.

## Licence

New project material is Apache-2.0. Adapted predecessor filter algebra retains
its MIT attribution; see `third_party/tws-repro-MIT.txt` and `NOTICE`.
The unchanged source manuscript retains the CC-BY-4.0 designation stated by
the predecessor repository; it is not relicensed by the root licence.
