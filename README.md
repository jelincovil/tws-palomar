# Exact db2 cascade norms and an optimal uniform constant

**Candidate for audit, not a Palomar registration.** The main statement is an
exact formula for every scale of the undecimated db2 cascade, and the least
constant that bounds the associated periodic operators uniformly. The argument
is written out in [the cascade note](docs/CASCADE_THEOREM.md). Priority
relative to the literature is unresolved;
see [related work](docs/RELATED_WORK.md). The historical manuscript is
[docs/manuscript-source.pdf](docs/manuscript-source.pdf).

The proofs in `Solution.lean` use Lean `v4.35.0-rc2` and the pinned Mathlib.
What each check covers, and which commit it covers, is in
[verification status](docs/VERIFICATION.md). A sandboxed run on an earlier
commit is not a check of a later tree, and a successful run is not a
registration. See the [Spanish audit guide](AUDITORIA_ES.md).

## The problem

An undecimated db2 smoother on a periodic grid is convolution by a kernel
built from the orthonormal four-tap low-pass filter. One stage is the
half-autocorrelation

```
k_0 = [-1, 0, 9, 16, 9, 0, -1] / 32.
```

Further stages convolve with dyadically upsampled copies of the same mask.
The indexed level `j = 0` is already this first stage. On a grid of side `N`
and dimension `d`, the quantity of interest is the supremum operator norm of
that convolution. When the period is shorter than the support, taps collide
and the norm can drop. A bound obtained by multiplying one stage by the next
grows like `(9/8)^{(j+1)d}` and becomes useless as a uniform estimate.

## The theorem

Write `L = 1651/1395` and

```
c_j = L - (4/63) 4^{-j} + (1/180) 16^{-j} - (1/1736) 32^{-j}.
```

The free ℓ¹ mass of level `j` is `c_j`. It does not depend on `N`. If
`N` is at least the support `S_j = 6 * 2^{j+1} - 5`, folding does not cancel
and the periodic operator norm is `c_j^d` in every dimension, including
`d = 0`. For every positive period, aliasing included, the norm is at most
`L^d`. That power is the least constant with this role: the period used in
the comparison may grow with the level, and one fixed `N` is not claimed to
attain it. At `d = 0` the least-constant conclusion is `1 ≤ B`. It does not
force `B = 1`, although each individual zero-dimensional norm equals `1`.
The free mass increases strictly to `L`, and the gap is at most
`(4/63) 4^{-j}`. The condition `N ≥ S_j` is sufficient, not necessary.

The part of the argument that is special to this kernel is the control of
signs. Symmetry, support, and the signed sum `1` do not determine the
absolute mass. The proof keeps a positive center whose consecutive
differences have ratios in `[1/3, 3]`, and a negative first side whose
absolute values have ratios in `[1/2, 5/2]`, including the taps created at
the block boundaries. Those signs turn the block sums into linear
recurrences, and the recurrences have the closed form above. Convolution,
folding, and tensorization then transfer the mass to the operator norm.
Those three steps are standard.

Levels `1`, `2`, and `3` remain available as direct evaluations:
`(299/256)^d` for `N ≥ 19`, `(9663/8192)^d` for `N ≥ 43`, and
`(309991/262144)^d` for `N ≥ 91`. They agree with `c_1`, `c_2`, and `c_3`.
At `j = 0` the formula is `(9/8)^d` for `N ≥ 7`.

If a summary satisfies a supplied Lipschitz bound `L` in one seminorm and
that seminorm compares with a second seminorm by `sqrt(mu)`, the summary of
the level-one smoothed signals obeys the factor `L * (9/8)^d * sqrt(mu)`.
The difference of the squared summary norms obeys the corresponding product
bound. Both statements take the summary hypotheses as assumptions. They do
not prove bottleneck stability or landscape non-expansiveness.

## What is standard, what is specific, what follows

The general convolution norm, the folding inequality, and the tensor power
are standard finite-dimensional facts. They are proved in full so that the
cascade theorem does not depend on an external formalization, and they are
not offered as the contribution.

The specific work is the sign analysis that produces `c_j` for every level
and the least uniform constant `L^d`. The finite levels, the gap, the
increase, the limit, and the zero-dimensional identity are consequences of
that analysis. Twenty-two declarations are selected because that is the
Comparator interface. They are parts of one development.

Whether this is enough for a Palomar registration is an editorial question.
The [related-work note](docs/RELATED_WORK.md) records that the closest
papers were not available in full, so novelty is not claimed. The elementary
improvement on `(9/8)^{(j+1)d}` does not answer that question.

## Supporting identities

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

Applied to `k_0` on `(Z/NZ)^d`, the same identity gives
`||P|| = (9/8)^d` whenever `N >= 7`. A unit-norm signal attains this value.
The zero-dimensional case is the identity on a singleton. These are the
`j = 0` case of the theorem above, not a separate contribution.

## How the pieces fit the manuscript

Proposition 3.4 of the [source manuscript](docs/manuscript-source.pdf) is the
level-one case `j = 0`: the norm `(9/8)^d` for `N ≥ 7`, attained by a sign
signal. Equation (10) of that manuscript prints rounded two-dimensional
values at the next three levels. Those values are the squares of `c_1`,
`c_2`, and `c_3`. The closed form for every level, the uniform constant, and
the rate are later than the manuscript. They are explained in
[docs/CASCADE_THEOREM.md](docs/CASCADE_THEOREM.md).

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
| `TWSPeriodic.cascade_l1_formula` | Periodized mass equals `c_j` when `N >= S_j`. The free mass equals `c_j` with no period hypothesis |
| `TWSPeriodic.cascade_opNorm_formula` | Operator norm `c_j^d` for every level, when `N >= S_j` |
| `TWSPeriodic.cascade_opNorm_uniform` | At most `(1651/1395)^d` for every `N >= 1` |
| `TWSPeriodic.cascade_l1_gap` | `0 < 1651/1395 - c_j <= (4/63) 4^{-j}` |
| `TWSPeriodic.cascade_l1_succ_lt` | The free mass is strictly increasing |
| `TWSPeriodic.cascade_l1_tendsto` | The free mass converges to `1651/1395` |
| `TWSPeriodic.cascade_uniform_constant_least` | `(1651/1395)^d` is the least common bound |
| `TWSPeriodic.cascade_opNorm_d_zero` | Dimension zero is exactly 1 |

These are related parts of one result, not twenty-two independent research contributions.
The small-period kernel is defined by genuine folding, even though the db2
specialization is only asserted for `N >= 7`.

## Scope limits

- No persistence-diagram construction, bottleneck theorem, or proof that a
  landscape is non-expansive is claimed. The composed bounds take those
  ingredients as hypotheses.
- Attainment concerns the smoothing operator alone. A downstream nonlinear
  summary need not attain the composed bound.
- The theorem concerns the explicitly defined mathematical convolution.
  Cascade levels 1, 2 and 3 remain certified, and the closed form covers every
  level. `N >= S_j` is a sufficient no-collision condition. The uniform bound
  allows aliasing. It does not certify Python/PyWavelets code, floating-point
  arithmetic, other padding modes, or arbitrary wavelet filters.
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

## Earlier API correction

On 2026-10-17, before the cascade formula was added, two scripts in
`Solution.lean` were adjusted to the pinned Mathlib API. The statements
selected at that moment were not changed by those two edits.

- `ContinuousLinearMap.unit_le_opNorm` takes the witness vector explicitly.
- `sub_right_cancel` is not in this Mathlib revision. Injectivity of the seven
  centered offsets cancels the shared shift with `sub_add_cancel`.

The cascade statements were added after that correction. The current selected
list is the table above.

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

The submission procedure below follows
<https://palomar-registry.org/how-to-submit> as read on 2026-10-18. This
package does not open the form and does not submit.

1. Audit the mathematical note, the related-work conclusion, and
   `docs/VERIFICATION.md`. Push only the snapshot you want reviewed.
2. Palomar fetches one immutable commit. In this repository root run
   `git rev-parse HEAD` and copy the full 40-character SHA. Uncommitted
   files and a branch name are not the submission.
3. Open <https://submit.palomar-registry.org/> in a browser. Enter
   `https://github.com/jelincovil/tws-palomar` and that SHA. The project
   lives at the repository root, so leave the project path, the Comparator
   path, and the metadata path blank. `comparator.json` is already at the
   root.
4. The previous mechanical review did not offer registration, so there is
   no Palomar ID to attach. Leave that field blank. Enter an existing ID
   only when registering a new version of a result that already has one.
5. The form's write-access check is for the maintainer. The current
   instructions say that machines should not drive the form.
6. Read the new automated review before deciding to register. Mechanical
   success is not registration, and registration is a separate action.

Keep the predecessor commit
`f15103f97a300cfa243991956fa2d89e9c9ab6a7` reachable in
`jelincovil/tws-palomar`; this snapshot cites it. Registration and any
later public publication remain actions for the maintainer. This package
does not assert that the review will pass. The Challenge module is within
the hard limit of 1000 lines and 100 KiB. The submission guide says that
about 300 lines is the surface Palomar would rather review. The current
Challenge is 329 lines and 14384 bytes, so it is inside the hard limit and
longer than that preference.

## Licence

New project material is Apache-2.0. Adapted predecessor filter algebra retains
its MIT attribution; see `third_party/tws-repro-MIT.txt` and `NOTICE`.
The unchanged source manuscript retains the CC-BY-4.0 designation stated by
the predecessor repository; it is not relicensed by the root licence.
