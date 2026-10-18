# Endpoint-replicated (nonperiodic) db2 cascade: specification and proofs

Status: **complete for all `n ≥ 1` and all `j ≥ 0`.** Every statement below is a
Lean theorem that compiles with no `sorry`. The only axioms used are `propext`,
`Classical.choice` and `Quot.sound`; the phase-closing audit `extension/AxiomCheck.lean`
covers all 90 public declarations of the five modules plus the two baseline theorems,
and is reproducible with `lake env lean AxiomCheck.lean` (see `verification/axioms-1.log`).
Lean namespace: `ThresholdCert.Nonperiodic`.

## 1. Data and notation

* `n ≥ 1`, written as the instance `[NeZero n]`. `j ≥ 0` is any natural number.
* Signals are `Fin n → ℝ` with Mathlib's finite Pi supremum norm.
* The following are the baseline definitions from `Solution.lean`, used without change:
  * `r = TWSPeriodic.cascadeRadius j = 3(2^(j+1) − 1)`;
  * `s = TWSPeriodic.cascadeSupport j = 2r + 1`;
  * the taps `TWSPeriodic.cascadeTap j : Fin s → ℝ`.
* `M = padLen j n = n + 2r`.

## 2. Definitions

| Lean name | Meaning |
|---|---|
| `clamp n t` | `⟨min t.toNat (n−1), _⟩ : Fin n`. This gives `t<0 ↦ 0`, `0≤t<n ↦ t` and `t≥n ↦ n−1`. The case lemmas are `clamp_of_neg`, `clamp_of_mem` and `clamp_of_ge`. |
| `directOp j n` | The continuous linear map `(A x) i = ∑ a : Fin s, cascadeTap j a * x (clamp n (i − (a − r)))`. All arithmetic is in `ℤ`. |
| `padLen j n` | `n + 2r`, with the instance `NeZero (padLen j n)` (`padLen_neZero`). |
| `padOp j n` | `E`, a continuous linear map into `(Fin 1 → ZMod M) → ℝ`, given by `(E x) u = x (clamp n ((u 0).val − r))`. |
| `restrictOp j n` | `R`, the continuous linear map `(R z) i = z (fun _ => ((r + i : ℕ) : ZMod M))`. |

`directOp` is defined by the stencil formula alone. It is not defined through `E`, `R` or the periodic operator.
It applies the full level-`j` kernel once, to the endpoint extension of the original signal.
It does not re-pad between cascade stages.

Padding layout: `E x` at periodic index `u` (with `0 ≤ u.val < M`) is
* `x 0` for `u < r`;
* `x (u − r)` for `r ≤ u < r + n`;
* `x (n−1)` for `u ≥ r + n`.

So the padded array has `r` copies of the first sample, then the `n` original samples, then `r` copies of the last sample.

## 3. Theorems

### Extension and restriction
* `cascadeSupport_le_padLen : cascadeSupport j ≤ padLen j n`. Proof: `2r+1 ≤ n+2r`, using `n ≥ 1`.
* `restrict_pad : restrictOp j n (padOp j n x) = x`.
* `padOp_norm_le : ‖padOp j n‖ ≤ 1` and `restrictOp_norm_le : ‖restrictOp j n‖ ≤ 1`.
  Each output coordinate is one input coordinate, so `|out_i| ≤ ‖input‖`.

### Identification (central obligation)
* `convolution_foldKernel`: convolution with a folded kernel equals the sum over the unfolded taps:
  `convolutionOperator (foldKernel a q) f x = ∑ i, a i * f (x − q i)`.
  No injectivity of `q` is needed, so this holds for every period.
* `cascadeOperator_one_apply`: this is the dimension-one tensor simplification together with the fold:
  `cascadeOperator j N 1 z u = ∑ a, cascadeTap j a * z (u − fun _ => cascadeOffset j N a)`.
* `pad_at_tap`: the index calculation (see §4).
* **`directOp_eq_restrict_cascade_pad`**: for every `n ≥ 1`, every `j` and every `x`,
  `directOp j n x = restrictOp j n (cascadeOperator j (padLen j n) 1 (padOp j n x))`.
* `directOp_eq_comp`: the same identity as an equality of continuous linear maps, `A = R ∘L C ∘L E`.

### Norm bounds
These are upper bounds only. Neither is claimed to be the exact nonperiodic norm, or optimal.
* `directOp_norm_le_periodic : ‖A‖ ≤ ‖cascadeOperator j M 1‖`.
* `directOp_norm_le_C : ‖A‖ ≤ cascadeC j`. This uses the baseline `cascade_opNorm_formula` at period `M ≥ s`, through the existing bridge `ThresholdCert.Db2.cascade1_opNorm_eq_C`.
* `directOp_norm_le_L : ‖A‖ ≤ cascadeL`. This uses the baseline `cascade_opNorm_uniform` through `ThresholdCert.Db2.cascade1_opNorm_le_L`.

### Perturbation bounds
Each assumes only `‖y − x‖ ≤ ε`. None assumes a norm bound on `A`.
* `directOp_perturbation_C : ‖A y − A x‖ ≤ cascadeC j * ε`.
* `directOp_perturbation_L : ‖A y − A x‖ ≤ cascadeL * ε`.
* Coordinatewise versions: `directOp_coord_perturbation_C` and `directOp_coord_perturbation_L`.

### Threshold certificate
Write `m = cascadeC j * ε`. Each of the following assumes only `‖y − x‖ ≤ ε`.
* `above_sound_C`: `τ + m < (A y) i → τ < (A x) i`.
* `notAbove_sound_C`: `(A y) i ≤ τ − m → (A x) i ≤ τ`.
* `symmDiff_subset_band_C`: `{i | τ < (A y) i} ∆ {i | τ < (A x) i} ⊆ {i | τ − m < (A y) i ∧ (A y) i ≤ τ + m}`.
* `above_sound_L`, `notAbove_sound_L` and `symmDiff_subset_band_L` are the same statements with `m = cascadeL * ε`.

### Conservation of constants (added in the local close-out)

Module `ThresholdExtension.ConstantPreservation`. These statements concern the operator `A`
alone; no noise bound is involved.

* `cascadeTap_sum_one (j)` : `∑ a : Fin (cascadeSupport j), cascadeTap j a = 1`.
  This is the **signed** mass of the kernel, not the `ℓ¹` mass `cascadeC j`.
* `directOp_const (j n) [NeZero n] (c)` : `A (fun _ => c) = fun _ => c`, for every `j` and
  every `n ≥ 1`; there is no hypothesis `n ≥ cascadeSupport j`.
* `directOp_one_eq_id (j)` : `A_{j,1} = ContinuousLinearMap.id ℝ (Fin 1 → ℝ)`.
* `cascadeInt_sum (j)` : `∑_{n ∈ [-r_j, r_j]} cascadeInt j n = cascadeScale j`, the integer
  mass identity from which the tap sum is obtained by dividing by the positive scale.

Proof route. `cascadeInt j` is supported in `[-r_j, r_j]` (`cascadeInt_vanish`) and obeys the
five-tap recurrence with weights `16, 9, 9, -1, -1`, whose sum is `32`. Summing the
recurrence over the symmetric interval, reindexing each of the five shifted copies (a finite
translation, legitimate because the support stays inside the interval), and using the base
case `16 + 9 + 9 - 1 - 1 = 32 = cascadeScale 0` gives `mass(j+1) = 32 · mass(j)`. Since
`cascadeScale (j+1) = 32 · cascadeScale j`, induction yields `cascadeInt_sum`. Reindexing
`Fin (2r+1) → [-r, r]` by `a ↦ a.val - r` converts the integer mass into the tap sum.

All of these concern the **smoothed reference `A x`**. Nothing is claimed about `x` itself.
Such a claim would need an extra bias bound `‖A x − x‖ ≤ δ`; the existing abstract lemmas `raw_above_sound` and `raw_notAbove_sound` show how the margin would then become `m + δ`.

## 4. Informal proof of the identification

Fix `i < n` and a tap index `a ∈ [0, 2r]`, and put `t = a − r ∈ [−r, r]`.

1. **Unfold the baseline operator.** At `d = 1` the tensor kernel is `k(y 0)`. Here `k = foldKernel tap offset` is a sum of indicator terms.
   Swap the two finite sums. For `Fin 1`, the condition `offset a = y 0` is equivalent to `(fun _ => offset a) = y`.
   So each inner sum collapses (`Finset.sum_ite_eq`), which leaves
   `(C z)(u) = ∑_a tap a · z(u − offset a)`.
   This holds for every period `N`. Collisions between taps are harmless, because the fold only adds the colliding taps together.
2. **Index calculation.** The restriction evaluates at `u = r + i`. Then
   `u − offset a = (r+i) − (a − r) = 2r + i − a` in `ZMod M`.
   As a natural number, `0 ≤ 2r + i − a ≤ 2r + n − 1 = M − 1` (this uses `a ≤ 2r` and `i ≤ n−1`), so `ZMod.val` returns exactly `2r + i − a`.
   Equivalently, `0 ≤ r + i − t ≤ M − 1`. **The retained outputs never read across the periodic seam.**
3. **Padding.** `E` reads `clamp n ((2r + i − a) − r) = clamp n (i − (a − r))`, which is exactly the sample used by the direct stencil.
4. Summing over `a` gives the identity.

There is no assumption `n ≥ s`. When `n < s`, many taps land in the replicated region, and the clamp handles them.
`cascadeSupport j ≤ M` always holds, so the exact periodic norm `c_j` is available at period `M`.

Norm bounds: `‖A‖ = ‖R C E‖ ≤ ‖R‖ ‖C‖ ‖E‖ ≤ ‖C‖`. Then use `‖C‖ = c_j` (because `s ≤ M`) and `‖C‖ ≤ L`.
Perturbation: `‖A y − A x‖ = ‖A (y − x)‖ ≤ ‖A‖ ε`.
Certificates: apply the abstract `ThresholdCert` theorems with `T = A`, together with the bound just derived.

## 5. Edge cases

* **`n = 1`** (`directOp_n_one`): every clamped index is `0`, so `A_{j,1} x = (∑_a tap a) · x`.
  By `cascadeTap_sum_one` the tap sum is `1` for every `j`, so `directOp_one_eq_id` proves
  `A_{j,1} = id` at every level. The earlier level-zero instance `directOp_zero_one` is kept
  as a cross-check.
* **`j = 0`**: `cascadeTap_zero_values` gives the taps `[-1,0,9,16,9,0,-1]/32` (`r = 3`, `s = 7`).
* **`n < s`**: all exact checks below have `n ∈ {2, 3}` and `s ∈ {7, 19}`.
* **First and last coordinates**: the checks below evaluate every output coordinate, including `i = 0` and `i = n−1`.
  The general proof makes no special case of them; the clamp covers both ends.
* No hypothesis `n ≥ cascadeSupport j` appears anywhere.

Exact checks. In each one, the periodic side is computed from the baseline operator via
`cascadeOperator_one_apply` and finite `ZMod` arithmetic. It does **not** use the identification theorem.

| check | data | result (direct = padded-periodic) |
|---|---|---|
| `check_direct_j0_n2` / `check_periodic_j0_n2` | `j=0, n=2, x=(1,0)`, `M=8` | `(3/4, 1/4)` |
| `check_direct_j0_n3` / `check_periodic_j0_n3` | `j=0, n=3, x=(0,1,0)`, `M=9` | `(9/32, 1/2, 9/32)` |
| `check_direct_j1_n2` / `check_periodic_j1_n2` | `j=1, n=2, x=(1,0)`, `M=20` | `(5/8, 3/8)` |

**Tempting false claim, refuted** (`unpadded_periodic_differs`): one might apply the periodic cascade directly at period `N = n` instead of padding.
This does not give the endpoint-replicated result. For `j=0, n=2, x=(1,0)`, the periodic operator at period 2 gives `1/2` at coordinate 0, whereas endpoint replication gives `3/4`.

No target statement in the task was found to be false. The operator was not changed.

## 6. Not claimed

* That `cascadeC j` or `cascadeL` is the exact norm of `A_{j,n}`, or optimal for it.
  For small `n`, coincident clamped taps can cancel, so the true norm may be smaller.
* Anything about `x` itself (denoising accuracy).
* Other padding modes, repeated intermediate re-padding, higher dimensions, or floating point.
