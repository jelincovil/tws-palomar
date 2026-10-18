module

public import Solution

/-!
# Endpoint-replicated (nonperiodic) db2 cascade on finite signals

For `n ≥ 1` (expressed as `[NeZero n]`) and a level `j`, with
`r = TWSPeriodic.cascadeRadius j`, `s = TWSPeriodic.cascadeSupport j = 2 r + 1` and
`M = n + 2 r`, this module

* defines the clamp `ℤ → Fin n` (endpoint replication of indices);
* defines the direct stencil operator `directOp j n` on `Fin n → ℝ`, independently of any
  periodic object, by
  `(A x) i = ∑ a : Fin s, cascadeTap j a * x (clamp n (i - (a - r)))` (all in `ℤ`);
* defines the endpoint extension `padOp j n` into the baseline periodic signal space
  `(Fin 1 → ZMod M) → ℝ` and the restriction `restrictOp j n` back to `Fin n → ℝ`;
* proves `R (E x) = x`, `‖E‖ ≤ 1`, `‖R‖ ≤ 1`, `cascadeSupport j ≤ M`;
* proves the identification
  `directOp j n x = restrictOp j n (TWSPeriodic.cascadeOperator j M 1 (padOp j n x))`
  for every `x`, against the actual baseline operator.

There is no assumption `n ≥ cascadeSupport j`.
-/

@[expose] public section

open TWSPeriodic

namespace ThresholdCert.Nonperiodic

/-! ## Clamp -/

/-- Endpoint-replication clamp `ℤ → Fin n`: negative integers go to the first index,
`0 ≤ t < n` goes to `t`, and `t ≥ n` goes to the last index. -/
def clamp (n : ℕ) [NeZero n] (t : ℤ) : Fin n :=
  ⟨min t.toNat (n - 1), by have := NeZero.pos n; omega⟩

theorem clamp_val (n : ℕ) [NeZero n] (t : ℤ) : (clamp n t).val = min t.toNat (n - 1) := rfl

theorem clamp_of_neg (n : ℕ) [NeZero n] {t : ℤ} (ht : t < 0) :
    clamp n t = ⟨0, NeZero.pos n⟩ := by
  ext; simp only [clamp_val]; omega

theorem clamp_of_mem (n : ℕ) [NeZero n] {t : ℤ} (h0 : 0 ≤ t) (h1 : t < n) :
    ((clamp n t).val : ℤ) = t := by
  simp only [clamp_val]; omega

theorem clamp_of_ge (n : ℕ) [NeZero n] {t : ℤ} (ht : (n : ℤ) ≤ t) :
    clamp n t = ⟨n - 1, by have := NeZero.pos n; omega⟩ := by
  ext; simp only [clamp_val]; omega

theorem clamp_natCast (n : ℕ) [NeZero n] (i : Fin n) : clamp n (i.val : ℤ) = i := by
  ext; simp only [clamp_val]; omega

/-! ## Padded length -/

/-- Padded period `M = n + 2 r`, `r = cascadeRadius j`. -/
def padLen (j n : ℕ) : ℕ := n + 2 * cascadeRadius j

theorem padLen_pos (j n : ℕ) [NeZero n] : 0 < padLen j n := by
  unfold padLen; have := NeZero.pos n; omega

instance padLen_neZero (j n : ℕ) [NeZero n] : NeZero (padLen j n) :=
  ⟨(padLen_pos j n).ne'⟩

/-- The full cascade support fits in one period of the padded signal (uses `n ≥ 1`). -/
theorem cascadeSupport_le_padLen (j n : ℕ) [NeZero n] : cascadeSupport j ≤ padLen j n := by
  unfold padLen cascadeSupport; have := NeZero.pos n; omega

/-! ## The direct nonperiodic operator -/

/-- Direct endpoint-replicated stencil of the full level-`j` cascade kernel. -/
noncomputable def directOp (j n : ℕ) [NeZero n] : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) where
  toFun x i := ∑ a : Fin (cascadeSupport j),
    cascadeTap j a * x (clamp n ((i.val : ℤ) - ((a.val : ℤ) - (cascadeRadius j : ℤ))))
  map_add' x y := by
    ext i
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    ext i
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  cont := by fun_prop

theorem directOp_apply (j n : ℕ) [NeZero n] (x : Fin n → ℝ) (i : Fin n) :
    directOp j n x i = ∑ a : Fin (cascadeSupport j),
      cascadeTap j a * x (clamp n ((i.val : ℤ) - ((a.val : ℤ) - (cascadeRadius j : ℤ)))) :=
  rfl

/-! ## Extension and restriction -/

/-- Endpoint extension into the baseline periodic signal space of period `M`:
`(E x) u = x (clamp n ((u 0).val - r))`. -/
noncomputable def padOp (j n : ℕ) [NeZero n] :
    (Fin n → ℝ) →L[ℝ] ((Fin 1 → ZMod (padLen j n)) → ℝ) where
  toFun x u := x (clamp n (((u 0).val : ℤ) - (cascadeRadius j : ℤ)))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := by fun_prop

theorem padOp_apply (j n : ℕ) [NeZero n] (x : Fin n → ℝ) (u : Fin 1 → ZMod (padLen j n)) :
    padOp j n x u = x (clamp n (((u 0).val : ℤ) - (cascadeRadius j : ℤ))) := rfl

/-- Restriction to the `n` central samples: `(R z) i = z (fun _ => r + i)`. -/
noncomputable def restrictOp (j n : ℕ) [NeZero n] :
    ((Fin 1 → ZMod (padLen j n)) → ℝ) →L[ℝ] (Fin n → ℝ) where
  toFun z i := z (fun _ : Fin 1 => ((cascadeRadius j + i.val : ℕ) : ZMod (padLen j n)))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := by fun_prop

theorem restrictOp_apply (j n : ℕ) [NeZero n] (z : (Fin 1 → ZMod (padLen j n)) → ℝ)
    (i : Fin n) :
    restrictOp j n z i =
      z (fun _ : Fin 1 => ((cascadeRadius j + i.val : ℕ) : ZMod (padLen j n))) := rfl

/-- Value of a natural number below the period. -/
theorem val_natCast_padLen {j n : ℕ} [NeZero n] {k : ℕ} (hk : k < padLen j n) :
    ((k : ZMod (padLen j n))).val = k := by
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt hk]

/-- `R ∘ E = id`. -/
theorem restrict_pad (j n : ℕ) [NeZero n] (x : Fin n → ℝ) :
    restrictOp j n (padOp j n x) = x := by
  ext i
  rw [restrictOp_apply, padOp_apply]
  have hk : cascadeRadius j + i.val < padLen j n := by unfold padLen; omega
  rw [val_natCast_padLen hk]
  congr 1
  rw [show ((cascadeRadius j + i.val : ℕ) : ℤ) - (cascadeRadius j : ℤ) = (i.val : ℤ) by
    push_cast; ring]
  exact clamp_natCast n i

theorem padOp_norm_le (j n : ℕ) [NeZero n] : ‖padOp j n‖ ≤ 1 := by
  refine (padOp j n).opNorm_le_bound zero_le_one fun x => ?_
  rw [one_mul]
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg x)).2 fun u => ?_
  rw [padOp_apply]
  exact norm_le_pi_norm x _

theorem restrictOp_norm_le (j n : ℕ) [NeZero n] : ‖restrictOp j n‖ ≤ 1 := by
  refine (restrictOp j n).opNorm_le_bound zero_le_one fun z => ?_
  rw [one_mul]
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg z)).2 fun i => ?_
  rw [restrictOp_apply]
  exact norm_le_pi_norm z _

/-! ## The baseline periodic operator at dimension one -/

/-- Convolution with a folded kernel is the sum over the unfolded taps
(no injectivity of the offsets is needed). -/
theorem convolution_foldKernel {I G : Type} [Fintype I] [Fintype G] [AddCommGroup G]
    [DecidableEq G] (a : I → ℝ) (q : I → G) (f : G → ℝ) (x : G) :
    convolutionOperator (foldKernel a q) f x = ∑ i : I, a i * f (x - q i) := by
  rw [convolutionOperator_apply]
  simp only [foldKernel, Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  simp

/-- Dimension-one tensor simplification together with the folded kernel: the baseline
operator `cascadeOperator j N 1` acts as the unfolded centered stencil. -/
theorem cascadeOperator_one_apply (j N : ℕ) [NeZero N] (z : (Fin 1 → ZMod N) → ℝ)
    (u : Fin 1 → ZMod N) :
    cascadeOperator j N 1 z u =
      ∑ a : Fin (cascadeSupport j),
        cascadeTap j a * z (u - fun _ : Fin 1 => cascadeOffset j N a) := by
  classical
  unfold cascadeOperator
  rw [convolutionOperator_apply]
  simp only [tensorKernel, Fin.prod_univ_one, cascadeKernel, foldKernel, Finset.sum_mul,
    ite_mul, zero_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  have hiff : ∀ y : Fin 1 → ZMod N,
      (cascadeOffset j N a = y 0) ↔ ((fun _ : Fin 1 => cascadeOffset j N a) = y) := by
    intro y
    constructor
    · intro h; funext k; rw [Fin.fin_one_eq_zero k]; exact h
    · intro h; rw [← h]
  simp only [hiff]
  simp

/-! ## Identification of the direct stencil with the padded periodic realization -/

/-- Index calculation: for a retained output `i < n` and a tap `a ≤ 2 r`, the periodic
index read by the baseline operator is the integer `2 r + i - a ∈ [0, M - 1]`, so the
artificial periodic seam is never touched, and the padded sample is the clamped original
sample at `i - (a - r)`. -/
theorem pad_at_tap (j n : ℕ) [NeZero n] (x : Fin n → ℝ) (i : Fin n)
    (a : Fin (cascadeSupport j)) :
    padOp j n x ((fun _ : Fin 1 => ((cascadeRadius j + i.val : ℕ) : ZMod (padLen j n))) -
        fun _ : Fin 1 => cascadeOffset j (padLen j n) a) =
      x (clamp n ((i.val : ℤ) - ((a.val : ℤ) - (cascadeRadius j : ℤ)))) := by
  rw [padOp_apply]
  have ha : a.val ≤ 2 * cascadeRadius j := by
    have := a.isLt; unfold cascadeSupport at this; omega
  have hk : 2 * cascadeRadius j + i.val - a.val < padLen j n := by
    unfold padLen; omega
  have hidx : ((cascadeRadius j + i.val : ℕ) : ZMod (padLen j n)) -
      cascadeOffset j (padLen j n) a =
      ((2 * cascadeRadius j + i.val - a.val : ℕ) : ZMod (padLen j n)) := by
    unfold cascadeOffset
    rw [Nat.cast_sub (by omega)]
    push_cast; ring
  simp only [Pi.sub_apply]
  rw [hidx, val_natCast_padLen hk]
  congr 2
  rw [Nat.cast_sub (by omega)]
  push_cast; ring

/-- **Identification.** For every `n ≥ 1`, every level `j` and every signal `x`, the
direct endpoint-replicated stencil equals extension, then the actual baseline periodic
cascade `cascadeOperator j M 1`, then restriction. -/
theorem directOp_eq_restrict_cascade_pad (j n : ℕ) [NeZero n] (x : Fin n → ℝ) :
    directOp j n x =
      restrictOp j n (cascadeOperator j (padLen j n) 1 (padOp j n x)) := by
  ext i
  rw [directOp_apply, restrictOp_apply, cascadeOperator_one_apply]
  exact Finset.sum_congr rfl fun a _ => by rw [pad_at_tap]

/-- The identification as an equality of continuous linear maps. -/
theorem directOp_eq_comp (j n : ℕ) [NeZero n] :
    directOp j n =
      (restrictOp j n).comp ((cascadeOperator j (padLen j n) 1).comp (padOp j n)) := by
  ext1 x
  exact directOp_eq_restrict_cascade_pad j n x

end ThresholdCert.Nonperiodic
