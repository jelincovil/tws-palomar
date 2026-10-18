import ThresholdExtension.ThresholdCertificate
import ThresholdExtension.Db2ThresholdCertificate
import ThresholdExtension.EndpointReplication
import ThresholdExtension.NonperiodicDb2Certificate
import ThresholdExtension.ConstantPreservation

/-!
# Axiom audit for the complete threshold-certificate extension

This is the phase-closing audit. It covers **every** public declaration of the five final
modules (90 declarations: theorems and definitions), plus the two baseline norm theorems
they rest on, for 92 audited names in total. The subset shipped with the agent entry
covered only the first phase (31 names).

Acceptable output: every line reports axioms contained in `{propext, Classical.choice,
Quot.sound}`, or no axioms at all. Any `sorryAx` is a failure.
-/

/-! ## ThresholdCert — abstract layer (20 declarations) -/

#print axioms ThresholdCert.CertifiedAbove
#print axioms ThresholdCert.CertifiedNotAbove
#print axioms ThresholdCert.Uncertified
#print axioms ThresholdCert.superlevel
#print axioms ThresholdCert.uncertaintyBand
#print axioms ThresholdCert.coord_perturbation
#print axioms ThresholdCert.certifiedAbove_sound
#print axioms ThresholdCert.certifiedNotAbove_sound
#print axioms ThresholdCert.trichotomy
#print axioms ThresholdCert.trichotomy_of_bounds
#print axioms ThresholdCert.diff_subsets
#print axioms ThresholdCert.symmDiff_subset_band
#print axioms ThresholdCert.uncertaintyBand_eq_empty_of_mul_eq_zero
#print axioms ThresholdCert.superlevel_eq_of_mul_eq_zero
#print axioms ThresholdCert.raw_above_sound
#print axioms ThresholdCert.raw_notAbove_sound
#print axioms ThresholdCert.nonstrict_above_unsound
#print axioms ThresholdCert.open_band_fails
#print axioms ThresholdCert.uncertified_not_wrong
#print axioms ThresholdCert.smoothed_cert_not_raw_cert

/-! ## ThresholdCert.Db2 — periodic db2 bridge (16 declarations) -/

#print axioms ThresholdCert.Db2.cascadeL
#print axioms ThresholdCert.Db2.cascadeC
#print axioms ThresholdCert.Db2.cascade1_opNorm_le_L
#print axioms ThresholdCert.Db2.cascade1_opNorm_eq_C
#print axioms ThresholdCert.Db2.cascadeC_nonneg
#print axioms ThresholdCert.Db2.cascadeC_le_L
#print axioms ThresholdCert.Db2.coord_perturbation_uniform
#print axioms ThresholdCert.Db2.certifiedAbove_sound_uniform
#print axioms ThresholdCert.Db2.certifiedNotAbove_sound_uniform
#print axioms ThresholdCert.Db2.symmDiff_subset_band_uniform
#print axioms ThresholdCert.Db2.superlevel_eq_uniform_of_eps_zero
#print axioms ThresholdCert.Db2.coord_perturbation_exact
#print axioms ThresholdCert.Db2.certifiedAbove_sound_exact
#print axioms ThresholdCert.Db2.certifiedNotAbove_sound_exact
#print axioms ThresholdCert.Db2.symmDiff_subset_band_exact
#print axioms ThresholdCert.Db2.band_exact_subset_uniform

/-! ## ThresholdCert.Nonperiodic — endpoint replication (24 declarations) -/

#print axioms ThresholdCert.Nonperiodic.clamp
#print axioms ThresholdCert.Nonperiodic.clamp_val
#print axioms ThresholdCert.Nonperiodic.clamp_of_neg
#print axioms ThresholdCert.Nonperiodic.clamp_of_mem
#print axioms ThresholdCert.Nonperiodic.clamp_of_ge
#print axioms ThresholdCert.Nonperiodic.clamp_natCast
#print axioms ThresholdCert.Nonperiodic.padLen
#print axioms ThresholdCert.Nonperiodic.padLen_pos
#print axioms ThresholdCert.Nonperiodic.cascadeSupport_le_padLen
#print axioms ThresholdCert.Nonperiodic.directOp
#print axioms ThresholdCert.Nonperiodic.directOp_apply
#print axioms ThresholdCert.Nonperiodic.padOp
#print axioms ThresholdCert.Nonperiodic.padOp_apply
#print axioms ThresholdCert.Nonperiodic.restrictOp
#print axioms ThresholdCert.Nonperiodic.restrictOp_apply
#print axioms ThresholdCert.Nonperiodic.val_natCast_padLen
#print axioms ThresholdCert.Nonperiodic.restrict_pad
#print axioms ThresholdCert.Nonperiodic.padOp_norm_le
#print axioms ThresholdCert.Nonperiodic.restrictOp_norm_le
#print axioms ThresholdCert.Nonperiodic.convolution_foldKernel
#print axioms ThresholdCert.Nonperiodic.cascadeOperator_one_apply
#print axioms ThresholdCert.Nonperiodic.pad_at_tap
#print axioms ThresholdCert.Nonperiodic.directOp_eq_restrict_cascade_pad
#print axioms ThresholdCert.Nonperiodic.directOp_eq_comp

/-! ## ThresholdCert.Nonperiodic — nonperiodic certificates (26 declarations) -/

#print axioms ThresholdCert.Nonperiodic.directOp_norm_le_periodic
#print axioms ThresholdCert.Nonperiodic.directOp_norm_le_C
#print axioms ThresholdCert.Nonperiodic.directOp_norm_le_L
#print axioms ThresholdCert.Nonperiodic.directOp_perturbation_C
#print axioms ThresholdCert.Nonperiodic.directOp_perturbation_L
#print axioms ThresholdCert.Nonperiodic.directOp_coord_perturbation_C
#print axioms ThresholdCert.Nonperiodic.directOp_coord_perturbation_L
#print axioms ThresholdCert.Nonperiodic.above_sound_C
#print axioms ThresholdCert.Nonperiodic.notAbove_sound_C
#print axioms ThresholdCert.Nonperiodic.symmDiff_subset_band_C
#print axioms ThresholdCert.Nonperiodic.above_sound_L
#print axioms ThresholdCert.Nonperiodic.notAbove_sound_L
#print axioms ThresholdCert.Nonperiodic.symmDiff_subset_band_L
#print axioms ThresholdCert.Nonperiodic.directOp_n_one
#print axioms ThresholdCert.Nonperiodic.cascadeTap_zero_values
#print axioms ThresholdCert.Nonperiodic.directOp_zero_one
#print axioms ThresholdCert.Nonperiodic.stepSignal2
#print axioms ThresholdCert.Nonperiodic.spikeSignal3
#print axioms ThresholdCert.Nonperiodic.check_direct_j0_n2
#print axioms ThresholdCert.Nonperiodic.check_periodic_j0_n2
#print axioms ThresholdCert.Nonperiodic.check_direct_j0_n3
#print axioms ThresholdCert.Nonperiodic.check_periodic_j0_n3
#print axioms ThresholdCert.Nonperiodic.check_direct_j1_n2
#print axioms ThresholdCert.Nonperiodic.check_periodic_j1_n2
#print axioms ThresholdCert.Nonperiodic.wrapSignal2
#print axioms ThresholdCert.Nonperiodic.unpadded_periodic_differs

/-! ## ThresholdCert.Nonperiodic — constant preservation (new) (4 declarations) -/

#print axioms ThresholdCert.Nonperiodic.cascadeInt_sum
#print axioms ThresholdCert.Nonperiodic.cascadeTap_sum_one
#print axioms ThresholdCert.Nonperiodic.directOp_const
#print axioms ThresholdCert.Nonperiodic.directOp_one_eq_id

/-! ## Baseline theorems reused (declared in `Solution.lean`) -/

#print axioms TWSPeriodic.cascade_opNorm_uniform
#print axioms TWSPeriodic.cascade_opNorm_formula
