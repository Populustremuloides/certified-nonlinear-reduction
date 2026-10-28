import Populus.Chapters.NonlinearModelReductionWithErrorBounds.CertifiedReduction.WitnessExistence
import Populus.Chapters.NonlinearModelReductionWithErrorBounds.CertifiedReduction.NominalErrorBounds
import Populus.Chapters.NonlinearModelReductionWithErrorBounds.CertifiedReduction.ConstructedCertificate

/-!
# Existence of every fixed matrix witness in the main theorem

The nominal error witness is also constructed from actual full and reduced
Schur responses. No stability, gain finiteness, or storage witness for that
joint realization is smuggled in as a new premise.
-/
namespace Populus.ModelReduction.Certified
open scoped Matrix.Norms.L2Operator
noncomputable section
variable {q r m p p_u p_z : ℕ}

/-- The full-minus-reduced nominal channel admits a finite strict matrix
storage witness, derived from the two Schur components. -/
theorem nominal_error_storage_witness_exists [NeZero q] [NeZero r]
    (A : Mat q q) (A_hat : Mat r r) (B : Mat q m) (B_hat : Mat r m)
    (C : Mat p q) (C_hat : Mat p r) (hA : Schur A) (hA_hat : Schur A_hat) :
    ∃ U : StorageUpper (q+r), U.Valid (errorA A A_hat) (errorB B B_hat) (errorC C C_hat) := by
  have hy := exact_channel_gain_prefix A B C hA
  have hy_hat := exact_channel_gain_prefix A_hat B_hat C_hat hA_hat
  have hz := exact_channel_gain_prefix A B (1 : Mat q q) hA
  have hz_hat := exact_channel_gain_prefix A_hat B_hat (1 : Mat r r) hA_hat
  obtain ⟨c,hc,hQz,hQy⟩ := schur_free_prefix_bounds A C hA
  obtain ⟨c_hat,hc_hat,hQz_hat,hQy_hat⟩ := schur_free_prefix_bounds A_hat C_hat hA_hat
  let E : Rn (q+r) ≃L[ℝ] Rn q×Rn r := errorCoordinates
  let g_y : ℝ := (channelGain A B C).toReal+(channelGain A_hat B_hat C_hat).toReal
  let g_z : ℝ := ‖E.symm.toContinuousLinearMap‖*((channelGain A B (1 : Mat q q)).toReal+
    (channelGain A_hat B_hat (1 : Mat r r)).toReal)
  let c_z : ℝ := ‖E.symm.toContinuousLinearMap‖*(c+c_hat)*‖E.toContinuousLinearMap‖
  have hTy : HasPrefixChannelGain (errorA A A_hat) (errorB B B_hat) (errorC C C_hat) g_y :=
    error_output_prefix_bound A A_hat B B_hat C C_hat _ _ hy hy_hat
  have hTz : HasPrefixChannelGain (errorA A A_hat) (errorB B B_hat) (1 : Mat (q+r) (q+r)) g_z :=
    error_state_prefix_bound A A_hat B B_hat _ _ hz hz_hat
  have hQz_err : HasFreePrefixBound (errorA A A_hat) (1 : Mat (q+r) (q+r)) c_z :=
    error_free_prefix_bound A A_hat c c_hat hQz hQz_hat
  have hQy_err := free_output_bound_of_state_bound (errorA A A_hat) (errorC C C_hat) c_z hQz_err
  let M := HilbertLinearRealization.ofBounds (errorA A A_hat) (errorB B B_hat) (errorC C C_hat)
    g_y g_z (‖errorC C C_hat‖*c_z) c_z hTy hTz hQy_err hQz_err
  have hnorm : ‖M.T_y‖≤g_y := norm_channelOperator_le _ _ _ g_y hTy
  obtain ⟨X,hX,hQ⟩ := strict_storage_witness_of_hilbert_realization M (g_y+1) (hnorm.trans_lt (by linarith))
  refine ⟨⟨g_y+1,X⟩,?_,hX,hQ.posSemidef⟩
  exact add_nonneg hTy.1 zero_le_one

/-- All fixed finite matrix witnesses exist under the two exact strict state-
channel margins and the feasible projection from the paper. -/
theorem reduction_matrix_witnesses_exist [NeZero q] [NeZero r]
    (N : NominalMatrices q m p p_u p_z) (W_r : Mat r q) (V_r : Mat q r)
    (hV : Function.Injective (act V_r))
    (hA : Schur N.A) (hA_hat : Schur (N.reduced W_r V_r).A)
    (hsmall : (channelGain N.A N.B_δz (1 : Mat q q)).toReal<1)
    (hsmall_hat : (channelGain (N.reduced W_r V_r).A (N.reduced W_r V_r).B_δz V_r).toReal<1) :
    ∃ R : ReductionWitnesses q r, R.Valid N W_r V_r := by
  obtain ⟨M,hM⟩ := matrix_gain_witnesses_exist N (1 : Mat q q) hA hsmall
  obtain ⟨M_hat,hM_hat⟩ := matrix_gain_witnesses_exist (N.reduced W_r V_r) V_r hA_hat hsmall_hat
  obtain ⟨U,hU⟩ := nominal_error_storage_witness_exists N.A (N.reduced W_r V_r).A
    N.B_u (N.reduced W_r V_r).B_u N.C (N.reduced W_r V_r).C hA hA_hat
  exact ⟨⟨M,M_hat,U⟩,hA,hA_hat,hV,hM,hM_hat,hU⟩

end
end Populus.ModelReduction.Certified
