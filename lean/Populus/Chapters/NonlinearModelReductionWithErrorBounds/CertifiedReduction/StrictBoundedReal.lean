import Populus.Chapters.NonlinearModelReductionWithErrorBounds.CertifiedReduction.StrictStorageConstruction
import Populus.Chapters.NonlinearModelReductionWithErrorBounds.CertifiedReduction.SchurChannelBounds
import Populus.Chapters.NonlinearModelReductionWithErrorBounds.CertifiedReduction.StorageWitnessAdapter

/-!
# Strict discrete bounded-real witness existence

The converse is proved through actual Hilbert channel operators and a genuine
maximized-supply storage, not assumed as a synthesis oracle. This closes the
classical existence assertion in the paper's named matrix-gain lemma.
-/
namespace Populus.ModelReduction.Certified
open scoped ENNReal Matrix.Norms.L2Operator
noncomputable section
variable {d b o : ℕ} {A : Mat d d} {B : Mat d b} {C : Mat o d}

/-- A positive state-cost coefficient and reserved input margin can always
be chosen below a strict actual operator-norm upper. -/
theorem strict_storage_witness_of_hilbert_realization
    (M : HilbertLinearRealization A B C) (g : ℝ) (hg : ‖M.T_y‖<g) :
    ∃ X : Mat d d, X.PosDef ∧ (-boundedRealMatrix A B C X g).PosDef := by
  let γ : ℝ := (g+‖M.T_y‖)/2
  have hgpos : 0<g := (norm_nonneg _).trans_lt hg
  have hγpos : 0<γ := by dsimp [γ]; positivity
  have hγlower : ‖M.T_y‖<γ := by dsimp [γ]; linarith
  have hγupper : γ<g := by dsimp [γ]; linarith
  have hgap0 : 0<γ^2-‖M.T_y‖^2 := sub_pos.2
    ((sq_lt_sq₀ (norm_nonneg _) hγpos.le).2 hγlower)
  let α : ℝ := (γ^2-‖M.T_y‖^2)/(2*(1+‖M.T_z‖^2))
  have hα : 0<α := div_pos hgap0 (by positivity)
  have hαeq : α*(2*(1+‖M.T_z‖^2))=γ^2-‖M.T_y‖^2 :=
    div_mul_cancel₀ _ (by positivity : 2*(1+‖M.T_z‖^2)≠0)
  have hgap : 0<γ^2-‖M.T_y‖^2-α*‖M.T_z‖^2 := by
    nlinarith [mul_nonneg hα.le (sq_nonneg ‖M.T_z‖)]
  have hc := supplyPenalty_coercive M.T_y M.T_z γ α hα.le hgap
  exact ⟨M.storageMatrix γ α hc,M.strict_storage_witness γ α g hα
    ((sq_lt_sq₀ hγpos.le hgpos.le).2 hγupper) hc⟩

/-- Schur nominal dynamics supply actual bounded Hilbert free/forced response
operators, with output-operator norm below the actual induced gain. -/
theorem exists_hilbert_realization_of_schur [NeZero d]
    (A : Mat d d) (B : Mat d b) (C : Mat o d) (hA : Schur A) :
    ∃ M : HilbertLinearRealization A B C, ‖M.T_y‖≤(channelGain A B C).toReal := by
  obtain ⟨c,hc,hQz,hQy⟩ := schur_free_prefix_bounds A C hA
  have hTy := exact_channel_gain_prefix A B C hA
  have hTz := exact_channel_gain_prefix A B (1 : Mat d d) hA
  let M := HilbertLinearRealization.ofBounds A B C
    (channelGain A B C).toReal (channelGain A B (1 : Mat d d)).toReal
    (‖C‖*c) c hTy hTz hQy hQz
  exact ⟨M,norm_channelOperator_le A B C _ hTy⟩

/-- Every real upper strictly above the true induced gain admits a strictly
positive-definite storage witness for the exact printed matrix block. -/
theorem strict_storage_witness_of_schur [NeZero d]
    (A : Mat d d) (B : Mat d b) (C : Mat o d) (hA : Schur A)
    (g : ℝ) (hg : (channelGain A B C).toReal<g) :
    ∃ X : Mat d d, X.PosDef ∧ (-boundedRealMatrix A B C X g).PosDef := by
  obtain ⟨M,hM⟩ := exists_hilbert_realization_of_schur A B C hA
  exact strict_storage_witness_of_hilbert_realization M g (hM.trans_lt hg)

/-- **Paper Lemma `lem:storage-gain`: Certified linear channel gain.**

The first conclusion is the actual channel's gain bound from the finite
storage inequality. The second proves, rather than assumes, existence of a
positive-definite strict witness for every upper strictly above the true gain.
All matrices, dimensions, Euclidean norms and zero-state responses coincide
with the paper. No controllability or observability hypothesis is added.
-/
theorem certified_linear_channel_gain [NeZero d]
    (A_g : Mat d d) (B_g : Mat d b) (C_g : Mat o d) (hA : Schur A_g)
    (X_g : Mat d d) (g : ℝ) (hg : 0≤g) (hX : X_g.PosDef)
    (hQ : (-boundedRealMatrix A_g B_g C_g X_g g).PosSemidef) :
    (∀ w, FiniteEnergy w →
      ℓ₂ (fun k => act C_g (linearResponse A_g B_g w k))≤ENNReal.ofReal g*ℓ₂ w) ∧
    (∀ g' : ℝ, (channelGain A_g B_g C_g).toReal<g' →
      ∃ X' : Mat d d, X'.PosDef ∧ (-boundedRealMatrix A_g B_g C_g X' g').PosDef) := by
  exact ⟨(hasChannelGain_of_hasPrefixChannelGain A_g B_g C_g g
      (matrix_storage_channel_prefix A_g B_g C_g X_g g hg hX hQ)).2,
    fun g' hg' => strict_storage_witness_of_schur A_g B_g C_g hA g' hg'⟩

end
end Populus.ModelReduction.Certified
