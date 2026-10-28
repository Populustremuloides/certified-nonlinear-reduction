import Populus.Chapters.NonlinearModelReductionWithErrorBounds.CertifiedReduction.StrictBoundedReal
import Populus.Chapters.NonlinearModelReductionWithErrorBounds.CertifiedReduction.MatrixWitnesses

/-!
# Fixed finite matrix witnesses exist under a strict true-gain margin

This is the witness-selection step in the constructive main proof. The
strict bounded-real existence theorem is proved in the imported module; no
witness-existence conclusion is supplied as a new reference hypothesis.
-/
namespace Populus.ModelReduction.Certified
noncomputable section
variable {d q m p p_u p_z : ℕ}

def storageUpperOfSchur [NeZero d] (A : Mat d d) (B : Mat d m) (O : Mat p d)
    (hA : Schur A) (g : ℝ) (hg : (channelGain A B O).toReal<g) : StorageUpper d where
  g := g
  X := (strict_storage_witness_of_schur A B O hA g hg).choose

theorem storageUpperOfSchur_valid [NeZero d] (A : Mat d d) (B : Mat d m) (O : Mat p d)
    (hA : Schur A) (g : ℝ) (hg : (channelGain A B O).toReal<g) :
    (storageUpperOfSchur A B O hA g hg).Valid A B O := by
  have h := (strict_storage_witness_of_schur A B O hA g hg).choose_spec
  exact ⟨ENNReal.toReal_nonneg.trans hg.le,h.1,h.2.posSemidef⟩

/-- The six storage witnesses can be fixed once, with the autonomous upper
strictly below one, under precisely the paper's strict true-gain margin. -/
theorem matrix_gain_witnesses_exist [NeZero d]
    (N : NominalMatrices d m p p_u p_z) (O : Mat q d) (hA : Schur N.A)
    (hsmall : (channelGain N.A N.B_δz O).toReal<1) :
    ∃ M : MatrixGainWitnesses d, M.Valid N O := by
  let γ_z : ℝ := ((channelGain N.A N.B_δz O).toReal+1)/2
  have hγ : (channelGain N.A N.B_δz O).toReal<γ_z := by dsimp [γ_z]; linarith
  have hγ1 : γ_z<1 := by dsimp [γ_z]; linarith
  let M : MatrixGainWitnesses d := {
    state_u := storageUpperOfSchur N.A N.B_u O hA ((channelGain N.A N.B_u O).toReal+1) (by linarith)
    state_δu := storageUpperOfSchur N.A N.B_δu O hA ((channelGain N.A N.B_δu O).toReal+1) (by linarith)
    state_δz := storageUpperOfSchur N.A N.B_δz O hA γ_z hγ
    output_u := storageUpperOfSchur N.A N.B_u N.C hA ((channelGain N.A N.B_u N.C).toReal+1) (by linarith)
    output_δu := storageUpperOfSchur N.A N.B_δu N.C hA ((channelGain N.A N.B_δu N.C).toReal+1) (by linarith)
    output_δz := storageUpperOfSchur N.A N.B_δz N.C hA ((channelGain N.A N.B_δz N.C).toReal+1) (by linarith) }
  refine ⟨M,?_⟩
  exact ⟨storageUpperOfSchur_valid _ _ _ hA _ (by linarith),
    storageUpperOfSchur_valid _ _ _ hA _ (by linarith),
    storageUpperOfSchur_valid _ _ _ hA _ hγ,
    storageUpperOfSchur_valid _ _ _ hA _ (by linarith),
    storageUpperOfSchur_valid _ _ _ hA _ (by linarith),
    storageUpperOfSchur_valid _ _ _ hA _ (by linarith),hγ1⟩

end
end Populus.ModelReduction.Certified
