import Populus.Chapters.NonlinearModelReductionWithErrorBounds.CertifiedReduction.StorageWitnessAdapter

/-!
# Finite matrices supplying the six channel bounds

Witness data consist only of real scalars and square storage matrices. Their
validity consists of the printed positive-definiteness and block matrix
inequalities. Nonlinear gain conclusions are derived rather than stored.
-/
namespace Populus.ModelReduction.Certified
noncomputable section
variable {d q m p p_u p_z : ℕ}

structure StorageUpper (d : ℕ) where
  g : ℝ
  X : Mat d d

namespace StorageUpper

def Valid (U : StorageUpper d) (A : Mat d d) (B : Mat d m) (O : Mat p d) : Prop :=
  0≤U.g ∧ U.X.PosDef ∧ (-boundedRealMatrix A B O U.X U.g).PosSemidef

theorem channel_prefix (U : StorageUpper d) (h : U.Valid A B O) :
    HasPrefixChannelGain A B O U.g := matrix_storage_channel_prefix A B O U.X U.g h.1 h.2.1 h.2.2

end StorageUpper

structure MatrixGainWitnesses (d : ℕ) where
  state_u : StorageUpper d
  state_δu : StorageUpper d
  state_δz : StorageUpper d
  output_u : StorageUpper d
  output_δu : StorageUpper d
  output_δz : StorageUpper d

namespace MatrixGainWitnesses

def bounds (M : MatrixGainWitnesses d) : GainBounds where
  g_u := M.state_u.g
  g_δu := M.state_δu.g
  g_δz := M.state_δz.g
  h_u := M.output_u.g
  h_δu := M.output_δu.g
  h_δz := M.output_δz.g

def Valid (M : MatrixGainWitnesses d) (N : NominalMatrices d m p p_u p_z) (O : Mat q d) : Prop :=
  M.state_u.Valid N.A N.B_u O ∧ M.state_δu.Valid N.A N.B_δu O ∧
  M.state_δz.Valid N.A N.B_δz O ∧ M.output_u.Valid N.A N.B_u N.C ∧
  M.output_δu.Valid N.A N.B_δu N.C ∧ M.output_δz.Valid N.A N.B_δz N.C ∧ M.state_δz.g<1

/-- Every finite-matrix check implies the exact channel-bound premises used
by the nonlinear argument, consistently in all six terms. -/
theorem valid_bounds (M : MatrixGainWitnesses d) (N : NominalMatrices d m p p_u p_z)
    (O : Mat q d) (hM : M.Valid N O) : M.bounds.Valid N O := by
  rcases hM with ⟨h₁,h₂,h₃,h₄,h₅,h₆,hsmall⟩
  exact ⟨M.state_u.channel_prefix h₁,M.state_δu.channel_prefix h₂,M.state_δz.channel_prefix h₃,
    M.output_u.channel_prefix h₄,M.output_δu.channel_prefix h₅,M.output_δz.channel_prefix h₆,hsmall⟩

end MatrixGainWitnesses
end
end Populus.ModelReduction.Certified
