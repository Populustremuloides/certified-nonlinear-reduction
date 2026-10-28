import Populus.Chapters.NonlinearModelReductionWithErrorBounds.CertifiedReduction.GainWitnesses

/-!
# Finite-matrix storage witnesses certify the actual induced channels

This is the sufficient part of paper `lem:storage-gain`, wired to the same
channel definition used by the nonlinear comparison. The strict-witness
existence converse is deliberately not claimed by this supporting theorem.
-/
namespace Populus.ModelReduction.Certified
open scoped ENNReal
noncomputable section
variable {d b o : ℕ}

/-- A checked block matrix inequality bounds actual channel prefixes. -/
theorem matrix_storage_channel_prefix
    (A : Mat d d) (B : Mat d b) (O : Mat o d) (X : Mat d d) (g : ℝ)
    (hg : 0≤g) (hX : X.PosDef) (hQ : (-boundedRealMatrix A B O X g).PosSemidef) :
    HasPrefixChannelGain A B O g := by
  refine ⟨hg,fun w K => ?_⟩
  have hp := matrix_storage_prefix_bound A B O X g hX hQ
    (linearResponse A B w) w rfl (fun k => rfl) K
  have hs := Real.sqrt_le_sqrt hp
  simpa [prefixNorm,Real.sqrt_mul (sq_nonneg g),Real.sqrt_sq hg] using hs

/-- The same finite matrix witness certifies the paper's supremum-of-ratios
induced gain, without assuming any output summability beforehand. -/
theorem matrix_storage_channel_gain
    (A : Mat d d) (B : Mat d b) (O : Mat o d) (X : Mat d d) (g : ℝ)
    (hg : 0≤g) (hX : X.PosDef) (hQ : (-boundedRealMatrix A B O X g).PosSemidef) :
    channelGain A B O ≤ ENNReal.ofReal g :=
  (prefix_channel_gain_iff_induced_gain_bound A B O g hg).1
    (matrix_storage_channel_prefix A B O X g hg hX hQ)

end
end Populus.ModelReduction.Certified
