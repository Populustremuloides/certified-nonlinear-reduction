import Populus.Chapters.NonlinearModelReductionWithErrorBounds.CertifiedReduction.Lifting
import Populus.Chapters.NonlinearModelReductionWithErrorBounds.CertifiedReduction.NeuralUpdates

namespace Populus.ModelReduction.Certified
noncomputable section
variable {n q : ℕ}

theorem continuous_Φ_θ (C_x : Mat n q) (ψ_θ : ReLUNetwork n q) : Continuous (Φ_θ C_x ψ_θ) := by
  have hdag := (Matrix.toEuclideanLin (C_x_dagger C_x)).continuous_of_finiteDimensional
  have hR := (Matrix.toEuclideanLin (R_x C_x)).continuous_of_finiteDimensional
  exact hdag.add (hR.comp (ψ_θ.continuous_eval.sub continuous_const))

/-- Pointwise form of the already-proved supremum lifting approximation,
with compactness supplying the boundedness needed for the real supremum. -/
theorem neural_lifting_pointwise_approximation
    (C_x : Mat n q) (Φ : Rn n → Rn q) (hΦ : Continuous Φ)
    (hreconstruct : ∀ x, act C_x (Φ x)=x) (hΦ0 : Φ 0=0)
    (X : Set (Rn n)) (hX : IsCompact X) (h0 : (0 : Rn n)∈X)
    (ε : ℝ) (hε : 0<ε) :
    ∃ ψ_θ : ReLUNetwork n q,
      (∀ x, act C_x (Φ_θ C_x ψ_θ x)=x) ∧ Φ_θ C_x ψ_θ 0=0 ∧
      (∀ x : X, ‖Φ_θ C_x ψ_θ x-Φ x‖<ε) := by
  obtain ⟨ψ,hψC,hψ0,hψ⟩ := neural_lifting_uniform_approximation C_x Φ hΦ hreconstruct hΦ0 X hX h0 ε hε
  letI : CompactSpace X := isCompact_iff_compactSpace.mp hX
  have hc : Continuous (fun x : X => ‖Φ_θ C_x ψ x-Φ x‖) :=
    (((continuous_Φ_θ C_x ψ).sub hΦ).comp continuous_subtype_val).norm
  have hb : BddAbove (Set.range (fun x : X => ‖Φ_θ C_x ψ x-Φ x‖)) := (isCompact_range hc).bddAbove
  exact ⟨ψ,hψC,hψ0,fun x => (le_csSup hb ⟨x,rfl⟩).trans_lt hψ⟩

end
end Populus.ModelReduction.Certified
