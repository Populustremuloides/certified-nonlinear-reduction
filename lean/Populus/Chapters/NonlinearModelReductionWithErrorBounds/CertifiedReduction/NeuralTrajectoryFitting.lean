import Populus.Chapters.NonlinearModelReductionWithErrorBounds.CertifiedReduction.LiftingContinuity
import Populus.Chapters.NonlinearModelReductionWithErrorBounds.CertifiedReduction.NearReferenceFitting
import Populus.Chapters.NonlinearModelReductionWithErrorBounds.CertifiedReduction.TrainingNeighborhoods

/-!
# Construct finite neural predictors with convergent training trajectories

This is the approximation/initialization/finite-horizon part of `thm:main`.
Every parameter contains three actual finite ReLU networks. Approximation
regions, networks and eventual trajectory containment are constructed below;
they are not assumptions about successful neural training or generalization.
-/
namespace Populus.ModelReduction.Certified
open scoped Topology Matrix.Norms.L2Operator
open Filter
noncomputable section
variable {n q m p p_u p_z N : ℕ}

structure NeuralParameter (n q m p_u p_z : ℕ) where
  ψ : ReLUNetwork n q
  a : ReLUNetwork q p_z
  c : ReLUNetwork (q+m) p_u

/-- **Constructive approximation part of the main theorem.** The reference
has exactly the continuous globally envelope-bounded factors assumed by the
paper. No preselected scalar modulus or approximate-trajectory containment
premise is supplied. `H` and `N` are positive, as for the prediction loss. -/
theorem finite_neural_training_trajectories_converge [NeZero N] [NeZero H]
    (M : NominalMatrices q m p p_u p_z) (C_x : Mat n q)
    (Φ : Rn n → Rn q) (hΦ : Continuous Φ)
    (hreconstruct : ∀ x, act C_x (Φ x)=x) (hΦ0 : Φ 0=0)
    (Δ_z_star : Rn q → Rn p_z) (Δ_u_star : Rn q → Rn m → Rn p_u)
    (hcz : Continuous Δ_z_star) (hcu : Continuous (fun v : Rn q×Rn m => Δ_u_star v.1 v.2))
    (hz : ∀ z, ‖Δ_z_star z‖≤‖z‖) (hu : ∀ z u, ‖Δ_u_star z u‖≤‖u‖)
    (x₀ : Fin N → Rn n) (u : Fin N → ℕ → Rn m) :
    ∃ θ : ℕ → NeuralParameter n q m p_u p_z,
      (∀ ℓ x, act C_x (Φ_θ C_x (θ ℓ).ψ x)=x) ∧
      (∀ ℓ, Φ_θ C_x (θ ℓ).ψ 0=0) ∧
      ∀ i : Fin N, ∀ k≤H,
        Tendsto (fun ℓ => rollout (neuralUpdate M (θ ℓ).a (θ ℓ).c)
          (Φ_θ C_x (θ ℓ).ψ (x₀ i)) (u i) k) atTop
          (nhds (rollout (M.fullUpdate Δ_z_star Δ_u_star) (Φ (x₀ i)) (u i) k)) := by
  classical
  let F_star := M.fullUpdate Δ_z_star Δ_u_star
  let z_star : Fin N → ℕ → Rn q := fun i => rollout F_star (Φ (x₀ i)) (u i)
  let K_z := trainingNeighborhood z_star H
  let K_u := trainingInputs u H
  have hKz : IsCompact K_z := trainingNeighborhood_compact z_star H
  have hKu : IsCompact K_u := trainingInputs_compact u H
  have hneZ : K_z.Nonempty := trainingNeighborhood_nonempty z_star H
  have hneU : K_u.Nonempty := trainingInputs_nonempty u
  let ez : C(K_z,Rn p_z) := ⟨fun z => Δ_z_star z,hcz.comp continuous_subtype_val⟩
  let eu : C(K_z ×ˢ K_u,Rn p_u) := ⟨fun v => Δ_u_star v.1.1 v.1.2,hcu.comp continuous_subtype_val⟩
  let η : ℕ → ℝ := fun ℓ => 1/((ℓ : ℝ)+1)
  have hηpos (ℓ : ℕ) : 0<η ℓ := by dsimp [η]; positivity
  have hη : Tendsto η atTop (nhds 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have happrox (ℓ : ℕ) := neural_update_uniform_approximation M K_z K_u hKz hKu hneZ hneU
    ez eu (fun z => hz z) (fun v => hu v.1.1 v.1.2) (η ℓ) (hηpos ℓ)
  choose a c hac using happrox
  let X₀ := trainingInitialStates x₀
  have hX₀ : IsCompact X₀ := trainingInitialStates_compact x₀
  have hψ (ℓ : ℕ) := neural_lifting_pointwise_approximation C_x Φ hΦ hreconstruct hΦ0
    X₀ hX₀ (zero_mem_trainingInitialStates x₀) (η ℓ) (hηpos ℓ)
  choose ψ hψC hψ0 hψapp using hψ
  let θ : ℕ → NeuralParameter n q m p_u p_z := fun ℓ => ⟨ψ ℓ,a ℓ,c ℓ⟩
  refine ⟨θ,hψC,hψ0,fun i => ?_⟩
  have hinit : Tendsto (fun ℓ => Φ_θ C_x (ψ ℓ) (x₀ i)) atTop (nhds (Φ (x₀ i))) := by
    apply tendsto_iff_norm_sub_tendsto_zero.2
    apply squeeze_zero (fun ℓ => norm_nonneg _) _ hη
    intro ℓ
    exact (hψapp ℓ ⟨x₀ i,mem_trainingInitialStates x₀ i⟩).le
  let d : ℕ → ℝ := fun ℓ => (‖M.B_δu‖+‖M.B_δz‖)*η ℓ
  have hd : Tendsto d atTop (nhds 0) := by simpa [d] using tendsto_const_nhds.mul hη
  have hcont (k : ℕ) : Continuous (fun z => F_star z (u i k)) := by
    have hA := (Matrix.toEuclideanLin M.A).continuous_of_finiteDimensional
    have hBz := (Matrix.toEuclideanLin M.B_δz).continuous_of_finiteDimensional
    have hBu := (Matrix.toEuclideanLin M.B_δu).continuous_of_finiteDimensional
    exact ((hA.add continuous_const).add
      (hBu.comp (hcu.comp (continuous_id.prodMk continuous_const)))).add (hBz.comp hcz)
  apply rollout_converges_near_reference (fun ℓ => neuralUpdate M (a ℓ) (c ℓ)) F_star
    (fun ℓ => Φ_θ C_x (ψ ℓ) (x₀ i)) (Φ (x₀ i)) (u i) K_z H 1 zero_lt_one d hd hinit
  · intro k hk z hz'
    exact mem_trainingNeighborhood z_star H i k hk z hz'
  · intro ℓ k hk z hz'
    have hu' : u i k∈K_u := mem_trainingInputs u H i k hk
    exact hac ℓ ⟨z,hz'⟩ ⟨u i k,hu'⟩
  · intro k _
    exact (hcont k).continuousAt

end
end Populus.ModelReduction.Certified
