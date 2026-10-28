import Populus.Chapters.NonlinearModelReductionWithErrorBounds.CertifiedReduction.RealSchur

/-!
# Compact approximation neighborhoods for a finite training dataset

These are the finite union of state balls and finite set of applied inputs
constructed in Appendix E. Approximate trajectories are not assumed to lie in
them: `rollout_converges_near_reference` derives that eventual containment.
-/
namespace Populus.ModelReduction.Certified
noncomputable section
variable {N q n m : ℕ}

def trainingNeighborhood (z : Fin N → ℕ → Rn q) (H : ℕ) : Set (Rn q) :=
  ⋃ i : Fin N, ⋃ k : Fin (H+1), Metric.closedBall (z i k) 1

theorem trainingNeighborhood_compact (z : Fin N → ℕ → Rn q) (H : ℕ) :
    IsCompact (trainingNeighborhood z H) := by
  exact isCompact_iUnion (fun i => isCompact_iUnion (fun k => isCompact_closedBall (z i k) 1))

theorem trainingNeighborhood_nonempty [NeZero N] (z : Fin N → ℕ → Rn q) (H : ℕ) :
    (trainingNeighborhood z H).Nonempty := by
  refine ⟨z 0 0,Set.mem_iUnion.2 ⟨0,Set.mem_iUnion.2 ⟨⟨0,by omega⟩,?_⟩⟩⟩
  simp

/-- Every state within the fixed reference radius is in the common compact
set, uniformly over all training samples and times through H. -/
theorem mem_trainingNeighborhood (z : Fin N → ℕ → Rn q) (H : ℕ)
    (i : Fin N) (k : ℕ) (hk : k≤H) (v : Rn q) (hv : ‖v-z i k‖<1) :
    v∈trainingNeighborhood z H := by
  refine Set.mem_iUnion.2 ⟨i,Set.mem_iUnion.2 ⟨⟨k,by omega⟩,?_⟩⟩
  exact Metric.mem_closedBall.2 (by simpa only [dist_eq_norm] using hv.le)

def trainingInputs (u : Fin N → ℕ → Rn m) (H : ℕ) : Set (Rn m) :=
  Set.range (fun ik : Fin N×Fin H => u ik.1 ik.2)

theorem trainingInputs_compact (u : Fin N → ℕ → Rn m) (H : ℕ) :
    IsCompact (trainingInputs u H) := Set.Finite.isCompact (Set.finite_range _)

theorem trainingInputs_nonempty [NeZero N] [NeZero H] (u : Fin N → ℕ → Rn m) :
    (trainingInputs u H).Nonempty := Set.range_nonempty _

theorem mem_trainingInputs (u : Fin N → ℕ → Rn m) (H : ℕ)
    (i : Fin N) (k : ℕ) (hk : k<H) : u i k∈trainingInputs u H :=
  ⟨(i,⟨k,hk⟩),rfl⟩

def trainingInitialStates (x₀ : Fin N → Rn n) : Set (Rn n) := insert 0 (Set.range x₀)

theorem trainingInitialStates_compact (x₀ : Fin N → Rn n) :
    IsCompact (trainingInitialStates x₀) := (Set.finite_range x₀).insert 0 |>.isCompact

@[simp] theorem zero_mem_trainingInitialStates (x₀ : Fin N → Rn n) :
    (0 : Rn n)∈trainingInitialStates x₀ := Set.mem_insert _ _

theorem mem_trainingInitialStates (x₀ : Fin N → Rn n) (i : Fin N) :
    x₀ i∈trainingInitialStates x₀ := Set.mem_insert_of_mem _ (Set.mem_range_self i)

end
end Populus.ModelReduction.Certified
