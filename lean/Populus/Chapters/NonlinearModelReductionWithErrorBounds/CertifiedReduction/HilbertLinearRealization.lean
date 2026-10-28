import Populus.Chapters.NonlinearModelReductionWithErrorBounds.CertifiedReduction.HilbertFreeResponses
import Populus.Chapters.NonlinearModelReductionWithErrorBounds.CertifiedReduction.QuadraticSupplyOptimization

/-!
# Hilbert realization and the dynamic supply identity

Every operator is tied to the literal nominal recurrence by an evaluation
identity. The constructor uses only the already-proved finite channel and free
response bounds. Prepending an actual input splits its supply into one stage
and the actual continuation from A x+B u; no dynamic-programming equation is
assumed as a certificate premise.
-/
namespace Populus.ModelReduction.Certified
noncomputable section
variable {d b o : ℕ}

structure HilbertLinearRealization (A : Mat d d) (B : Mat d b) (C : Mat o d) where
  T_y : L2 (Rn b) →L[ℝ] L2 (Rn o)
  T_z : L2 (Rn b) →L[ℝ] L2 (Rn d)
  Q_y : Rn d →L[ℝ] L2 (Rn o)
  Q_z : Rn d →L[ℝ] L2 (Rn d)
  T_y_apply : ∀ u k, T_y u k=act C (linearResponse A B (fun j => u j) k)
  T_z_apply : ∀ u k, T_z u k=linearResponse A B (fun j => u j) k
  Q_y_apply : ∀ x k, Q_y x k=act C (freeResponse A x k)
  Q_z_apply : ∀ x k, Q_z x k=freeResponse A x k

namespace HilbertLinearRealization

def ofBounds (A : Mat d d) (B : Mat d b) (C : Mat o d)
    (g_y g_z c_y c_z : ℝ)
    (hTy : HasPrefixChannelGain A B C g_y) (hTz : HasPrefixChannelGain A B (1 : Mat d d) g_z)
    (hQy : HasFreePrefixBound A C c_y) (hQz : HasFreePrefixBound A (1 : Mat d d) c_z) :
    HilbertLinearRealization A B C where
  T_y := channelOperator A B C g_y hTy
  T_z := channelOperator A B (1 : Mat d d) g_z hTz
  Q_y := freeOperator A C c_y hQy
  Q_z := freeOperator A (1 : Mat d d) c_z hQz
  T_y_apply := channelOperator_apply A B C g_y hTy
  T_z_apply := by intro u k; simp
  Q_y_apply := freeOperator_apply A C c_y hQy
  Q_z_apply := by intro x k; simp

theorem output_total_apply (M : HilbertLinearRealization A B C) (x : Rn d) (u : L2 (Rn b)) (k : ℕ) :
    (M.Q_y x+M.T_y u) k=act C (rollout (fun z v => act A z+act B v) x (fun j => u j) k) := by
  change M.Q_y x k+M.T_y u k=_
  rw [M.Q_y_apply,M.T_y_apply,linear_trajectory_decomposition,act_add]

theorem state_total_apply (M : HilbertLinearRealization A B C) (x : Rn d) (u : L2 (Rn b)) (k : ℕ) :
    (M.Q_z x+M.T_z u) k=rollout (fun z v => act A z+act B v) x (fun j => u j) k := by
  change M.Q_z x k+M.T_z u k=_
  rw [M.Q_z_apply,M.T_z_apply,linear_trajectory_decomposition]

/-- Shift an actual trajectory after prepending one input sample. -/
theorem trajectory_prepend (A : Mat d d) (B : Mat d b) (x : Rn d)
    (u₀ : Rn b) (u : L2 (Rn b)) (k : ℕ) :
    rollout (fun z v => act A z+act B v) x (fun j => L2.prepend u₀ u j) (k+1)=
      rollout (fun z v => act A z+act B v) (act A x+act B u₀) (fun j => u j) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change act A (rollout (fun z v => act A z+act B v) x (fun j => L2.prepend u₀ u j) (k+1))+
      act B (L2.prepend u₀ u (k+1))=_
    rw [ih,L2.prepend_succ]
    rfl

theorem output_prepend (M : HilbertLinearRealization A B C) (x : Rn d)
    (u₀ : Rn b) (u : L2 (Rn b)) :
    M.Q_y x+M.T_y (L2.prepend u₀ u)=
      L2.prepend (act C x) (M.Q_y (act A x+act B u₀)+M.T_y u) := by
  apply lp.ext
  funext k
  cases k with
  | zero =>
    change (M.Q_y x+M.T_y (L2.prepend u₀ u)) 0=act C x
    rw [M.output_total_apply]
    rfl
  | succ k =>
    change (M.Q_y x+M.T_y (L2.prepend u₀ u)) (k+1)=(M.Q_y (act A x+act B u₀)+M.T_y u) k
    rw [M.output_total_apply,M.output_total_apply,trajectory_prepend]

theorem state_prepend (M : HilbertLinearRealization A B C) (x : Rn d)
    (u₀ : Rn b) (u : L2 (Rn b)) :
    M.Q_z x+M.T_z (L2.prepend u₀ u)=
      L2.prepend x (M.Q_z (act A x+act B u₀)+M.T_z u) := by
  apply lp.ext
  funext k
  cases k with
  | zero =>
    change (M.Q_z x+M.T_z (L2.prepend u₀ u)) 0=x
    rw [M.state_total_apply]
    rfl
  | succ k =>
    change (M.Q_z x+M.T_z (L2.prepend u₀ u)) (k+1)=(M.Q_z (act A x+act B u₀)+M.T_z u) k
    rw [M.state_total_apply,M.state_total_apply,trajectory_prepend]

/-- Exact decomposition of the infinite-horizon supply, with actual finite-
energy membership already supplied by the Hilbert operators. -/
theorem supply_prepend (M : HilbertLinearRealization A B C) (γ α : ℝ)
    (x : Rn d) (u₀ : Rn b) (u : L2 (Rn b)) :
    supplyValue M.T_y M.T_z M.Q_y M.Q_z γ α x (L2.prepend u₀ u)=
      ‖act C x‖^2+α*‖x‖^2-γ^2*‖u₀‖^2+
      supplyValue M.T_y M.T_z M.Q_y M.Q_z γ α (act A x+act B u₀) u := by
  dsimp only [supplyValue]
  rw [M.output_prepend,M.state_prepend,L2.norm_prepend_sq,L2.norm_prepend_sq,L2.norm_prepend_sq]
  ring

/-- The maximized supply satisfies the genuine one-step storage inequality. -/
theorem maximized_supply_step (M : HilbertLinearRealization A B C) (γ α : ℝ)
    (h : IsCoercive (supplyPenalty M.T_y M.T_z γ α)) (x : Rn d) (u₀ : Rn b) :
    let V := fun z => supplyValue M.T_y M.T_z M.Q_y M.Q_z γ α z
      (optimalSupplyInput M.T_y M.T_z M.Q_y M.Q_z γ α h z)
    V (act A x+act B u₀)+‖act C x‖^2+α*‖x‖^2≤V x+γ^2*‖u₀‖^2 := by
  dsimp only
  have hmax := optimalSupplyInput_maximizes M.T_y M.T_z M.Q_y M.Q_z γ α h x
    (L2.prepend u₀ (optimalSupplyInput M.T_y M.T_z M.Q_y M.Q_z γ α h (act A x+act B u₀)))
  rw [M.supply_prepend] at hmax
  linarith

end HilbertLinearRealization
end
end Populus.ModelReduction.Certified
