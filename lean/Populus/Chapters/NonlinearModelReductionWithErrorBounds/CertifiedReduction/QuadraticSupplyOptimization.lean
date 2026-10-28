import Mathlib.Analysis.InnerProductSpace.LaxMilgram
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic

/-!
# Strictly concave Hilbert-space supply optimization

A supporting analytic step for the strict discrete bounded-real converse.
Coercivity is proved from an actual operator-norm gap. Lax–Milgram then
constructs the maximizing input as a bounded linear function of the initial
state. No desired storage inequality or quadratic-witness existence is assumed.
-/
namespace Populus.ModelReduction.Certified
open scoped InnerProductSpace
noncomputable section
variable {U Y Z X : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X]

def supplyPenalty (T : U →L[ℝ] Y) (S : U →L[ℝ] Z) (γ α : ℝ) : U →L[ℝ] U →L[ℝ] ℝ :=
  γ^2 • innerSL ℝ - (innerSL ℝ).bilinearComp T T - α • (innerSL ℝ).bilinearComp S S

@[simp] theorem supplyPenalty_apply (T : U →L[ℝ] Y) (S : U →L[ℝ] Z) (γ α : ℝ) (u v : U) :
    supplyPenalty T S γ α u v = γ^2 * ⟪u, v⟫_ℝ - ⟪T u, T v⟫_ℝ - α * ⟪S u, S v⟫_ℝ := by
  rfl

theorem supplyPenalty_symmetric (T : U →L[ℝ] Y) (S : U →L[ℝ] Z) (γ α : ℝ) (u v : U) :
    supplyPenalty T S γ α u v=supplyPenalty T S γ α v u := by
  simp only [supplyPenalty_apply,real_inner_comm]

/-- A strict operator-norm gap supplies the coercivity required by the
classical variational existence theorem; it is not presumed as a witness. -/
theorem supplyPenalty_coercive (T : U →L[ℝ] Y) (S : U →L[ℝ] Z) (γ α : ℝ)
    (hα : 0≤α) (hgap : 0<γ^2-‖T‖^2-α*‖S‖^2) : IsCoercive (supplyPenalty T S γ α) := by
  refine ⟨γ^2-‖T‖^2-α*‖S‖^2,hgap,fun u => ?_⟩
  have hT : ‖T u‖^2≤‖T‖^2*‖u‖^2 := by
    have h := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2 (T.le_opNorm u)
    simpa only [mul_pow] using h
  have hS : ‖S u‖^2≤‖S‖^2*‖u‖^2 := by
    have h := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2 (S.le_opNorm u)
    simpa only [mul_pow] using h
  have hαS := mul_le_mul_of_nonneg_left hS hα
  simp only [supplyPenalty_apply,real_inner_self_eq_norm_sq]
  nlinarith

def supplyCross (T : U →L[ℝ] Y) (S : U →L[ℝ] Z)
    (Q : X →L[ℝ] Y) (R : X →L[ℝ] Z) (α : ℝ) : X →L[ℝ] U :=
  T.adjoint.comp Q+α • S.adjoint.comp R

@[simp] theorem supplyCross_inner (T : U →L[ℝ] Y) (S : U →L[ℝ] Z)
    (Q : X →L[ℝ] Y) (R : X →L[ℝ] Z) (α : ℝ) (x : X) (u : U) :
    ⟪supplyCross T S Q R α x, u⟫_ℝ = ⟪Q x, T u⟫_ℝ + α * ⟪R x, S u⟫_ℝ := by
  simp only [supplyCross,ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply,inner_add_left,real_inner_smul_left,ContinuousLinearMap.adjoint_inner_left]

def optimalSupplyInput (T : U →L[ℝ] Y) (S : U →L[ℝ] Z)
    (Q : X →L[ℝ] Y) (R : X →L[ℝ] Z) (γ α : ℝ)
    (h : IsCoercive (supplyPenalty T S γ α)) : X →L[ℝ] U :=
  h.continuousLinearEquivOfBilin.symm.toContinuousLinearMap.comp (supplyCross T S Q R α)

/-- The actual maximizer satisfies its variational equation. -/
theorem optimalSupplyInput_equation (T : U →L[ℝ] Y) (S : U →L[ℝ] Z)
    (Q : X →L[ℝ] Y) (R : X →L[ℝ] Z) (γ α : ℝ)
    (h : IsCoercive (supplyPenalty T S γ α)) (x : X) (u : U) :
    supplyPenalty T S γ α (optimalSupplyInput T S Q R γ α h x) u=
      ⟪Q x, T u⟫_ℝ + α * ⟪R x, S u⟫_ℝ := by
  have heq := h.continuousLinearEquivOfBilin_apply
    (optimalSupplyInput T S Q R γ α h x) u
  have hc : h.continuousLinearEquivOfBilin (optimalSupplyInput T S Q R γ α h x)=
      supplyCross T S Q R α x := by
    exact h.continuousLinearEquivOfBilin.apply_symm_apply _
  rw [hc,supplyCross_inner] at heq
  exact heq.symm

def supplyValue (T : U →L[ℝ] Y) (S : U →L[ℝ] Z)
    (Q : X →L[ℝ] Y) (R : X →L[ℝ] Z) (γ α : ℝ) (x : X) (u : U) : ℝ :=
  ‖Q x+T u‖^2+α*‖R x+S u‖^2-γ^2*‖u‖^2

/-- Expand the actual supply as a strictly concave quadratic in its input. -/
theorem supplyValue_expansion (T : U →L[ℝ] Y) (S : U →L[ℝ] Z)
    (Q : X →L[ℝ] Y) (R : X →L[ℝ] Z) (γ α : ℝ) (x : X) (u : U) :
    supplyValue T S Q R γ α x u=‖Q x‖^2+α*‖R x‖^2+
      2*(⟪Q x, T u⟫_ℝ + α * ⟪R x, S u⟫_ℝ)-supplyPenalty T S γ α u u := by
  simp only [supplyValue,norm_add_sq_real,supplyPenalty_apply,real_inner_self_eq_norm_sq]
  ring

/-- Completion of the square around the constructed maximizing input. -/
theorem supplyValue_completion (T : U →L[ℝ] Y) (S : U →L[ℝ] Z)
    (Q : X →L[ℝ] Y) (R : X →L[ℝ] Z) (γ α : ℝ)
    (h : IsCoercive (supplyPenalty T S γ α)) (x : X) (u : U) :
    supplyValue T S Q R γ α x u=
      supplyValue T S Q R γ α x (optimalSupplyInput T S Q R γ α h x)-
      supplyPenalty T S γ α (u-optimalSupplyInput T S Q R γ α h x)
        (u-optimalSupplyInput T S Q R γ α h x) := by
  let k := optimalSupplyInput T S Q R γ α h x
  let B := supplyPenalty T S γ α
  have hsub : B (u-k) (u-k)=B u u-2*B k u+B k k := by
    simp only [map_sub,ContinuousLinearMap.sub_apply]
    have hs : B u k=B k u := supplyPenalty_symmetric T S γ α u k
    rw [hs]
    ring
  have hoptu : B k u=⟪Q x, T u⟫_ℝ + α * ⟪R x, S u⟫_ℝ :=
    optimalSupplyInput_equation T S Q R γ α h x u
  have hoptk : B k k=⟪Q x, T k⟫_ℝ + α * ⟪R x, S k⟫_ℝ :=
    optimalSupplyInput_equation T S Q R γ α h x k
  change supplyValue T S Q R γ α x u=supplyValue T S Q R γ α x k-B (u-k) (u-k)
  rw [supplyValue_expansion,supplyValue_expansion,← hoptu,← hoptk,hsub]
  dsimp only [B]
  ring

/-- The variationally constructed finite-energy input is an actual global
maximizer of the infinite-horizon supply, not just a stationary candidate. -/
theorem optimalSupplyInput_maximizes (T : U →L[ℝ] Y) (S : U →L[ℝ] Z)
    (Q : X →L[ℝ] Y) (R : X →L[ℝ] Z) (γ α : ℝ)
    (h : IsCoercive (supplyPenalty T S γ α)) (x : X) (u : U) :
    supplyValue T S Q R γ α x u≤supplyValue T S Q R γ α x (optimalSupplyInput T S Q R γ α h x) := by
  rw [supplyValue_completion T S Q R γ α h x u]
  have hcopy := h
  rcases hcopy with ⟨c,hc,hbound⟩
  have hnonneg : 0≤supplyPenalty T S γ α
      (u-optimalSupplyInput T S Q R γ α h x) (u-optimalSupplyInput T S Q R γ α h x) :=
    (mul_nonneg (mul_nonneg hc.le (norm_nonneg _)) (norm_nonneg _)).trans (hbound _)
  linarith

end
end Populus.ModelReduction.Certified
