import Populus.Chapters.NonlinearModelReductionWithErrorBounds.CertifiedReduction.BalancedTailStorage
import Populus.Chapters.NonlinearModelReductionWithErrorBounds.CertifiedReduction.LinearResponseAlgebra

/-! One-step dissipation for an actual principal balanced truncation. -/
namespace Populus.ModelReduction.Certified
open scoped InnerProductSpace
noncomputable section
variable {a b m p : ℕ}

theorem act_sub (A : Mat a b) (x y : Rn b) : act A (x-y)=act A x-act A y :=
  map_sub (Matrix.toEuclideanLin A) x y

theorem join_take_zero_decomposition (z : Rn (a+b)) :
    join (take z) (0 : Rn b)=z-join (0 : Rn a) (drop z) := by
  ext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [join,take,drop]

def balancedErrorStorage (σ : Fin a → ℝ) (τ : ℝ)
    (x : Rn (a+b)) (xr : Rn a) : ℝ :=
  balancedEnergy σ τ (x-join xr (0 : Rn b))+
    τ^2*balancedEnergy (fun i => (σ i)⁻¹) τ⁻¹ (x+join xr (0 : Rn b))

theorem balanced_principal_one_step (σ : Fin a → ℝ) (τ : ℝ) (hτ : 0<τ)
    (A : Mat (a+b) (a+b)) (B : Mat (a+b) m) (C : Mat p (a+b))
    (hobs : ∀ z,balancedEnergy σ τ (act A z)+‖act C z‖^2≤balancedEnergy σ τ z)
    (hctrl : ∀ z u,balancedEnergy (fun i => (σ i)⁻¹) τ⁻¹ (act A z+act B u)≤
      balancedEnergy (fun i => (σ i)⁻¹) τ⁻¹ z+‖u‖^2)
    (x : Rn (a+b)) (xr : Rn a) (u : Rn m) :
    balancedErrorStorage σ τ (act A x+act B u)
        (take (act A (join xr (0 : Rn b))+act B u))+
        ‖act C (x-join xr (0 : Rn b))‖^2≤
      balancedErrorStorage σ τ x xr+4*τ^2*‖u‖^2 := by
  let jxr := join xr (0 : Rn b)
  let r := act A jxr+act B u
  let v := drop r
  let am := act A (x-jxr)
  let ap := act A (x+jxr)+act B ((2:ℝ) • u)
  have hav : drop ap-drop am=(2:ℝ) • v := by
    have he : ap-am=(2:ℝ) • r := by
      dsimp [ap,am,r]
      simp only [act_add,act_smul,act_sub]
      module
    change drop ap-drop am=(2:ℝ) • drop r
    ext i
    have hd := congrArg (fun z : Rn (a+b) => z (Fin.natAdd a i)) he
    simpa [drop] using hd
  have hm : act A x+act B u-join (take r) (0 : Rn b)=am+join (0 : Rn a) v := by
    rw [join_take_zero_decomposition]
    dsimp [am,r,v]
    simp only [act_sub]
    module
  have hp : act A x+act B u+join (take r) (0 : Rn b)=ap-join (0 : Rn a) v := by
    rw [join_take_zero_decomposition]
    dsimp [ap,r,v]
    simp only [act_add,act_smul]
    module
  have hc := balanced_tail_cancellation σ τ (ne_of_gt hτ) am ap v hav
  have ho := hobs (x-jxr)
  have ht := hctrl (x+jxr) ((2:ℝ) • u)
  have hn : ‖(2:ℝ) • u‖^2=4*‖u‖^2 := by rw [norm_smul]; norm_num; ring
  rw [hn] at ht
  change balancedEnergy σ τ (act A x+act B u-join (take r) (0 : Rn b))+
      τ^2*balancedEnergy (fun i => (σ i)⁻¹) τ⁻¹
        (act A x+act B u+join (take r) (0 : Rn b))+_≤_
  rw [hm,hp,hc]
  change _≤balancedEnergy σ τ (x-jxr)+
    τ^2*balancedEnergy (fun i => (σ i)⁻¹) τ⁻¹ (x+jxr)+4*τ^2*‖u‖^2
  have hmul := mul_le_mul_of_nonneg_left ht (sq_nonneg τ)
  dsimp [am,ap]
  nlinarith [sq_nonneg ‖v‖]

end
end Populus.ModelReduction.Certified
