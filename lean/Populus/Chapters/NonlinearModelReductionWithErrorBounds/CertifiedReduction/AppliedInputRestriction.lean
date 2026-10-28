import Populus.Chapters.NonlinearModelReductionWithErrorBounds.CertifiedReduction.BalancedSteinCoordinates

/-! A nominal bound for augmented input ports controls the applied-input port. -/
namespace Populus.ModelReduction.Certified
open Matrix
noncomputable section
variable {q r m n p : ℕ}

def inputJoin (B : Mat q m) (D : Mat q n) : Mat q (m+n) :=
  fun i => Fin.addCases (B i) (D i)
def firstInputMatrix (B : Mat q (m+n)) : Mat q m := fun i j => B i (Fin.castAdd n j)

@[simp] theorem firstInputMatrix_inputJoin (B : Mat q m) (D : Mat q n) :
    firstInputMatrix (inputJoin B D)=B := by ext i j; simp [firstInputMatrix,inputJoin]

theorem firstInputMatrix_act (B : Mat q (m+n)) (u : Rn m) :
    act B (join u (0 : Rn n))=act (firstInputMatrix B) u := by
  ext i
  simp [act,Matrix.toEuclideanLin,Matrix.mulVec,dotProduct,join,firstInputMatrix,Fin.sum_univ_add]

theorem firstInputMatrix_response (A : Mat q q) (B : Mat q (m+n))
    (u : ℕ → Rn m) :
    linearResponse A B (fun k => join (u k) (0 : Rn n))=linearResponse A (firstInputMatrix B) u := by
  funext k
  induction k with
  | zero => rfl
  | succ k ih =>
    change act A (linearResponse A B (fun k => join (u k) (0 : Rn n)) k)+
      act B (join (u k) (0 : Rn n))=_
    rw [ih,firstInputMatrix_act]
    rfl

@[simp] theorem firstInputMatrix_retained (B : Mat q (m+n)) (h : r≤q) :
    firstInputMatrix (retainedB B h)=retainedB (firstInputMatrix B) h := rfl

theorem balanced_tail_applied_input {r k m n p : ℕ} (σ : Fin (r+k) → ℝ)
    (hσ : ∀ i,0<σ i) (A : Mat (r+k) (r+k)) (B : Mat (r+k) (m+n)) (C : Mat p (r+k))
    (hobs : ∀ z,diagonalEnergy σ (act A z)+‖act C z‖^2≤diagonalEnergy σ z)
    (hctrl : ∀ z u,diagonalEnergy (fun i => (σ i)⁻¹) (act A z+act B u)≤
      diagonalEnergy (fun i => (σ i)⁻¹) z+‖u‖^2) :
    inducedGain (fun u j => nominalOutput A (firstInputMatrix B) C u j-
      nominalOutput (retainedA A (Nat.le_add_right r k))
        (retainedB (firstInputMatrix B) (Nat.le_add_right r k))
        (retainedC C (Nat.le_add_right r k)) u j)≤ENNReal.ofReal (2*tailSum σ) := by
  apply balanced_tail_induced_gain σ hσ A (firstInputMatrix B) C hobs
  intro z u
  have h := hctrl z (join u (0 : Rn n))
  simpa only [firstInputMatrix_act,norm_join_zero] using h

end
end Populus.ModelReduction.Certified
