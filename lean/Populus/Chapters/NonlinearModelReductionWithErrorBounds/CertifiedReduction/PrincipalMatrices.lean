import Populus.Chapters.NonlinearModelReductionWithErrorBounds.CertifiedReduction.BalancedSteinError

/-! Literal retained principal matrices and their actual reduced responses. -/
namespace Populus.ModelReduction.Certified
open Matrix
noncomputable section
variable {a b m p : ℕ}

def principalA (A : Mat (a+b) (a+b)) : Mat a a :=
  fun i j => A (Fin.castAdd b i) (Fin.castAdd b j)
def principalB (B : Mat (a+b) m) : Mat a m := fun i j => B (Fin.castAdd b i) j
def principalC (C : Mat p (a+b)) : Mat p a := fun i j => C i (Fin.castAdd b j)

theorem act_principalA (A : Mat (a+b) (a+b)) (z : Rn a) :
    act (principalA A) z=take (act A (join z (0 : Rn b))) := by
  ext i
  simp [act,Matrix.toEuclideanLin,Matrix.mulVec,dotProduct,principalA,take,join,Fin.sum_univ_add]

theorem act_principalB (B : Mat (a+b) m) (u : Rn m) :
    act (principalB B) u=take (act B u) := by ext i; rfl

theorem act_principalC (C : Mat p (a+b)) (z : Rn a) :
    act (principalC C) z=act C (join z (0 : Rn b)) := by
  ext i
  simp [act,Matrix.toEuclideanLin,Matrix.mulVec,dotProduct,principalC,join,Fin.sum_univ_add]

theorem principal_linearResponse (A : Mat (a+b) (a+b)) (B : Mat (a+b) m)
    (u : ℕ → Rn m) :
    linearResponse (principalA A) (principalB B) u=balancedPrincipalResponse (b:=b) A B u := by
  funext k
  induction k with
  | zero => rfl
  | succ k ih =>
    change act (principalA A) (linearResponse (principalA A) (principalB B) u k)+
      act (principalB B) (u k)=_
    rw [ih,act_principalA,act_principalB]
    ext i
    rfl

end
end Populus.ModelReduction.Certified
