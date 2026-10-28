import Populus.Chapters.NonlinearModelReductionWithErrorBounds.CertifiedReduction.PrincipalStorageInheritance

/-! Nested leading-coordinate reductions and their common applied-input maps. -/
namespace Populus.ModelReduction.Certified
open scoped BigOperators
noncomputable section
variable {q r n m p : ℕ}

def retainedA (A : Mat q q) (h : r≤q) : Mat r r :=
  fun i j => A (Fin.castLE h i) (Fin.castLE h j)
def retainedB (B : Mat q m) (h : r≤q) : Mat r m := fun i j => B (Fin.castLE h i) j
def retainedC (C : Mat p q) (h : r≤q) : Mat p r := fun i j => C i (Fin.castLE h j)

@[simp] theorem retainedA_self (A : Mat q q) : retainedA A le_rfl=A := rfl
@[simp] theorem retainedB_self (B : Mat q m) : retainedB B le_rfl=B := rfl
@[simp] theorem retainedC_self (C : Mat p q) : retainedC C le_rfl=C := rfl

@[simp] theorem retainedA_trans (A : Mat q q) (h₁ : n≤q) (h₂ : r≤n) :
    retainedA (retainedA A h₁) h₂=retainedA A (h₂.trans h₁) := rfl
@[simp] theorem retainedB_trans (B : Mat q m) (h₁ : n≤q) (h₂ : r≤n) :
    retainedB (retainedB B h₁) h₂=retainedB B (h₂.trans h₁) := rfl
@[simp] theorem retainedC_trans (C : Mat p q) (h₁ : n≤q) (h₂ : r≤n) :
    retainedC (retainedC C h₁) h₂=retainedC C (h₂.trans h₁) := rfl

theorem principalA_eq_retained {a b : ℕ} (A : Mat (a+b) (a+b)) :
    principalA (a:=a) (b:=b) A=retainedA A (Nat.le_add_right a b) := rfl
theorem principalB_eq_retained {a b : ℕ} (B : Mat (a+b) m) :
    principalB (a:=a) (b:=b) B=retainedB B (Nat.le_add_right a b) := rfl
theorem principalC_eq_retained {a b : ℕ} (C : Mat p (a+b)) :
    principalC (a:=a) (b:=b) C=retainedC C (Nat.le_add_right a b) := rfl

def nominalOutput (A : Mat q q) (B : Mat q m) (C : Mat p q)
    (u : ℕ → Rn m) : ℕ → Rn p := fun k => act C (linearResponse A B u k)

theorem principal_output_difference {a b : ℕ} (A : Mat (a+b) (a+b))
    (B : Mat (a+b) m) (C : Mat p (a+b)) (u : ℕ → Rn m) :
    (fun k => act C (linearResponse A B u k-
      join (balancedPrincipalResponse (b:=b) A B u k) (0 : Rn b)))=
      (fun k => nominalOutput A B C u k-
        nominalOutput (principalA A) (principalB B) (principalC C) u k) := by
  funext k
  simp only [nominalOutput,act_sub,act_principalC,principal_linearResponse]

def tailSum {r k : ℕ} (σ : Fin (r+k) → ℝ) : ℝ := ∑ j : Fin k,σ (Fin.natAdd r j)

theorem tailSum_succ {r k : ℕ} (σ : Fin (r+(k+1)) → ℝ) :
    tailSum σ=tailSum (r:=r) (k:=k) (fun i => σ (Fin.castSucc i))+σ (Fin.last (r+k)) := by
  rw [tailSum,Fin.sum_univ_castSucc]
  rfl

end
end Populus.ModelReduction.Certified
