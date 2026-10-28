import Populus.Chapters.NonlinearModelReductionWithErrorBounds.CertifiedReduction.RetainedSchur

/-! Invertible nominal coordinate changes preserve the applied-input response. -/
namespace Populus.ModelReduction.Certified
open Matrix
noncomputable section
variable {q r m p : ℕ}

@[simp] theorem complexify_mul (A B : Mat q q) : complexify (A*B)=complexify A*complexify B := by
  exact Matrix.map_mul (L:=A) (M:=B) (f:=Complex.ofRealHom)

@[simp] theorem complexify_one : complexify (1 : Mat q q)=1 := by
  ext i j
  by_cases h : i=j <;> simp [complexify,Matrix.one_apply,h]

theorem schur_similarity (A T R : Mat q q) (hTR : T*R=1) (hRT : R*T=1)
    (hA : Schur A) : Schur (T*A*R) := by
  intro ζ hζ
  obtain ⟨v,hv,he⟩ := (matrix_mem_spectrum_iff_eigenvector _ ζ).1 hζ
  have hcTR : complexify T*complexify R=1 := by rw [← complexify_mul,hTR,complexify_one]
  have hcRT : complexify R*complexify T=1 := by rw [← complexify_mul,hRT,complexify_one]
  let w := complexify R *ᵥ v
  have hw : w≠0 := by
    intro hz
    have hh := congrArg (fun y => complexify T *ᵥ y) hz
    simp only [w,Matrix.mulVec_mulVec,hcTR,Matrix.one_mulVec,Matrix.mulVec_zero] at hh
    exact hv hh
  have hew : complexify A *ᵥ w=ζ • w := by
    have hh := congrArg (fun y => complexify R *ᵥ y) he
    simp only [complexify_mul,Matrix.mulVec_smul] at hh
    rw [Matrix.mulVec_mulVec,← Matrix.mul_assoc,← Matrix.mul_assoc,hcRT,Matrix.one_mul] at hh
    simpa only [← Matrix.mulVec_mulVec] using hh
  exact hA ζ ((matrix_mem_spectrum_iff_eigenvector _ ζ).2 ⟨w,hw,hew⟩)

theorem similarity_linearResponse (A : Mat q q) (B : Mat q m) (T R : Mat q q)
    (hRT : R*T=1) (u : ℕ → Rn m) (k : ℕ) :
    linearResponse (T*A*R) (T*B) u k=act T (linearResponse A B u k) := by
  induction k with
  | zero => simp [linearResponse,rollout]
  | succ k ih =>
    change act (T*A*R) (linearResponse (T*A*R) (T*B) u k)+act (T*B) (u k)=_
    rw [ih]
    simp only [act_mul,← act_add]
    have he (z : Rn q) : act R (act T z)=z := by rw [← act_mul,hRT,act_one]
    rw [he]
    rfl

theorem similarity_nominalOutput (A : Mat q q) (B : Mat q m) (C : Mat p q)
    (T R : Mat q q) (hRT : R*T=1) (u : ℕ → Rn m) :
    nominalOutput (T*A*R) (T*B) (C*R) u=nominalOutput A B C u := by
  funext k
  simp only [nominalOutput,similarity_linearResponse A B T R hRT,act_mul]
  rw [← act_mul R T,hRT,act_one]

def balancedW (T : Mat q q) (h : r≤q) : Mat r q := fun i j => T (Fin.castLE h i) j
def balancedV (R : Mat q q) (h : r≤q) : Mat q r := fun i j => R i (Fin.castLE h j)

theorem balancedW_mul_balancedV (T R : Mat q q) (h : r≤q) (hTR : T*R=1) :
    balancedW T h*balancedV R h=1 := by
  ext i j
  change (T*R) (Fin.castLE h i) (Fin.castLE h j)=(1 : Mat r r) i j
  rw [hTR]
  simp [Matrix.one_apply]

theorem balanced_projected_A (A T R : Mat q q) (h : r≤q) :
    balancedW T h*A*balancedV R h=retainedA (T*A*R) h := rfl
theorem balanced_projected_B (B : Mat q m) (T : Mat q q) (h : r≤q) :
    balancedW T h*B=retainedB (T*B) h := rfl
theorem balanced_projected_C (C : Mat p q) (R : Mat q q) (h : r≤q) :
    C*balancedV R h=retainedC (C*R) h := rfl

end
end Populus.ModelReduction.Certified
