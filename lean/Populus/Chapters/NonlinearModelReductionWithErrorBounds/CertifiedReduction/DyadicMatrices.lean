import Populus.Chapters.NonlinearModelReductionWithErrorBounds.CertifiedReduction.AnchoredReluModel
import Mathlib.LinearAlgebra.Matrix.Integer
import Mathlib.Data.ZMod.Basic

/-!
# Exact dyadic interpretation of frozen binary coefficients

The data are integer numerators over a common positive power of two.
These lemmas transport exact integer computations to the real matrices used
by the analytic theorems; no floating-point or native evaluator is trusted.
-/
namespace Populus.ModelReduction.Certified
noncomputable section
variable {n m k p d : ℕ}

def dyadicScale (e : ℕ) : ℝ := ((2 : ℝ)^e)⁻¹
def dyadicMatrix (e : ℕ) (Z : Matrix (Fin n) (Fin m) ℤ) : Mat n m :=
  dyadicScale e • Z.map (Int.castRingHom ℝ)
def dyadicVector (e : ℕ) (v : Fin n → ℤ) : Rn n :=
  WithLp.toLp 2 (fun i => dyadicScale e*(v i : ℝ))

theorem dyadicScale_pos (e : ℕ) : 0<dyadicScale e := by
  unfold dyadicScale
  positivity

theorem dyadicScale_add (e f : ℕ) : dyadicScale (e+f)=dyadicScale e*dyadicScale f := by
  simp [dyadicScale,pow_add,mul_comm]

theorem intMatrix_cast_mul (A : Matrix (Fin n) (Fin m) ℤ) (B : Matrix (Fin m) (Fin k) ℤ) :
    (A*B).map (Int.castRingHom ℝ)=A.map (Int.castRingHom ℝ)*B.map (Int.castRingHom ℝ) :=
  Matrix.map_mul

theorem dyadicMatrix_mul (e f : ℕ) (A : Matrix (Fin n) (Fin m) ℤ)
    (B : Matrix (Fin m) (Fin k) ℤ) :
    dyadicMatrix e A*dyadicMatrix f B=dyadicMatrix (e+f) (A*B) := by
  simp only [dyadicMatrix,intMatrix_cast_mul,dyadicScale_add,Matrix.smul_mul,
    Matrix.mul_smul,smul_smul]
  rw [mul_comm]

theorem dyadicMatrix_ne_zero (e : ℕ) {Z : Matrix (Fin n) (Fin m) ℤ} (hZ : Z≠0) :
    dyadicMatrix e Z≠0 := by
  intro hz
  have hcast : Z.map (Int.castRingHom ℝ)=0 :=
    (smul_eq_zero.1 hz).resolve_left (ne_of_gt (dyadicScale_pos e))
  apply hZ
  ext i j
  have hij := congrArg (fun M : Mat n m => M i j) hcast
  change (Z i j : ℝ)=0 at hij
  exact_mod_cast hij

theorem dyadic_bias_ne_zero (e : ℕ) (v : Fin n → ℤ) (hv : ∀ i, v i≠0) :
    ∀ i, dyadicVector e v i≠0 := by
  intro i
  change dyadicScale e*(v i : ℝ)≠0
  exact mul_ne_zero (ne_of_gt (dyadicScale_pos e)) (by exact_mod_cast hv i)

theorem activeDiagonal_dyadic (e : ℕ) (v : Fin n → ℤ) :
    activeDiagonal (dyadicVector e v)=dyadicMatrix 0
      (Matrix.diagonal (fun i => if 0<v i then 1 else 0)) := by
  ext i j
  simp only [activeDiagonal,dyadicMatrix,dyadicScale,pow_zero,inv_one,one_smul,
    Matrix.map_apply,Matrix.diagonal_apply]
  by_cases hij : i=j
  · subst j
    have hs : 0<dyadicVector e v i ↔ 0<v i := by
      change 0<dyadicScale e*(v i : ℝ) ↔ 0<v i
      rw [mul_pos_iff_of_pos_left (dyadicScale_pos e)]
      exact Int.cast_pos
    simp [hs]
  · simp [hij]

theorem prefixRows_dyadic (e : ℕ) (H : Matrix (Fin (p+d)) (Fin n) ℤ) :
    prefixRows (dyadicMatrix e H)=dyadicMatrix e (fun i j => H (Fin.castAdd d i) j) := rfl

theorem intMatrix_ne_zero_of_mod_entry (Z : Matrix (Fin n) (Fin m) ℤ)
    (prime : ℕ) (i : Fin n) (j : Fin m)
    (h : (Z i j : ZMod prime)≠0) : Z≠0 := by
  intro hz
  have he : Z i j=0 := congrArg (fun M => M i j) hz
  exact h (by rw [he]; simp)

end
end Populus.ModelReduction.Certified
