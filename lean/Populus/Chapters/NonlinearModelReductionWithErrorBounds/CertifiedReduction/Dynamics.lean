import Populus.Chapters.NonlinearModelReductionWithErrorBounds.CertifiedReduction.MatrixStorage
import Populus.Chapters.NonlinearModelReductionWithErrorBounds.CertifiedReduction.FiniteHorizonFitting

/-!
# Literal full and projected discrete recurrences

Paper: Definitions 1--2, `eq:full`, `eq:reduced`, `eq:reduced-matrices`,
`eq:reduced-channels`. All states range over the complete ambient Euclidean
space. A reconstruction is evaluated before either nonlinear residual.
These definitions add no stability, fitting, or gain hypothesis.
-/

namespace Populus.ModelReduction.Certified
noncomputable section

@[simp] theorem act_zero {n m : ℕ} (A : Mat n m) : act A 0=0 := map_zero _

@[simp] theorem act_add {n m : ℕ} (A : Mat n m) (x y : Rn m) :
    act A (x+y)=act A x+act A y := map_add _ _ _

@[simp] theorem act_mul {n m p : ℕ} (A : Mat n m) (B : Mat m p) (x : Rn p) :
    act (A*B) x=act A (act B x) := by
  ext i
  exact congrFun (Matrix.mulVec_mulVec (x : Fin p → ℝ) A B).symm i

@[simp] theorem act_one {n : ℕ} (x : Rn n) : act (1 : Mat n n) x=x := by
  ext i
  exact congrFun (Matrix.one_mulVec (x : Fin n → ℝ)) i

/-- Matrices of the nominal LTI model and its three distinct input channels. -/
structure NominalMatrices (q m p p_u p_z : ℕ) where
  A : Mat q q
  B_u : Mat q m
  B_δu : Mat q p_u
  B_δz : Mat q p_z
  C : Mat p q

namespace NominalMatrices

variable {q m p p_u p_z r : ℕ}

def fullUpdate (N : NominalMatrices q m p p_u p_z)
    (Δ_z : Rn q → Rn p_z) (Δ_u : Rn q → Rn m → Rn p_u)
    (z : Rn q) (u : Rn m) : Rn q :=
  act N.A z+act N.B_u u+act N.B_δu (Δ_u z u)+act N.B_δz (Δ_z z)

def reduced (N : NominalMatrices q m p p_u p_z) (W_r : Mat r q) (V_r : Mat q r) :
    NominalMatrices r m p p_u p_z where
  A := W_r*N.A*V_r
  B_u := W_r*N.B_u
  B_δu := W_r*N.B_δu
  B_δz := W_r*N.B_δz
  C := N.C*V_r

def reducedUpdate (N : NominalMatrices q m p p_u p_z) (W_r : Mat r q) (V_r : Mat q r)
    (Δ_z : Rn q → Rn p_z) (Δ_u : Rn q → Rn m → Rn p_u)
    (z_hat : Rn r) (u : Rn m) : Rn r :=
  act W_r (N.fullUpdate Δ_z Δ_u (act V_r z_hat) u)

/-- The actual projected recurrence, not a separate surrogate recurrence. -/
theorem reducedUpdate_eq (N : NominalMatrices q m p p_u p_z)
    (W_r : Mat r q) (V_r : Mat q r)
    (Δ_z : Rn q → Rn p_z) (Δ_u : Rn q → Rn m → Rn p_u)
    (z_hat : Rn r) (u : Rn m) :
    N.reducedUpdate W_r V_r Δ_z Δ_u z_hat u =
      act (N.reduced W_r V_r).A z_hat+
      act (N.reduced W_r V_r).B_u u+
      act (N.reduced W_r V_r).B_δu (Δ_u (act V_r z_hat) u)+
      act (N.reduced W_r V_r).B_δz (Δ_z (act V_r z_hat)) := by
  simp [reducedUpdate,fullUpdate,reduced]

/-- Both origin equilibria follow from the magnitude envelopes, independent
of the neural weights and independently of balancing. -/
theorem origins (N : NominalMatrices q m p p_u p_z)
    (W_r : Mat r q) (V_r : Mat q r)
    (Δ_z : Rn q → Rn p_z) (Δ_u : Rn q → Rn m → Rn p_u)
    (hz : ∀ z, ‖Δ_z z‖ ≤ ‖z‖)
    (hu : ∀ z u, ‖Δ_u z u‖ ≤ ‖u‖) :
    N.fullUpdate Δ_z Δ_u 0 0=0 ∧ N.reducedUpdate W_r V_r Δ_z Δ_u 0 0=0 := by
  have hzero : Δ_z 0=0 := norm_eq_zero.mp (le_antisymm (by simpa using hz 0) (norm_nonneg _))
  have hinput (z : Rn q) : Δ_u z 0=0 :=
    norm_eq_zero.mp (le_antisymm (by simpa using hu z 0) (norm_nonneg _))
  simp [fullUpdate,reducedUpdate,hzero,hinput]

end NominalMatrices

end
end Populus.ModelReduction.Certified
