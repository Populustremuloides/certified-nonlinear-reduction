import Populus.Chapters.NonlinearModelReductionWithErrorBounds.CertifiedReduction.ResidualApproximation
import Populus.Chapters.NonlinearModelReductionWithErrorBounds.CertifiedReduction.Dynamics
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Data.Real.StarOrdered
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Physical reconstruction and origin-preserving neural lifting

Paper: `eq:lifting`, Appendix A.1 and initialization in `thm:main`. The actual
right inverse is C_x^T (C_x C_x^T)^(-1), not an assumed surrogate. Its existence
is derived from the reference's global physical reconstruction identity.
-/
namespace Populus.ModelReduction.Certified
open scoped Matrix.Norms.L2Operator
noncomputable section
variable {n q : ℕ}

def C_x_dagger (C_x : Mat n q) : Mat q n := C_x.transpose*(C_x*C_x.transpose)⁻¹
def R_x (C_x : Mat n q) : Mat q q := 1-C_x_dagger C_x*C_x

private theorem act_sub_vec (A : Mat n q) (x y : Rn q) : act A (x-y)=act A x-act A y := map_sub _ _ _
private theorem act_sub_matrix (A B : Mat n q) (x : Rn q) : act (A-B) x=act A x-act B x := by
  ext i
  simp [act,Matrix.toEuclideanLin,Matrix.sub_mulVec]

/-- Global physical reconstruction implies full row rank and hence a genuine
positive-definite row Gram matrix; no full-column-rank readout is required. -/
theorem reconstruction_row_gram_posDef
    (C_x : Mat n q) (Φ : Rn n → Rn q) (h : ∀ x, act C_x (Φ x)=x) :
    (C_x*C_x.transpose).PosDef := by
  have hsurj : Function.Surjective C_x.mulVec := by
    intro x
    refine ⟨(Φ (WithLp.toLp 2 x) : Fin q → ℝ),?_⟩
    have heq := h (WithLp.toLp 2 x)
    exact congrArg (fun z : Rn n => (z : Fin n → ℝ)) heq
  obtain ⟨D,hD⟩ := Matrix.mulVec_surjective_iff_exists_right_inverse.1 hsurj
  have hvec : Function.Injective C_x.vecMul := by
    intro x y hxy
    have heq := congrArg (fun z => Matrix.vecMul z D) hxy
    simpa only [Matrix.vecMul_vecMul,hD,Matrix.vecMul_one] using heq
  simpa only [Matrix.conjTranspose,star_trivial,Matrix.map_id] using
    Matrix.PosDef.mul_conjTranspose_self C_x hvec

/-- The exact pseudoinverse formula used in the manuscript is a right inverse. -/
theorem C_x_mul_dagger
    (C_x : Mat n q) (Φ : Rn n → Rn q) (h : ∀ x, act C_x (Φ x)=x) :
    C_x*C_x_dagger C_x=1 := by
  have hp := reconstruction_row_gram_posDef C_x Φ h
  have hunit : IsUnit (C_x*C_x.transpose).det := isUnit_iff_ne_zero.2 (ne_of_gt hp.det_pos)
  dsimp [C_x_dagger]
  rw [← Matrix.mul_assoc,Matrix.mul_nonsing_inv _ hunit]

/-- Actual finite lifting from `eq:lifting`. -/
def Φ_θ (C_x : Mat n q) (ψ_θ : ReLUNetwork n q) (x : Rn n) : Rn q :=
  act (C_x_dagger C_x) x+act (R_x C_x) (ψ_θ.eval x-ψ_θ.eval 0)

/-- Both required global identities hold for every network and every state. -/
theorem neural_lifting_identities
    (C_x : Mat n q) (Φ : Rn n → Rn q) (h : ∀ x, act C_x (Φ x)=x)
    (ψ_θ : ReLUNetwork n q) :
    (∀ x, act C_x (Φ_θ C_x ψ_θ x)=x) ∧ Φ_θ C_x ψ_θ 0=0 := by
  have hdag := C_x_mul_dagger C_x Φ h
  have hR : C_x*R_x C_x=0 := by
    dsimp [R_x]
    rw [Matrix.mul_sub,Matrix.mul_one,← Matrix.mul_assoc,hdag,Matrix.one_mul,sub_self]
  constructor
  · intro x
    simp only [Φ_θ,act_add,← act_mul,hdag,act_one,hR]
    have hz : act (0 : Mat n q) (ψ_θ.eval x-ψ_θ.eval 0)=0 := by
      ext i; simp [act,Matrix.toEuclideanLin]
    rw [hz,add_zero]
  · simp [Φ_θ]

/-- The learned lifting error is the projected, centered coefficient error. -/
theorem neural_lifting_error
    (C_x : Mat n q) (Φ : Rn n → Rn q) (h : ∀ x, act C_x (Φ x)=x) (hΦ0 : Φ 0=0)
    (ψ_θ : ReLUNetwork n q) (x : Rn n) :
    Φ_θ C_x ψ_θ x-Φ x=
      act (R_x C_x) ((ψ_θ.eval x-Φ x)-(ψ_θ.eval 0-Φ 0)) := by
  have href : act (C_x_dagger C_x) x+act (R_x C_x) (Φ x)=Φ x := by
    simp only [R_x,act_sub_matrix,act_one,act_mul,h]
    abel
  have hlinear : act (R_x C_x) ((ψ_θ.eval x-Φ x)-(ψ_θ.eval 0-Φ 0))=
      (act (R_x C_x) (ψ_θ.eval x)-act (R_x C_x) (Φ x))-
      (act (R_x C_x) (ψ_θ.eval 0)-act (R_x C_x) (Φ 0)) := by simp only [act_sub_vec]
  rw [hlinear,hΦ0,act_zero]
  calc
    _ = Φ_θ C_x ψ_θ x-(act (C_x_dagger C_x) x+act (R_x C_x) (Φ x)) :=
      congrArg (fun t => Φ_θ C_x ψ_θ x-t) href.symm
    _ = _ := by simp only [Φ_θ,act_sub_vec]; abel

/-- Finite neural liftings uniformly approximate a feasible reference while
preserving physical reconstruction and the origin on the entire state space.
The compact approximation set contains the origin because the network is
centered there in the exact formula from the manuscript. -/
theorem neural_lifting_uniform_approximation
    (C_x : Mat n q) (Φ : Rn n → Rn q) (hΦ : Continuous Φ)
    (hreconstruct : ∀ x, act C_x (Φ x)=x) (hΦ0 : Φ 0=0)
    (X : Set (Rn n)) (hX : IsCompact X) (h0 : (0 : Rn n)∈X)
    (ε : ℝ) (hε : 0<ε) :
    ∃ ψ_θ : ReLUNetwork n q,
      (∀ x, act C_x (Φ_θ C_x ψ_θ x)=x) ∧ Φ_θ C_x ψ_θ 0=0 ∧
      sSup (Set.range (fun x : X => ‖Φ_θ C_x ψ_θ x-Φ x‖))<ε := by
  let R := R_x C_x
  let δ : ℝ := ε/(2*(1+‖R‖))
  have hδ : 0<δ := by dsimp [δ]; positivity
  let Φ_X : C(X,Rn q) := ⟨fun x => Φ x,hΦ.comp continuous_subtype_val⟩
  obtain ⟨ψ,hψ⟩ := uniform_vector_relu_approximation_on_compact X hX Φ_X δ hδ
  have hbound (x : X) : ‖Φ_θ C_x ψ x-Φ x‖≤2*‖R‖*δ := by
    rw [neural_lifting_error C_x Φ hreconstruct hΦ0 ψ x]
    calc
      _ ≤ ‖R‖*‖(ψ.eval x-Φ x)-(ψ.eval 0-Φ 0)‖ := Matrix.l2_opNorm_mulVec R _
      _ ≤ ‖R‖*(‖ψ.eval x-Φ x‖+‖ψ.eval 0-Φ 0‖) :=
        mul_le_mul_of_nonneg_left (norm_sub_le _ _) (norm_nonneg _)
      _ ≤ ‖R‖*(δ+δ) := mul_le_mul_of_nonneg_left
        (add_le_add (hψ x).le (hψ ⟨0,h0⟩).le) (norm_nonneg _)
      _ = _ := by ring
  have hδeq : δ*(2*(1+‖R‖))=ε := div_mul_cancel₀ _ (by positivity : 2*(1+‖R‖)≠0)
  have hfinal : 2*‖R‖*δ<ε := by nlinarith [norm_nonneg R]
  have hi := neural_lifting_identities C_x Φ hreconstruct ψ
  letI : Nonempty X := ⟨⟨0,h0⟩⟩
  refine ⟨ψ,hi.1,hi.2,lt_of_le_of_lt ?_ hfinal⟩
  apply csSup_le (Set.range_nonempty _)
  rintro y ⟨x,rfl⟩
  exact hbound x

end
end Populus.ModelReduction.Certified
