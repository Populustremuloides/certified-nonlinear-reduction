import Populus.Chapters.NonlinearModelReductionWithErrorBounds.CertifiedReduction.SupplyStorageMatrix

/-!
# Strict bounded-real storage constructed from the actual maximized supply

The storage is a genuine symmetric finite matrix in the paper coordinates.
A positive state cost makes it positive definite. Reserving a strict input
penalty margin makes the printed full block inequality negative definite.
-/
namespace Populus.ModelReduction.Certified
noncomputable section
variable {d b o : ℕ} {A : Mat d d} {B : Mat d b} {C : Mat o d}

namespace HilbertLinearRealization

def storageMatrix (M : HilbertLinearRealization A B C) (γ α : ℝ)
    (h : IsCoercive (supplyPenalty M.T_y M.T_z γ α)) : Mat d d :=
  standardMatrix (optimalValueBilin M.T_y M.T_z M.Q_y M.Q_z γ α h)

theorem storageMatrix_value (M : HilbertLinearRealization A B C) (γ α : ℝ)
    (h : IsCoercive (supplyPenalty M.T_y M.T_z γ α)) (x : Rn d) :
    storage (M.storageMatrix γ α h) x=
      supplyValue M.T_y M.T_z M.Q_y M.Q_z γ α x (optimalSupplyInput M.T_y M.T_z M.Q_y M.Q_z γ α h x) := by
  rw [storageMatrix,standardMatrix_storage,optimalValueBilin_eq_supply]

theorem freeState_norm_sq_lower (M : HilbertLinearRealization A B C) (x : Rn d) :
    ‖x‖^2≤‖M.Q_z x‖^2 := by
  have hp := prefixEnergy_le_energy (fun k => M.Q_z x k) (L2.finiteEnergy (M.Q_z x)) 0
  rw [← L2.norm_sq_eq_energy] at hp
  simpa [prefixEnergy,M.Q_z_apply] using hp

theorem storageMatrix_lower (M : HilbertLinearRealization A B C) (γ α : ℝ) (hα : 0≤α)
    (h : IsCoercive (supplyPenalty M.T_y M.T_z γ α)) (x : Rn d) :
    α*‖x‖^2≤storage (M.storageMatrix γ α h) x := by
  have hmax := optimalSupplyInput_maximizes M.T_y M.T_z M.Q_y M.Q_z γ α h x 0
  have hzero : ‖M.Q_y x‖^2+α*‖M.Q_z x‖^2≤storage (M.storageMatrix γ α h) x := by
    rw [M.storageMatrix_value]
    simpa [supplyValue] using hmax
  have hstate := mul_le_mul_of_nonneg_left (M.freeState_norm_sq_lower x) hα
  linarith [sq_nonneg ‖M.Q_y x‖]

theorem storageMatrix_hermitian (M : HilbertLinearRealization A B C) (γ α : ℝ)
    (h : IsCoercive (supplyPenalty M.T_y M.T_z γ α)) : (M.storageMatrix γ α h).IsHermitian :=
  standardMatrix_hermitian _ (energyBilin_symmetric _ _ _ γ α)

theorem storageMatrix_posDef (M : HilbertLinearRealization A B C) (γ α : ℝ) (hα : 0<α)
    (h : IsCoercive (supplyPenalty M.T_y M.T_z γ α)) : (M.storageMatrix γ α h).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos (M.storageMatrix_hermitian γ α h)
  intro x hx
  let z : Rn d := WithLp.toLp 2 x
  have hz : z≠0 := by
    intro heq
    apply hx
    exact congrArg (fun w : Rn d => (w : Fin d → ℝ)) heq
  have hp : 0<α*‖z‖^2 := mul_pos hα (sq_pos_of_pos (norm_pos_iff.2 hz))
  have hpositive := hp.trans_le (M.storageMatrix_lower γ α hα.le h z)
  simpa only [storage,star_trivial] using hpositive

/-- The actual matrix block in the paper is Hermitian for a symmetric storage. -/
theorem boundedRealMatrix_hermitian (A : Mat d d) (B : Mat d b) (C : Mat o d) (X : Mat d d) (g : ℝ)
    (hX : X.IsHermitian) : (boundedRealMatrix A B C X g).IsHermitian := by
  have hXT : X.transpose=X := by simpa only [Matrix.IsHermitian,Matrix.conjTranspose_eq_transpose_of_trivial] using hX
  rw [Matrix.IsHermitian,Matrix.conjTranspose_eq_transpose_of_trivial]
  simp [boundedRealMatrix,Matrix.fromBlocks_transpose,Matrix.transpose_mul,hXT,Matrix.mul_assoc]

/-- Constructed strict storage witness for every positive state cost and
strictly larger final input penalty. -/
theorem strict_storage_witness (M : HilbertLinearRealization A B C) (γ α g : ℝ)
    (hα : 0<α) (hmargin : γ^2<g^2)
    (h : IsCoercive (supplyPenalty M.T_y M.T_z γ α)) :
    (M.storageMatrix γ α h).PosDef ∧
      (-boundedRealMatrix A B C (M.storageMatrix γ α h) g).PosDef := by
  let X := M.storageMatrix γ α h
  have hX : X.PosDef := M.storageMatrix_posDef γ α hα h
  refine ⟨hX,Matrix.PosDef.of_dotProduct_mulVec_pos
    ((boundedRealMatrix_hermitian A B C X g hX.isHermitian).neg) ?_⟩
  intro v hv
  let x : Rn d := WithLp.toLp 2 (fun i => v (Sum.inl i))
  let u : Rn b := WithLp.toLp 2 (fun j => v (Sum.inr j))
  have hsplit : Sum.elim x u=v := by funext i; cases i <;> rfl
  have hne : x≠0 ∨ u≠0 := by
    by_contra hn
    have hz : x=0 ∧ u=0 := by tauto
    apply hv
    rw [← hsplit,hz.1,hz.2]
    funext i
    cases i <;> rfl
  have hpositive : 0<α*‖x‖^2+(g^2-γ^2)*‖u‖^2 := by
    rcases hne with hne|hne
    · exact add_pos_of_pos_of_nonneg (mul_pos hα (sq_pos_of_pos (norm_pos_iff.2 hne)))
        (mul_nonneg (by linarith) (sq_nonneg _))
    · exact add_pos_of_nonneg_of_pos (mul_nonneg hα.le (sq_nonneg _))
        (mul_pos (by linarith) (sq_pos_of_pos (norm_pos_iff.2 hne)))
  have hstep : storage X (act A x+act B u)+‖act C x‖^2+α*‖x‖^2≤storage X x+γ^2*‖u‖^2 := by
    rw [M.storageMatrix_value,M.storageMatrix_value]
    exact M.maximized_supply_step γ α h x u
  simp only [star_trivial,Matrix.neg_mulVec,dotProduct_neg]
  rw [← hsplit,bounded_real_quadratic_expansion]
  linarith

end HilbertLinearRealization
end
end Populus.ModelReduction.Certified
