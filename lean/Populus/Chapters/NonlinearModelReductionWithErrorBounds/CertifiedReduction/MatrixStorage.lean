import Populus.Chapters.NonlinearModelReductionWithErrorBounds.CertifiedReduction.SignalEnergy
import Populus.Chapters.NonlinearModelReductionWithErrorBounds.CertifiedReduction.ReLUDensity
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Matrix.Block

/-!
# The manuscript's bounded-real block matrix and its actual channel bound

Paper: Appendix B, `eq:brl`, the sufficient direction of `lem:storage-gain`.
The block matrix is expanded here, rather than assuming a dissipation identity.
The strict bounded-real existence/converse assertion is a separate obligation.
-/

namespace Populus.ModelReduction.Certified
open scoped BigOperators
open Matrix
noncomputable section

abbrev Mat (n m : ℕ) := Matrix (Fin n) (Fin m) ℝ

/-- Euclidean matrix action, with the paper's row/column dimensions. -/
def act {n m : ℕ} (A : Mat n m) (x : Rn m) : Rn n := Matrix.toEuclideanLin A x

/-- The actual quadratic storage `zᵀ X z`. -/
def storage {n : ℕ} (X : Mat n n) (z : Rn n) : ℝ := dotProduct z (X *ᵥ z)

/-- The exact matrix in `eq:brl`; sum-index blocks represent stacked state/input. -/
def boundedRealMatrix {n m p : ℕ} (A : Mat n n) (B : Mat n m) (C : Mat p n)
    (X : Mat n n) (g : ℝ) : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℝ :=
  Matrix.fromBlocks (A.transpose * X * A-X+C.transpose*C)
    (A.transpose*X*B) (B.transpose*X*A) (B.transpose*X*B-g^2 • 1)

private theorem dot_transpose_mul {n m : ℕ} (A : Mat n m)
    (x : Fin m → ℝ) (y : Fin n → ℝ) :
    dotProduct x (A.transpose *ᵥ y) = dotProduct (A *ᵥ x) y := by
  rw [dotProduct_mulVec, vecMul_transpose]

private theorem norm_act_sq {n m : ℕ} (A : Mat n m) (x : Rn m) :
    ‖act A x‖ ^ 2 = dotProduct (A *ᵥ x) (A *ᵥ x) := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [act, Matrix.toLpLin_apply, dotProduct, pow_two]

/-- The block-matrix quadratic form is precisely the one-step storage residual. -/
theorem bounded_real_quadratic_expansion {n m p : ℕ}
    (A : Mat n n) (B : Mat n m) (C : Mat p n) (X : Mat n n) (g : ℝ)
    (z : Rn n) (u : Rn m) :
    dotProduct (Sum.elim z u) (boundedRealMatrix A B C X g *ᵥ Sum.elim z u) =
      storage X (act A z+act B u)-storage X z+‖act C z‖^2-g^2*‖u‖^2 := by
  rw [boundedRealMatrix, Matrix.fromBlocks_mulVec, sumElim_dotProduct_sumElim]
  change dotProduct z (((A.transpose*X*A-X+C.transpose*C) *ᵥ z) +
    (A.transpose*X*B) *ᵥ u) + dotProduct u (((B.transpose*X*A) *ᵥ z) +
    (B.transpose*X*B-g^2 • 1) *ᵥ u) = _
  simp only [add_mulVec, sub_mulVec, smul_mulVec, one_mulVec,
    dotProduct_add, dotProduct_sub, dotProduct_smul,
    ← Matrix.mulVec_mulVec, dot_transpose_mul, smul_eq_mul]
  change _ = dotProduct (A *ᵥ z+B *ᵥ u) (X *ᵥ (A *ᵥ z+B *ᵥ u)) -
    dotProduct z (X *ᵥ z)+‖act C z‖^2-g^2*‖u‖^2
  rw [mulVec_add,add_dotProduct,dotProduct_add,dotProduct_add,norm_act_sq]
  have hu : ‖u‖^2 = dotProduct u u := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [dotProduct,pow_two]
  rw [hu]
  ring

/-- Negative semidefiniteness of the printed block yields one-step dissipation. -/
theorem bounded_real_one_step {n m p : ℕ}
    (A : Mat n n) (B : Mat n m) (C : Mat p n) (X : Mat n n) (g : ℝ)
    (hQ : (-boundedRealMatrix A B C X g).PosSemidef)
    (z : Rn n) (u : Rn m) :
    storage X (act A z+act B u)+‖act C z‖^2 ≤ storage X z+g^2*‖u‖^2 := by
  have h := hQ.dotProduct_mulVec_nonneg (Sum.elim z u)
  simp only [star_trivial,neg_mulVec,dotProduct_neg] at h
  rw [bounded_real_quadratic_expansion] at h
  linarith

/-- The sufficient half of the paper's matrix-gain lemma, for actual discrete
trajectories and the paper's inclusive finite-prefix convention. -/
theorem matrix_storage_prefix_bound {n m p : ℕ}
    (A : Mat n n) (B : Mat n m) (C : Mat p n) (X : Mat n n) (g : ℝ)
    (hX : X.PosDef) (hQ : (-boundedRealMatrix A B C X g).PosSemidef)
    (z : ℕ → Rn n) (u : ℕ → Rn m) (hz₀ : z 0=0)
    (hz : ∀ k, z (k+1)=act A (z k)+act B (u k)) :
    ∀ K, prefixEnergy (fun k => act C (z k)) K ≤ g^2*prefixEnergy u K := by
  have hnonneg (x : Rn n) : 0 ≤ storage X x := by
    simpa [storage] using hX.posSemidef.dotProduct_mulVec_nonneg (x : Fin n → ℝ)
  have ht (N : ℕ) : storage X (z N)+
      (∑ k ∈ Finset.range N, ‖act C (z k)‖^2) ≤
      storage X (z 0)+g^2*(∑ k ∈ Finset.range N, ‖u k‖^2) := by
    induction N with
    | zero => simp
    | succ N ih =>
      have hstep := bounded_real_one_step A B C X g hQ (z N) (u N)
      rw [← hz N] at hstep
      rw [Finset.sum_range_succ,Finset.sum_range_succ]
      nlinarith
  intro K
  have h := ht (K+1)
  have h0 : storage X (z 0)=0 := by simp [hz₀,storage]
  rw [h0] at h
  dsimp [prefixEnergy]
  linarith [hnonneg (z (K+1))]

/-- Finite-energy membership and the actual infinite channel-gain inequality
follow after the matrix/prefix proof, without assuming the output is in ℓ₂. -/
theorem matrix_storage_infinite_gain {n m p : ℕ}
    (A : Mat n n) (B : Mat n m) (C : Mat p n) (X : Mat n n) (g : ℝ)
    (hg : 0 ≤ g) (hX : X.PosDef) (hQ : (-boundedRealMatrix A B C X g).PosSemidef)
    (z : ℕ → Rn n) (u : ℕ → Rn m) (hu : FiniteEnergy u) (hz₀ : z 0=0)
    (hz : ∀ k, z (k+1)=act A (z k)+act B (u k)) :
    FiniteEnergy (fun k => act C (z k)) ∧
      Real.sqrt (energy (fun k => act C (z k))) ≤ g*Real.sqrt (energy u) := by
  have hp := matrix_storage_prefix_bound A B C X g hX hQ z u hz₀ hz
  have hC : 0 ≤ g^2*energy u := mul_nonneg (sq_nonneg _) (tsum_nonneg (fun k => sq_nonneg _))
  have hb (K : ℕ) : prefixEnergy (fun k => act C (z k)) K ≤ g^2*energy u :=
    (hp K).trans (mul_le_mul_of_nonneg_left (prefixEnergy_le_energy u hu K) (sq_nonneg g))
  refine ⟨finiteEnergy_of_prefix_bound _ _ hC hb,?_⟩
  have hs := Real.sqrt_le_sqrt (energy_le_of_prefix_bound _ _ hC hb)
  simpa [Real.sqrt_mul (sq_nonneg g),Real.sqrt_sq hg] using hs

end
end Populus.ModelReduction.Certified
