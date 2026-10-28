import Populus.Chapters.NonlinearModelReductionWithErrorBounds.CertifiedReduction.SchurDecay
import Populus.Chapters.NonlinearModelReductionWithErrorBounds.CertifiedReduction.Dynamics
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# The real-matrix Schur hypothesis and finite free-response energy

Paper: Definition of Schur stability and Appendix C.3's free-response estimate.
`Schur A` quantifies over the complex spectrum of the actual real matrix.
The Euclidean action is compared to its complexification without imposing
`‖A‖ < 1`. This is stronger analytically than a small one-step norm hypothesis.
-/
namespace Populus.ModelReduction.Certified
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section

/-- The complexification of the actual real nominal matrix. -/
def complexify {n : ℕ} (A : Mat n n) : Matrix (Fin n) (Fin n) ℂ := A.map Complex.ofReal

/-- Paper Schur stability: every complex spectral value is strictly inside
its unit disk. In finite dimension these are precisely matrix eigenvalues. -/
def Schur {n : ℕ} (A : Mat n n) : Prop :=
  ∀ ζ ∈ spectrum ℂ (complexify A), ‖ζ‖ < 1

def complexVector {n : ℕ} (z : Rn n) : EuclideanSpace ℂ (Fin n) :=
  WithLp.toLp 2 (fun i => (z i : ℂ))

@[simp] theorem norm_complexVector {n : ℕ} (z : Rn n) : ‖complexVector z‖=‖z‖ := by
  have hs : ‖complexVector z‖^2=‖z‖^2 := by
    rw [EuclideanSpace.norm_sq_eq,EuclideanSpace.real_norm_sq_eq]
    simp [complexVector,Complex.norm_real,sq_abs]
  nlinarith [norm_nonneg (complexVector z),norm_nonneg z]

theorem complexVector_act {n : ℕ} (A : Mat n n) (z : Rn n) :
    complexVector (act A z)=Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) (complexify A) (complexVector z) := by
  ext i
  exact RingHom.map_mulVec Complex.ofRealHom A (z : Fin n → ℝ) i

@[simp] theorem complexify_pow {n : ℕ} (A : Mat n n) (k : ℕ) :
    complexify (A^k)=(complexify A)^k := Matrix.map_pow A Complex.ofRealHom k

/-- Strict spectral radius follows from the paper's eigenvalue condition,
using compactness/nonemptiness of the complex Banach-algebra spectrum. -/
theorem spectralRadius_complexify_lt_one {n : ℕ} [NeZero n]
    (A : Mat n n) (hA : Schur A) : spectralRadius ℂ (complexify A)<1 := by
  apply spectrum.spectralRadius_lt_of_forall_lt
  intro ζ hζ
  exact_mod_cast hA ζ hζ

/-- A real orbit is bounded by the genuine complex Euclidean operator norm. -/
theorem norm_act_pow_le {n : ℕ} (A : Mat n n) (z : Rn n) (k : ℕ) :
    ‖act (A^k) z‖ ≤ ‖(complexify A)^k‖*‖z‖ := by
  rw [← norm_complexVector (act (A^k) z),complexVector_act,complexify_pow]
  have h := (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) ((complexify A)^k)).le_opNorm (complexVector z)
  simpa only [Matrix.l2_opNorm_toEuclideanCLM,norm_complexVector] using h

/-- The actual free response of the nominal state dynamics. -/
def freeResponse {n : ℕ} (A : Mat n n) (z₀ : Rn n) (k : ℕ) : Rn n := act (A^k) z₀

/-- Appendix C.3: Schur stability supplies a uniform finite free-response
constant on every finite prefix and hence on the infinite trajectory. -/
theorem schur_free_response_bound {n : ℕ} [NeZero n]
    (A : Mat n n) (hA : Schur A) :
    ∃ c : ℝ, 1 ≤ c ∧ ∀ z₀ K, prefixNorm (freeResponse A z₀) K ≤ c*‖z₀‖ := by
  have hsum := summable_norm_pow_sq_of_spectralRadius_lt_one (complexify A)
    (spectralRadius_complexify_lt_one A hA)
  let S : ℝ := ∑' k : ℕ, ‖(complexify A)^k‖^2
  have hS : 0 ≤ S := tsum_nonneg (fun k => sq_nonneg _)
  let c : ℝ := Real.sqrt (S+1)
  have hc : 1 ≤ c := by
    have hs := Real.sq_sqrt (by linarith : 0 ≤ S+1)
    have hn := Real.sqrt_nonneg (S+1)
    dsimp [c]
    nlinarith
  refine ⟨c,hc,?_⟩
  intro z₀ K
  have hprefix : prefixEnergy (freeResponse A z₀) K ≤ S*‖z₀‖^2 := by
    calc
      _ ≤ ∑ k ∈ Finset.range (K+1), ‖(complexify A)^k‖^2*‖z₀‖^2 := by
        apply Finset.sum_le_sum
        intro k _
        have hp := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg z₀))).2
          (norm_act_pow_le A z₀ k)
        simpa [freeResponse,mul_pow] using hp
      _ = (∑ k ∈ Finset.range (K+1), ‖(complexify A)^k‖^2)*‖z₀‖^2 :=
        (Finset.sum_mul _ _ _).symm
      _ ≤ S*‖z₀‖^2 := mul_le_mul_of_nonneg_right
        (Summable.sum_le_tsum (Finset.range (K+1)) (fun k _ => sq_nonneg _) hsum) (sq_nonneg _)
  have hbound : prefixEnergy (freeResponse A z₀) K ≤ (S+1)*‖z₀‖^2 :=
    hprefix.trans (mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _))
  have hs := Real.sqrt_le_sqrt hbound
  simpa [prefixNorm,c,Real.sqrt_mul (by linarith : 0 ≤ S+1),Real.sqrt_sq (norm_nonneg z₀)] using hs

end
end Populus.ModelReduction.Certified
