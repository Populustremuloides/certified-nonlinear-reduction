import Populus.Chapters.NonlinearModelReductionWithErrorBounds.CertifiedReduction.SmoothNormalizationDensity
import Populus.Chapters.NonlinearModelReductionWithErrorBounds.CertifiedReduction.VectorBlocks
import Populus.Chapters.NonlinearModelReductionWithErrorBounds.CertifiedReduction.MatrixNormBounds
import Populus.Chapters.NonlinearModelReductionWithErrorBounds.CertifiedReduction.LinearResponseAlgebra
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.FDeriv.Congr

/-!
# The exact anchored coefficient architecture in the frozen-example proof

The complete coefficient vector is normalized before its first block is taken.
This retains the full denominator from the deployed sixteen-output network.
The local activation-pattern argument below derives the actual coefficient
Jacobian, rather than assuming differentiability of ReLU at its kink.
-/
namespace Populus.ModelReduction.Certified
open Filter
open scoped Topology
noncomputable section
variable {q h p d : ℕ}

def matCLM {n m : ℕ} (A : Mat n m) : Rn m →L[ℝ] Rn n :=
  ⟨Matrix.toEuclideanLin A,(Matrix.toEuclideanLin A).continuous_of_finiteDimensional⟩
@[simp] theorem matCLM_apply {n m : ℕ} (A : Mat n m) (z : Rn m) : matCLM A z=act A z := rfl

def reluVec (z : Rn h) : Rn h := WithLp.toLp 2 (fun i => max (z i) 0)
def activeDiagonal (b : Rn h) : Mat h h := Matrix.diagonal (fun i => if 0<b i then 1 else 0)
def prefixRows (H : Mat (p+d) h) : Mat p h := fun i j => H (Fin.castAdd d i) j

@[simp] theorem take_act (H : Mat (p+d) h) (z : Rn h) : take (act H z)=act (prefixRows H) z := by
  ext i
  rfl

structure AnchoredReluModel (q h p d : ℕ) where
  A : Mat q q
  L : Mat h q
  b : Rn h
  H : Mat (p+d) h
  K : Mat q p

namespace AnchoredReluModel

def h_f (M : AnchoredReluModel q h p d) (z : Rn q) : Rn (p+d) :=
  act M.H (reluVec (act M.L z+M.b)-reluVec M.b)
def D_f (M : AnchoredReluModel q h p d) : Mat h h := activeDiagonal M.b
def M_f (M : AnchoredReluModel q h p d) : Mat q q := (2 : ℝ) • (M.K*prefixRows M.H*M.D_f*M.L)
def δ_f (M : AnchoredReluModel q h p d) (z : Rn q) : Rn p := ‖z‖ • take (ν (M.h_f z))
def f_f (M : AnchoredReluModel q h p d) (z : Rn q) : Rn q := act M.A z+(2 : ℝ) • act M.K (M.δ_f z)

/-- The magnitude envelope is global, despite the eventual unbounded Jacobian. -/
theorem δ_f_envelope (M : AnchoredReluModel q h p d) (z : Rn q) : ‖M.δ_f z‖≤‖z‖ := by
  rw [δ_f,norm_smul,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)]
  have h := (norm_take_le (ν (M.h_f z))).trans (norm_ν_lt_one _).le
  exact (mul_le_mul_of_nonneg_left h (norm_nonneg _)).trans (by simp)

theorem h_f_zero_on_kernel (M : AnchoredReluModel q h p d) (x : Rn q) (hx : act M.L x=0) :
    M.h_f x=0 := by simp [h_f,hx]

/-- With nonzero biases the activation pattern is locally fixed at every
kernel state, so the anchored network is locally exactly its active linear map. -/
theorem h_f_locally_linear (M : AnchoredReluModel q h p d)
    (hb : ∀ i, M.b i≠0) (x : Rn q) (hx : act M.L x=0) :
    M.h_f =ᶠ[𝓝 x] (fun z => act (M.H*M.D_f*M.L) z) := by
  have hcoord (i : Fin h) : ∀ᶠ z in 𝓝 x,
      max ((act M.L z+M.b) i) 0-max (M.b i) 0=
        (if 0<M.b i then (act M.L z) i else 0) := by
    have hc : ContinuousAt (fun z : Rn q => (act M.L z+M.b) i) x :=
      ((EuclideanSpace.proj i).continuous.comp ((matCLM M.L).continuous.add continuous_const)).continuousAt
    have hvalue : (act M.L x+M.b) i=M.b i := by rw [hx]; simp
    by_cases hpos : 0<M.b i
    · have he : ∀ᶠ z in 𝓝 x, 0<(act M.L z+M.b) i :=
        (tendsto_order.1 hc.tendsto).1 0 (by rw [hvalue]; exact hpos)
      filter_upwards [he] with z hz
      simp only [max_eq_left hz.le,max_eq_left hpos.le,if_pos hpos]
      simp
    · have hneg : M.b i<0 := lt_of_le_of_ne (le_of_not_gt hpos) (hb i)
      have he : ∀ᶠ z in 𝓝 x, (act M.L z+M.b) i<0 :=
        (tendsto_order.1 hc.tendsto).2 0 (by rw [hvalue]; exact hneg)
      filter_upwards [he] with z hz
      change (act M.L z) i+M.b i<0 at hz
      simp [max_eq_right hz.le,max_eq_right hneg.le,hpos]
  filter_upwards [eventually_all.2 hcoord] with z hz
  have hrelu : reluVec (act M.L z+M.b)-reluVec M.b=act M.D_f (act M.L z) := by
    ext i
    simpa [reluVec,D_f,activeDiagonal,act,Matrix.toEuclideanLin,Matrix.mulVec_diagonal] using hz i
  rw [h_f,hrelu,act_mul,act_mul]

theorem h_f_hasFDerivAt_on_kernel (M : AnchoredReluModel q h p d)
    (hb : ∀ i, M.b i≠0) (x : Rn q) (hx : act M.L x=0) :
    HasFDerivAt M.h_f (matCLM (M.H*M.D_f*M.L)) x :=
  (matCLM (M.H*M.D_f*M.L)).hasFDerivAt.congr_of_eventuallyEq (M.h_f_locally_linear hb x hx)

end AnchoredReluModel
end
end Populus.ModelReduction.Certified
