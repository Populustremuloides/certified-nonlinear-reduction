import Populus.Chapters.NonlinearModelReductionWithErrorBounds.CertifiedReduction.HilbertChannels
import Populus.Chapters.NonlinearModelReductionWithErrorBounds.CertifiedReduction.MatrixNormBounds

namespace Populus.ModelReduction.Certified
open scoped ENNReal Matrix.Norms.L2Operator
noncomputable section
variable {d o : ℕ}

def HasFreePrefixBound (A : Mat d d) (O : Mat o d) (c : ℝ) : Prop :=
  0≤c ∧ ∀ x K, prefixNorm (fun k => act O (freeResponse A x k)) K≤c*‖x‖

theorem finiteEnergy_of_uniform_prefix_bound {E : Type*} [NormedAddCommGroup E]
    (z : ℕ → E) (C : ℝ) (hC : 0≤C) (h : ∀ K, prefixNorm z K≤C) : FiniteEnergy z := by
  apply (finiteEnergy_iff_ℓ₂_ne_top z).2
  have hle : ℓ₂ z≤ENNReal.ofReal C := iSup_le (fun K => ENNReal.ofReal_le_ofReal (h K))
  exact ne_of_lt (hle.trans_lt ENNReal.ofReal_lt_top)

theorem free_l2_membership (A : Mat d d) (O : Mat o d) (c : ℝ)
    (h : HasFreePrefixBound A O c) (x : Rn d) :
    FiniteEnergy (fun k => act O (freeResponse A x k)) :=
  finiteEnergy_of_uniform_prefix_bound _ (c*‖x‖) (mul_nonneg h.1 (norm_nonneg x)) (h.2 x)

def freeLinear (A : Mat d d) (O : Mat o d) (c : ℝ) (h : HasFreePrefixBound A O c) :
    Rn d →ₗ[ℝ] L2 (Rn o) where
  toFun x := toL2 (fun k => act O (freeResponse A x k)) (free_l2_membership A O c h x)
  map_add' x y := by
    apply lp.ext
    funext k
    change act O (freeResponse A (x+y) k)=act O (freeResponse A x k)+act O (freeResponse A y k)
    simp [freeResponse,act_add]
  map_smul' t x := by
    apply lp.ext
    funext k
    change act O (freeResponse A (t • x) k)=t • act O (freeResponse A x k)
    simp [freeResponse,act_smul]

theorem freeLinear_norm_bound (A : Mat d d) (O : Mat o d) (c : ℝ)
    (h : HasFreePrefixBound A O c) (x : Rn d) : ‖freeLinear A O c h x‖≤c*‖x‖ := by
  have hle : ℓ₂ (fun k => act O (freeResponse A x k))≤ENNReal.ofReal (c*‖x‖) :=
    iSup_le (fun K => ENNReal.ofReal_le_ofReal (h.2 x K))
  have heq : ℓ₂ (fun k => act O (freeResponse A x k))=ENNReal.ofReal ‖freeLinear A O c h x‖ :=
    L2.ℓ₂_eq_norm (freeLinear A O c h x)
  rw [heq] at hle
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg h.1 (norm_nonneg x))).1 hle

def freeOperator (A : Mat d d) (O : Mat o d) (c : ℝ) (h : HasFreePrefixBound A O c) :
    Rn d →L[ℝ] L2 (Rn o) := (freeLinear A O c h).mkContinuous c (freeLinear_norm_bound A O c h)

@[simp] theorem freeOperator_apply (A : Mat d d) (O : Mat o d) (c : ℝ)
    (h : HasFreePrefixBound A O c) (x : Rn d) (k : ℕ) :
    freeOperator A O c h x k=act O (freeResponse A x k) := rfl

theorem schur_free_prefix_bounds [NeZero d] (A : Mat d d) (C : Mat o d) (hA : Schur A) :
    ∃ c : ℝ, 1≤c ∧ HasFreePrefixBound A (1 : Mat d d) c ∧
      HasFreePrefixBound A C (‖C‖*c) := by
  obtain ⟨c,hc,hfree⟩ := schur_free_response_bound A hA
  refine ⟨c,hc,⟨by linarith,?_⟩,⟨mul_nonneg (norm_nonneg _) (by linarith),?_⟩⟩
  · intro x K
    simpa only [act_one] using hfree x K
  · intro x K
    calc
      _ ≤ ‖C‖*prefixNorm (freeResponse A x) K :=
        prefixNorm_mul_bound _ _ ‖C‖ (norm_nonneg _) (fun k => norm_act_le C _) K
      _ ≤ ‖C‖*(c*‖x‖) := mul_le_mul_of_nonneg_left (hfree x K) (norm_nonneg _)
      _ = _ := by ring

end
end Populus.ModelReduction.Certified
