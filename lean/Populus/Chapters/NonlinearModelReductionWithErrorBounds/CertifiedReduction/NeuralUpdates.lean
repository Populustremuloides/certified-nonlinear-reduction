import Populus.Chapters.NonlinearModelReductionWithErrorBounds.CertifiedReduction.MatrixNormBounds
import Populus.Chapters.NonlinearModelReductionWithErrorBounds.CertifiedReduction.ResidualApproximation
import Populus.Chapters.NonlinearModelReductionWithErrorBounds.CertifiedReduction.SmoothNormalizationDensity
import Populus.Chapters.NonlinearModelReductionWithErrorBounds.CertifiedReduction.RealSchur

/-!
# Actual finite neural updates approximating a feasible reference

The injection matrices stay fixed. Density concerns the two learned factors,
and the actual full-update error follows by linear injection and a triangle
inequality. The approximation statement is proved, not supplied as a premise.
-/
namespace Populus.ModelReduction.Certified
open scoped Matrix.Norms.L2Operator
noncomputable section
variable {q m p p_u p_z : ℕ}

@[fun_prop] theorem ReLUNetwork.continuous_eval {a b : ℕ} (N : ReLUNetwork a b) : Continuous N.eval :=
  (PiLp.continuous_toLp 2 _).comp (continuous_pi (fun i => (N i).continuous_eval))

theorem continuous_Δ_z (a_θ : ReLUNetwork q p_z) : Continuous (Δ_z a_θ) :=
  continuous_norm.smul (continuous_rad.comp a_θ.continuous_eval)

theorem continuous_Δ_u (c_θ : ReLUNetwork (q+m) p_u) :
    Continuous (fun v : Rn q×Rn m => Δ_u c_θ v.1 v.2) := by
  exact continuous_snd.norm.smul (continuous_rad.comp (c_θ.continuous_eval.comp
    EuclideanSpace.finAddEquivProd.symm.continuous))

/-- Literal neural full update, using the state and applied-input envelopes. -/
def neuralUpdate (N : NominalMatrices q m p p_u p_z)
    (a_θ : ReLUNetwork q p_z) (c_θ : ReLUNetwork (q+m) p_u) : Rn q → Rn m → Rn q :=
  N.fullUpdate (Δ_z a_θ) (Δ_u c_θ)

private theorem act_sub_neural {a b : ℕ} (B : Mat a b) (x y : Rn b) :
    act B (x-y)=act B x-act B y := map_sub _ _ _

/-- Fixed injection matrices convert actual factor errors into an actual
full-update error, with no rank assumption on either injection. -/
theorem full_update_difference_bound
    (N : NominalMatrices q m p p_u p_z)
    («Δ_z¹» «Δ_z²» : Rn q → Rn p_z) («Δ_u¹» «Δ_u²» : Rn q → Rn m → Rn p_u)
    (z : Rn q) (u : Rn m) (δ : ℝ)
    (hz : ‖«Δ_z¹» z-«Δ_z²» z‖≤δ) (hu : ‖«Δ_u¹» z u-«Δ_u²» z u‖≤δ) :
    ‖N.fullUpdate «Δ_z¹» «Δ_u¹» z u-N.fullUpdate «Δ_z²» «Δ_u²» z u‖ ≤
      (‖N.B_δu‖+‖N.B_δz‖)*δ := by
  have heq : N.fullUpdate «Δ_z¹» «Δ_u¹» z u-N.fullUpdate «Δ_z²» «Δ_u²» z u=
      act N.B_δu («Δ_u¹» z u-«Δ_u²» z u)+act N.B_δz («Δ_z¹» z-«Δ_z²» z) := by
    simp only [NominalMatrices.fullUpdate,act_sub_neural]
    abel
  rw [heq]
  calc
    _ ≤ ‖act N.B_δu («Δ_u¹» z u-«Δ_u²» z u)‖+‖act N.B_δz («Δ_z¹» z-«Δ_z²» z)‖ := norm_add_le _ _
    _ ≤ ‖N.B_δu‖*‖«Δ_u¹» z u-«Δ_u²» z u‖+‖N.B_δz‖*‖«Δ_z¹» z-«Δ_z²» z‖ :=
      add_le_add (norm_act_le N.B_δu _) (norm_act_le N.B_δz _)
    _ ≤ ‖N.B_δu‖*δ+‖N.B_δz‖*δ := add_le_add
      (mul_le_mul_of_nonneg_left hu (norm_nonneg _)) (mul_le_mul_of_nonneg_left hz (norm_nonneg _))
    _ = _ := by ring

/-- Actual finite neural update approximation on the prescribed compact sets,
with the reference represented by its two continuous envelope-bounded factors. -/
theorem neural_update_uniform_approximation
    (N : NominalMatrices q m p p_u p_z)
    (K_z : Set (Rn q)) (K_u : Set (Rn m)) (hKz : IsCompact K_z) (hKu : IsCompact K_u)
    (hneZ : K_z.Nonempty) (hneU : K_u.Nonempty)
    (Δ_z_star : C(K_z,Rn p_z)) (Δ_u_star : C(K_z ×ˢ K_u,Rn p_u))
    (hz : ∀ z : K_z, ‖Δ_z_star z‖≤‖(z : Rn q)‖)
    (hu : ∀ v : K_z ×ˢ K_u, ‖Δ_u_star v‖≤‖v.1.2‖) (δ : ℝ) (hδ : 0<δ) :
    ∃ a_θ : ReLUNetwork q p_z, ∃ c_θ : ReLUNetwork (q+m) p_u,
      ∀ z : K_z, ∀ u : K_u,
      ‖neuralUpdate N a_θ c_θ z u-
        (act N.A z+act N.B_u u+act N.B_δu (Δ_u_star ⟨(z,u),⟨z.property,u.property⟩⟩)+
         act N.B_δz (Δ_z_star z))‖≤(‖N.B_δu‖+‖N.B_δz‖)*δ := by
  obtain ⟨a,c,happ⟩ := residual_approximation_at_tolerance K_z K_u hKz hKu hneZ hneU
    Δ_z_star Δ_u_star hz hu δ hδ
  letI : CompactSpace K_z := isCompact_iff_compactSpace.mp hKz
  letI : CompactSpace (K_z ×ˢ K_u) := isCompact_iff_compactSpace.mp (hKz.prod hKu)
  have hcz : Continuous (fun z : K_z => ‖Δ_z_star z-Δ_z a z‖) :=
    (Δ_z_star.continuous.sub ((continuous_Δ_z a).comp continuous_subtype_val)).norm
  have hcu : Continuous (fun v : K_z ×ˢ K_u => ‖Δ_u_star v-Δ_u c v.1.1 v.1.2‖) :=
    (Δ_u_star.continuous.sub ((continuous_Δ_u c).comp continuous_subtype_val)).norm
  have hboundz : BddAbove (Set.range (fun z : K_z => ‖Δ_z_star z-Δ_z a z‖)) :=
    (isCompact_range hcz).bddAbove
  have hboundu : BddAbove (Set.range (fun v : K_z ×ˢ K_u => ‖Δ_u_star v-Δ_u c v.1.1 v.1.2‖)) :=
    (isCompact_range hcu).bddAbove
  have hzerr (z : K_z) : ‖Δ_z a z-Δ_z_star z‖≤δ := by
    rw [norm_sub_rev]
    have hs : sSup (Set.range (fun z : K_z => ‖Δ_z_star z-Δ_z a z‖))≤δ :=
      (le_max_left _ _).trans (show residualApproximationError K_z K_u Δ_z_star Δ_u_star a c≤δ from happ.le)
    exact (le_csSup hboundz ⟨z,rfl⟩).trans hs
  have huerr (v : K_z ×ˢ K_u) : ‖Δ_u c v.1.1 v.1.2-Δ_u_star v‖≤δ := by
    rw [norm_sub_rev]
    have hs : sSup (Set.range (fun v : K_z ×ˢ K_u => ‖Δ_u_star v-Δ_u c v.1.1 v.1.2‖))≤δ :=
      (le_max_right _ _).trans (show residualApproximationError K_z K_u Δ_z_star Δ_u_star a c≤δ from happ.le)
    exact (le_csSup hboundu ⟨v,rfl⟩).trans hs
  refine ⟨a,c,fun z u => ?_⟩
  exact full_update_difference_bound N (Δ_z a) (fun _ => Δ_z_star z)
    (Δ_u c) (fun _ _ => Δ_u_star ⟨(z,u),⟨z.property,u.property⟩⟩) z u δ
      (hzerr z) (huerr ⟨(z,u),⟨z.property,u.property⟩⟩)

end
end Populus.ModelReduction.Certified
