import Populus.Chapters.NonlinearModelReductionWithErrorBounds.CertifiedReduction.EnvelopeApproximation

/-!
# The two prescribed-envelope residuals

Paper: `eq:neural`, `prop:density` (Appendix A).
Input coordinates `(z,u)` are packed by the canonical linear homeomorphism
`ℝ^(q+m) ≃ ℝ^q × ℝ^m`. This packs network arguments only. The driving norm
in `Δ_u` remains the norm of the applied input `u`, never of the packed pair.
-/

namespace Populus.ModelReduction.Certified
noncomputable section

instance {n : ℕ} : Inhabited (ReLUExpr n) := ⟨.const 0⟩

def pack {q m : ℕ} (z : Rn q) (u : Rn m) : Rn (q+m) :=
  (EuclideanSpace.finAddEquivProd (𝕜 := ℝ)).symm (z,u)

def Δ_z {q p_z : ℕ} (aθ : ReLUNetwork q p_z) (z : Rn q) : Rn p_z :=
  ‖z‖ • rad (aθ.eval z)

def Δ_u {q m p_u : ℕ} (cθ : ReLUNetwork (q+m) p_u) (z : Rn q) (u : Rn m) : Rn p_u :=
  ‖u‖ • rad (cθ.eval (pack z u))

theorem norm_Δ_z_le {q p_z : ℕ} (aθ : ReLUNetwork q p_z) (z : Rn q) :
    ‖Δ_z aθ z‖ ≤ ‖z‖ := by
  simpa [Δ_z, norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg z)] using
    mul_le_mul_of_nonneg_left
      (Populus.PaperEvidence.ModelReduction.norm_rad_le_one (aθ.eval z)) (norm_nonneg z)

theorem norm_Δ_u_le {q m p_u : ℕ} (cθ : ReLUNetwork (q+m) p_u) (z : Rn q) (u : Rn m) :
    ‖Δ_u cθ z u‖ ≤ ‖u‖ := by
  simpa [Δ_u, norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg u)] using
    mul_le_mul_of_nonneg_left
      (Populus.PaperEvidence.ModelReduction.norm_rad_le_one (cθ.eval (pack z u))) (norm_nonneg u)

/-- The maximum of the two uniform errors displayed in `prop:density`. -/
def residualApproximationError {q m p_z p_u : ℕ}
    (K_z : Set (Rn q)) (K_u : Set (Rn m))
    (Δ_z_star : C(K_z, Rn p_z)) (Δ_u_star : C(K_z ×ˢ K_u, Rn p_u))
    (aθ : ReLUNetwork q p_z) (cθ : ReLUNetwork (q+m) p_u) : ℝ :=
  max (sSup (Set.range (fun z : K_z => ‖Δ_z_star z - Δ_z aθ z‖)))
      (sSup (Set.range (fun v : K_z ×ˢ K_u => ‖Δ_u_star v - Δ_u cθ v.1.1 v.1.2‖)))

theorem residualApproximationError_nonneg {q m p_z p_u : ℕ}
    (K_z : Set (Rn q)) (K_u : Set (Rn m))
    (Δ_z_star : C(K_z, Rn p_z)) (Δ_u_star : C(K_z ×ˢ K_u, Rn p_u))
    (aθ : ReLUNetwork q p_z) (cθ : ReLUNetwork (q+m) p_u) :
    0 ≤ residualApproximationError K_z K_u Δ_z_star Δ_u_star aθ cθ := by
  apply le_trans _ (le_max_left _ _)
  apply Real.sSup_nonneg
  rintro y ⟨z,rfl⟩
  exact norm_nonneg _

/-- Arbitrary positive tolerance, before taking the infimum over the family. -/
theorem residual_approximation_at_tolerance {q m p_z p_u : ℕ}
    (K_z : Set (Rn q)) (K_u : Set (Rn m))
    (hKz : IsCompact K_z) (hKu : IsCompact K_u)
    (hneZ : K_z.Nonempty) (hneU : K_u.Nonempty)
    (Δ_z_star : C(K_z, Rn p_z)) (Δ_u_star : C(K_z ×ˢ K_u, Rn p_u))
    (hz : ∀ z : K_z, ‖Δ_z_star z‖ ≤ ‖(z : Rn q)‖)
    (hu : ∀ v : K_z ×ˢ K_u, ‖Δ_u_star v‖ ≤ ‖v.1.2‖)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ aθ : ReLUNetwork q p_z, ∃ cθ : ReLUNetwork (q+m) p_u,
      residualApproximationError K_z K_u Δ_z_star Δ_u_star aθ cθ < ε := by
  obtain ⟨aθ, ha, _⟩ := fixed_envelope_pointwise_approximation
    K_z hKz hneZ (fun z => ‖z‖) continuous_norm (fun z => norm_nonneg z)
    Δ_z_star hz (ε/2) (half_pos hε)
  let T : Rn (q+m) ≃L[ℝ] (Rn q × Rn m) := EuclideanSpace.finAddEquivProd
  let K : Set (Rn (q+m)) := T.symm '' (K_z ×ˢ K_u)
  have hK : IsCompact K := (hKz.prod hKu).image T.symm.continuous
  have hne : K.Nonempty := (hneZ.prod hneU).image T.symm
  let pair : K → (K_z ×ˢ K_u) := fun v =>
    ⟨T v, by
      obtain ⟨w, hw, hv⟩ := v.property
      simpa [← hv] using hw⟩
  have hpair : Continuous pair :=
    (T.continuous.comp continuous_subtype_val).subtype_mk _
  let e : C(K, Rn p_u) := Δ_u_star.comp ⟨pair,hpair⟩
  let ρ : Rn (q+m) → ℝ := fun v => ‖(T v).2‖
  have hρ : Continuous ρ := (continuous_snd.comp T.continuous).norm
  have he : ∀ v : K, ‖e v‖ ≤ ρ v := by
    intro v
    exact hu (pair v)
  obtain ⟨cθ, hc, _⟩ := fixed_envelope_pointwise_approximation
    K hK hne ρ hρ (fun v => norm_nonneg _) e he (ε/2) (half_pos hε)
  letI : Nonempty K_z := hneZ.to_subtype
  letI : Nonempty (K_z ×ˢ K_u) := (hneZ.prod hneU).to_subtype
  have haSup : sSup (Set.range (fun z : K_z => ‖Δ_z_star z - Δ_z aθ z‖)) ≤ ε/2 := by
    apply csSup_le (Set.range_nonempty _)
    rintro y ⟨z,rfl⟩
    exact (ha z).le
  have hcSup : sSup (Set.range (fun v : K_z ×ˢ K_u =>
      ‖Δ_u_star v - Δ_u cθ v.1.1 v.1.2‖)) ≤ ε/2 := by
    apply csSup_le (Set.range_nonempty _)
    rintro y ⟨v,rfl⟩
    have hv : pack v.1.1 v.1.2 ∈ K := ⟨v.1,v.property,rfl⟩
    have hh := (hc ⟨pack v.1.1 v.1.2,hv⟩).le
    simpa [e, pair, ρ, T, pack, Δ_u] using hh
  refine ⟨aθ,cθ,?_⟩
  exact (max_le haSup hcSup).trans_lt (half_lt_self hε)

/-- Paper Proposition 2 (`prop:density`), with the printed infimum equal to zero.
Both networks have finite affine/ReLU computation graphs. The compact targets
need only be defined on the stated domains; no incremental-gain hypothesis is used. -/
theorem approximation_within_prescribed_envelopes {q m p_z p_u : ℕ}
    (K_z : Set (Rn q)) (K_u : Set (Rn m))
    (hKz : IsCompact K_z) (hKu : IsCompact K_u)
    (hneZ : K_z.Nonempty) (hneU : K_u.Nonempty)
    (Δ_z_star : C(K_z, Rn p_z)) (Δ_u_star : C(K_z ×ˢ K_u, Rn p_u))
    (hz : ∀ z : K_z, ‖Δ_z_star z‖ ≤ ‖(z : Rn q)‖)
    (hu : ∀ v : K_z ×ˢ K_u, ‖Δ_u_star v‖ ≤ ‖v.1.2‖) :
    (⨅ θ : ReLUNetwork q p_z × ReLUNetwork (q+m) p_u,
      residualApproximationError K_z K_u Δ_z_star Δ_u_star θ.1 θ.2) = 0 := by
  have hn (θ : ReLUNetwork q p_z × ReLUNetwork (q+m) p_u) :=
    residualApproximationError_nonneg K_z K_u Δ_z_star Δ_u_star θ.1 θ.2
  have hb : BddBelow (Set.range (fun θ : ReLUNetwork q p_z × ReLUNetwork (q+m) p_u =>
      residualApproximationError K_z K_u Δ_z_star Δ_u_star θ.1 θ.2)) :=
    ⟨0, by rintro y ⟨θ,rfl⟩; exact hn θ⟩
  apply le_antisymm
  · apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨aθ,cθ,happ⟩ := residual_approximation_at_tolerance
      K_z K_u hKz hKu hneZ hneU Δ_z_star Δ_u_star hz hu ε hε
    exact (ciInf_le hb (aθ,cθ)).trans (by simpa using happ.le)
  · exact Real.iInf_nonneg hn

end
end Populus.ModelReduction.Certified
