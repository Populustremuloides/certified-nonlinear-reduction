import Populus.Chapters.NonlinearModelReductionWithErrorBounds.CertifiedReduction.SignalEnergy
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# The manuscript's extended ℓ₂ norm, before square summability is known

Paper notation: the monotone limit of finite-prefix norms, with `+∞` allowed.
`ℓ₂` is an extended nonnegative real, not a real-valued supremum which could
silently default to zero when unbounded. Its finite case is proved equal to
the square root of the actual convergent squared-norm sum.
-/
namespace Populus.ModelReduction.Certified
open scoped Topology BigOperators ENNReal
open Filter
noncomputable section
variable {E : Type*} [NormedAddCommGroup E]

/-- The paper's extended sequence norm, defined on every ambient sequence. -/
def ℓ₂ (z : ℕ → E) : ℝ≥0∞ := ⨆ K : ℕ, ENNReal.ofReal (prefixNorm z K)

theorem prefixNorm_nonneg (z : ℕ → E) (K : ℕ) : 0 ≤ prefixNorm z K := Real.sqrt_nonneg _

theorem prefixNorm_le_of_ℓ₂_le (z : ℕ → E) (C : ℝ) (hC : 0 ≤ C)
    (h : ℓ₂ z ≤ ENNReal.ofReal C) (K : ℕ) : prefixNorm z K ≤ C := by
  apply (ENNReal.ofReal_le_ofReal_iff hC).1
  exact (le_iSup (fun N => ENNReal.ofReal (prefixNorm z N)) K).trans h

/-- Finite energy implies the exact printed infinite norm formula. -/
theorem ℓ₂_eq_of_finiteEnergy (z : ℕ → E) (hz : FiniteEnergy z) :
    ℓ₂ z = ENNReal.ofReal (Real.sqrt (energy z)) := by
  have hsum : Filter.Tendsto (fun K => prefixEnergy z K) Filter.atTop (nhds (energy z)) := by
    simpa [prefixEnergy,energy] using
      (tendsto_add_atTop_iff_nat 1).mpr hz.hasSum.tendsto_sum_nat
  have hnorm : Filter.Tendsto (fun K => prefixNorm z K) Filter.atTop
      (nhds (Real.sqrt (energy z))) := Real.continuous_sqrt.continuousAt.tendsto.comp hsum
  have hext := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hnorm
  apply le_antisymm
  · apply iSup_le
    intro K
    exact ENNReal.ofReal_le_ofReal
      (Real.sqrt_le_sqrt (prefixEnergy_le_energy z hz K))
  · exact le_of_tendsto hext (Filter.Eventually.of_forall
      (fun K => le_iSup (fun N => ENNReal.ofReal (prefixNorm z N)) K))

/-- Bounded extended norm establishes, rather than assumes, square summability. -/
theorem finiteEnergy_of_ℓ₂_ne_top (z : ℕ → E) (h : ℓ₂ z ≠ ⊤) : FiniteEnergy z := by
  let C : ℝ := (ℓ₂ z).toReal
  have hC : 0 ≤ C := ENNReal.toReal_nonneg
  have hℓ : ℓ₂ z ≤ ENNReal.ofReal C := by rw [ENNReal.ofReal_toReal h]
  have hp : ∀ K, prefixEnergy z K ≤ C^2 := by
    intro K
    have hb := prefixNorm_le_of_ℓ₂_le z C hC hℓ K
    have hs := Real.sq_sqrt (prefixEnergy_nonneg z K)
    have hn := prefixNorm_nonneg z K
    dsimp [prefixNorm] at hb hn
    nlinarith
  exact finiteEnergy_of_prefix_bound z (C^2) (sq_nonneg _) hp

theorem finiteEnergy_iff_ℓ₂_ne_top (z : ℕ → E) : FiniteEnergy z ↔ ℓ₂ z ≠ ⊤ := by
  constructor
  · intro h
    rw [ℓ₂_eq_of_finiteEnergy z h]
    exact ENNReal.ofReal_ne_top
  · exact finiteEnergy_of_ℓ₂_ne_top z

/-- The extended sequence norm vanishes exactly on the zero sequence. -/
theorem ℓ₂_eq_zero_iff (z : ℕ → E) : ℓ₂ z=0 ↔ z=fun _ => 0 := by
  constructor
  · intro h
    funext k
    have hb := prefixNorm_le_of_ℓ₂_le z 0 le_rfl (by simpa [h]) k
    have hterm : ‖z k‖^2 ≤ prefixEnergy z k :=
      Finset.single_le_sum (fun j _ => sq_nonneg ‖z j‖)
        (Finset.mem_range.2 (Nat.lt_succ_self k))
    have hs := Real.sq_sqrt (prefixEnergy_nonneg z k)
    have hn := prefixNorm_nonneg z k
    apply norm_eq_zero.mp
    dsimp [prefixNorm] at hb hn
    nlinarith [norm_nonneg (z k)]
  · rintro rfl
    simp [ℓ₂,prefixNorm,prefixEnergy]

end
end Populus.ModelReduction.Certified
