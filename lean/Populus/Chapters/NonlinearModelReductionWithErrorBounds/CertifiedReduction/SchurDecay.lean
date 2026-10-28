import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

/-!
# Spectral stability gives genuinely summable powers

This supplies analytic content needed by the manuscript's Schur assumptions;
it is not an interface assuming the desired free-response bound. The first
result is for a complex Banach algebra. A paper-facing real-matrix adapter
must identify the spectrum of the complexified real matrix and its action.
-/
namespace Populus.ModelReduction.Certified
open scoped Topology
open Filter
noncomputable section

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

/-- The squared norm of the actual powers is summable under strict spectral
radius, even when the one-step operator norm is arbitrarily large. -/
theorem summable_norm_pow_sq_of_spectralRadius_lt_one (a : A)
    (ha : spectralRadius ℂ a < 1) : Summable (fun k : ℕ => ‖a^k‖^2) := by
  have hfin : spectralRadius ℂ a ≠ ⊤ := ne_of_lt (ha.trans_le le_top)
  have hs0 : 0 ≤ (spectralRadius ℂ a).toReal := ENNReal.toReal_nonneg
  have hs1 : (spectralRadius ℂ a).toReal < 1 := by
    have ht := (ENNReal.toReal_lt_toReal hfin ENNReal.one_ne_top).2 ha
    simpa using ht
  let r : ℝ := ((spectralRadius ℂ a).toReal+1)/2
  have hr : 0 < r := by dsimp [r]; linarith
  have hr1 : r < 1 := by dsimp [r]; linarith
  have hsr : spectralRadius ℂ a < ENNReal.ofReal r := by
    calc
      spectralRadius ℂ a = ENNReal.ofReal (spectralRadius ℂ a).toReal :=
        (ENNReal.ofReal_toReal hfin).symm
      _ < ENNReal.ofReal r := (ENNReal.ofReal_lt_ofReal_iff hr).2 (by dsimp [r]; linarith)
  have hroot := (tendsto_order.1
    (spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius a)).2
      (ENNReal.ofReal r) hsr
  have hbound : ∀ᶠ n : ℕ in atTop, ‖a^n‖^2 ≤ (r^2)^n := by
    filter_upwards [hroot, eventually_gt_atTop 0] with n hn hn0
    have hnl : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn0)
    have hlt : ‖a^n‖ ^ (1/(n : ℝ)) ≤ r :=
      ((ENNReal.ofReal_lt_ofReal_iff hr).1 hn).le
    have hpow : (‖a^n‖ ^ (1/(n : ℝ)))^n ≤ r^n := by gcongr
    have heq : (‖a^n‖ ^ (1/(n : ℝ)))^n = ‖a^n‖ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
      rw [one_div_mul_cancel hnl, Real.rpow_one]
    rw [heq] at hpow
    have hsquare := (sq_le_sq₀ (norm_nonneg _) (pow_nonneg hr.le n)).2 hpow
    rw [← pow_mul, Nat.mul_comm n 2, pow_mul] at hsquare
    exact hsquare
  have hgeometric : Summable (fun n : ℕ => (r^2)^n) :=
    summable_geometric_of_lt_one (sq_nonneg r) (by nlinarith)
  apply hgeometric.of_norm_bounded_eventually
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [hbound] with n hn
  simpa only [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg ‖a^n‖)] using hn

end
end Populus.ModelReduction.Certified
