import Populus.Chapters.NonlinearModelReductionWithErrorBounds.CertifiedReduction.FiniteHorizonFitting

/-!
# Finite-horizon fitting by local continuity along the reference

This gives the trajectory-convergence conclusion used in `thm:main` without
requiring an externally supplied continuity modulus. Induction proves eventual
membership of the approximate states in each reference neighborhood before
using the uniform update estimate there. It does not assume containment.
-/
namespace Populus.ModelReduction.Certified
open scoped Topology
open Filter
noncomputable section
variable {Z U : Type*} [NormedAddCommGroup Z]

/-- Uniform update approximation near a finite reference trajectory and
convergent initialization imply convergence of the actual autoregressive
predictions. Reference continuity is needed only at each visited state. -/
theorem rollout_converges_near_reference
    (F : ℕ → Z → U → Z) (F_star : Z → U → Z)
    (z₀ : ℕ → Z) (z₀_star : Z) (u : ℕ → U)
    (K : Set Z) (H : ℕ) (a : ℝ) (ha : 0<a) (d : ℕ → ℝ)
    (hd : Tendsto d atTop (nhds 0)) (hinit : Tendsto z₀ atTop (nhds z₀_star))
    (hball : ∀ k≤H, ∀ z, ‖z-rollout F_star z₀_star u k‖<a → z∈K)
    (happrox : ∀ ℓ k, k<H → ∀ z∈K, ‖F ℓ z (u k)-F_star z (u k)‖≤d ℓ)
    (hcont : ∀ k<H, ContinuousAt (fun z => F_star z (u k)) (rollout F_star z₀_star u k)) :
    ∀ k≤H, Tendsto (fun ℓ => rollout (F ℓ) (z₀ ℓ) u k)
      atTop (nhds (rollout F_star z₀_star u k)) := by
  intro k
  induction k with
  | zero => intro _; exact hinit
  | succ k ih =>
    intro hk
    have hkH : k<H := by omega
    have hprev := ih (by omega)
    have hn := tendsto_iff_norm_sub_tendsto_zero.1 hprev
    have hmem : ∀ᶠ ℓ in atTop, rollout (F ℓ) (z₀ ℓ) u k∈K := by
      filter_upwards [(tendsto_order.1 hn).2 a ha] with ℓ hℓ
      exact hball k (by omega) _ hℓ
    have herr : Tendsto (fun ℓ => F ℓ (rollout (F ℓ) (z₀ ℓ) u k) (u k)-
        F_star (rollout (F ℓ) (z₀ ℓ) u k) (u k)) atTop (nhds 0) := by
      apply tendsto_iff_norm_sub_tendsto_zero.2
      simp only [sub_zero]
      apply squeeze_zero' (Eventually.of_forall (fun ℓ => norm_nonneg _)) _ hd
      filter_upwards [hmem] with ℓ hℓ
      exact happrox ℓ k hkH _ hℓ
    have hreference := (hcont k hkH).tendsto.comp hprev
    have hsum := herr.add hreference
    simpa only [Function.comp_apply,sub_add_cancel,zero_add,rollout] using hsum

end
end Populus.ModelReduction.Certified
