import Populus.Chapters.NonlinearModelReductionWithErrorBounds.CertifiedReduction.SignalEnergy

/-!
# Autoregressive approximation over a fixed finite horizon

Paper: the trajectory-containment induction in Appendix E (`thm:main`).
The theorem below derives trajectory convergence from update/initialization
approximation on a neighborhood. It never assumes that the approximate
trajectories remain in that neighborhood. The actual neural construction and
existence of the continuity modulus are separate obligations for the final
paper theorem.
-/

namespace Populus.ModelReduction.Certified
open scoped Topology
noncomputable section

variable {Z U : Type*} [NormedAddCommGroup Z]

/-- The paper's full autoregressive recurrence, for an arbitrary input. -/
def rollout (F : Z → U → Z) (z₀ : Z) (u : ℕ → U) : ℕ → Z
  | 0 => z₀
  | k+1 => F (rollout F z₀ u k) (u k)

/-- Scalar bounds `b_{ℓ,0}=d_{ℓ,0}`, `b_{ℓ,k+1}=d_ℓ+ω(b_{ℓ,k})`. -/
def b (d d₀ : ℝ) (ω : ℝ → ℝ) : ℕ → ℝ
  | 0 => d₀
  | k+1 => d + ω (b d d₀ ω k)

/-- Construct the scalar bounds independently of the approximate trajectories. -/
theorem b_tendsto_zero (d d₀ : ℕ → ℝ) (ω : ℝ → ℝ)
    (hd : Filter.Tendsto d Filter.atTop (nhds 0))
    (hd₀ : Filter.Tendsto d₀ Filter.atTop (nhds 0))
    (hω : ContinuousAt ω 0) (hω₀ : ω 0 = 0) :
    ∀ k, Filter.Tendsto (fun ℓ => b (d ℓ) (d₀ ℓ) ω k) Filter.atTop (nhds 0) := by
  intro k
  induction k with
  | zero => exact hd₀
  | succ k ih =>
    simpa [b,hω₀] using hd.add (hω.tendsto.comp ih)

/-- One sufficiently large index controls all steps of a fixed horizon. -/
theorem b_eventually_small (d d₀ : ℕ → ℝ) (ω : ℝ → ℝ)
    (hb : ∀ k, Filter.Tendsto (fun ℓ => b (d ℓ) (d₀ ℓ) ω k)
      Filter.atTop (nhds 0)) (H : ℕ) (a : ℝ) (ha : 0 < a) :
    ∀ᶠ ℓ in Filter.atTop, ∀ k ≤ H, b (d ℓ) (d₀ ℓ) ω k < a := by
  induction H with
  | zero =>
    filter_upwards [(tendsto_order.1 (hb 0)).2 a ha] with ℓ hℓ k hk
    have : k=0 := by omega
    subst k
    exact hℓ
  | succ H ih =>
    filter_upwards [ih, (tendsto_order.1 (hb (H+1))).2 a ha] with ℓ hℓ hlast k hk
    by_cases h : k ≤ H
    · exact hℓ k h
    · have : k=H+1 := by omega
      subst k
      exact hlast

/-- Finite-horizon induction simultaneously proves the error bound and keeps
all approximate states inside the prescribed approximation region. -/
theorem rollout_error_bound
    (F F_star : Z → U → Z) (z₀ z₀_star : Z) (u : ℕ → U)
    (K : Set Z) (H : ℕ) (a d d₀ : ℝ) (ω : ℝ → ℝ)
    (hω : Monotone ω)
    (hinit : ‖z₀-z₀_star‖ ≤ d₀)
    (hball : ∀ k ≤ H, ∀ z : Z, ‖z-rollout F_star z₀_star u k‖ < a → z ∈ K)
    (happrox : ∀ k < H, ∀ z ∈ K, ‖F z (u k)-F_star z (u k)‖ ≤ d)
    (hcont : ∀ k < H, ∀ z ∈ K, ∀ w ∈ K,
      ‖F_star z (u k)-F_star w (u k)‖ ≤ ω ‖z-w‖)
    (hsmall : ∀ k ≤ H, b d d₀ ω k < a) :
    ∀ k ≤ H,
      ‖rollout F z₀ u k-rollout F_star z₀_star u k‖ ≤ b d d₀ ω k ∧
      rollout F z₀ u k ∈ K := by
  have ha : 0 < a := by
    have h0 := hsmall 0 (Nat.zero_le _)
    have hn : 0 ≤ d₀ := le_trans (norm_nonneg _) hinit
    simpa [b] using hn.trans_lt h0
  intro k
  induction k with
  | zero =>
    intro hk
    refine ⟨hinit,?_⟩
    apply hball 0 hk z₀
    exact hinit.trans_lt (hsmall 0 hk)
  | succ k ih =>
    intro hk
    have hkH : k < H := by omega
    obtain ⟨herr,hmem⟩ := ih (by omega)
    have href : rollout F_star z₀_star u k ∈ K := by
      apply hball k (by omega)
      simpa using ha
    have hnext : ‖rollout F z₀ u (k+1)-rollout F_star z₀_star u (k+1)‖ ≤
        b d d₀ ω (k+1) := by
      change ‖F (rollout F z₀ u k) (u k)-F_star (rollout F_star z₀_star u k) (u k)‖ ≤ _
      calc
        _ ≤ ‖F (rollout F z₀ u k) (u k)-F_star (rollout F z₀ u k) (u k)‖ +
            ‖F_star (rollout F z₀ u k) (u k)-F_star (rollout F_star z₀_star u k) (u k)‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ d+ω ‖rollout F z₀ u k-rollout F_star z₀_star u k‖ :=
          add_le_add (happrox k hkH _ hmem) (hcont k hkH _ hmem _ href)
        _ ≤ d+ω (b d d₀ ω k) := add_le_add le_rfl (hω herr)
        _ = b d d₀ ω (k+1) := rfl
    exact ⟨hnext,hball (k+1) hk _ (hnext.trans_lt (hsmall (k+1) hk))⟩

/-- The convergence step used in the paper's main theorem. All trajectory
containment conclusions are proved from finite approximation neighborhoods. -/
theorem rollout_converges_on_fixed_horizon
    (F : ℕ → Z → U → Z) (F_star : Z → U → Z)
    (z₀ : ℕ → Z) (z₀_star : Z) (u : ℕ → U)
    (K : Set Z) (H : ℕ) (a : ℝ) (ha : 0 < a)
    (d d₀ : ℕ → ℝ) (ω : ℝ → ℝ)
    (hd : Filter.Tendsto d Filter.atTop (nhds 0))
    (hd₀ : Filter.Tendsto d₀ Filter.atTop (nhds 0))
    (hω : ContinuousAt ω 0) (hω₀ : ω 0 = 0) (hmono : Monotone ω)
    (hinit : ∀ ℓ, ‖z₀ ℓ-z₀_star‖ ≤ d₀ ℓ)
    (hball : ∀ k ≤ H, ∀ z : Z, ‖z-rollout F_star z₀_star u k‖ < a → z ∈ K)
    (happrox : ∀ ℓ k, k < H → ∀ z ∈ K, ‖F ℓ z (u k)-F_star z (u k)‖ ≤ d ℓ)
    (hcont : ∀ k < H, ∀ z ∈ K, ∀ w ∈ K,
      ‖F_star z (u k)-F_star w (u k)‖ ≤ ω ‖z-w‖) :
    ∀ k ≤ H, Filter.Tendsto (fun ℓ => rollout (F ℓ) (z₀ ℓ) u k)
      Filter.atTop (nhds (rollout F_star z₀_star u k)) := by
  have hb := b_tendsto_zero d d₀ ω hd hd₀ hω hω₀
  have hsmall := b_eventually_small d d₀ ω hb H a ha
  intro k hk
  apply tendsto_iff_norm_sub_tendsto_zero.2
  have hbound : ∀ᶠ ℓ in Filter.atTop,
      ‖rollout (F ℓ) (z₀ ℓ) u k-rollout F_star z₀_star u k‖ ≤
        b (d ℓ) (d₀ ℓ) ω k := by
    filter_upwards [hsmall] with ℓ hℓ
    exact (rollout_error_bound (F ℓ) F_star (z₀ ℓ) z₀_star u K H a
      (d ℓ) (d₀ ℓ) ω hmono (hinit ℓ) hball (happrox ℓ) hcont hℓ k hk).1
  exact squeeze_zero' (Filter.Eventually.of_forall (fun ℓ => norm_nonneg _)) hbound (hb k)

end
end Populus.ModelReduction.Certified
