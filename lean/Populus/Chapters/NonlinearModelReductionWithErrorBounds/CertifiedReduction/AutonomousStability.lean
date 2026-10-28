import Populus.Chapters.NonlinearModelReductionWithErrorBounds.CertifiedReduction.SignalEnergy

/-!
# Summed trajectory energy implies global exponential stability

Paper correspondence: Appendix C.3, `eq:summed-energy`, and the stability
conclusion of `lem:departures`. The energy is the actual sum along `f^[k] ξ`.
This is a generic supporting theorem, not yet the whole paper lemma: a later
adapter must derive its hypothesis from the paper's Schur/margin assumptions.
-/

namespace Populus.ModelReduction.Certified
open scoped BigOperators Topology
noncomputable section

variable {E : Type*} [NormedAddCommGroup E]

/-- The paper's global exponential stability, with positive decay factor < 1,
for every initial state on the full ambient space. -/
def GloballyExponentiallyStable (f : E → E) : Prop :=
  f 0 = 0 ∧ ∃ M α : ℝ, 0 < M ∧ 0 < α ∧ α < 1 ∧
    ∀ ξ₀ k, ‖f^[k] ξ₀‖ ≤ M * α ^ k * ‖ξ₀‖

/-- The actual trajectory-sum function `Υ` in Appendix C.3. -/
def Υ (f : E → E) (ξ : E) : ℝ := energy (fun k => f^[k] ξ)

/-- Lower bound on `Υ`, justified by summability rather than by an arbitrary
real-valued `tsum` convention. -/
theorem norm_sq_le_Υ (f : E → E) (ξ : E)
    (hξ : FiniteEnergy (fun k => f^[k] ξ)) : ‖ξ‖ ^ 2 ≤ Υ f ξ := by
  have h := prefixEnergy_le_energy (fun k => f^[k] ξ) hξ 0
  simpa [Υ] using h

/-- Shift the convergent trajectory sum by one actual nonlinear update. -/
theorem Υ_update (f : E → E) (ξ : E)
    (hξ : FiniteEnergy (fun k => f^[k] ξ)) :
    Υ f (f ξ) = Υ f ξ - ‖ξ‖ ^ 2 := by
  have hs := hξ.tsum_eq_zero_add
  have ht : (fun k => ‖f^[k] (f ξ)‖ ^ 2) =
      (fun k => ‖f^[k+1] ξ‖ ^ 2) := by
    funext k
    rw [Function.iterate_succ_apply]
  change (∑' k, ‖f^[k] (f ξ)‖ ^ 2) = (∑' k, ‖f^[k] ξ‖ ^ 2) - ‖ξ‖ ^ 2
  rw [ht]
  simpa using (eq_sub_iff_add_eq.mpr (by simpa [add_comm] using hs.symm))

/-- Appendix C.3's full summed-energy argument, including an explicit norm
estimate. We enlarge `M₀` by one to cover its `M₀ = 1` case uniformly. -/
theorem globally_exponentially_stable_of_summed_energy
    (f : E → E) (M₀ : ℝ) (hM₀ : 1 ≤ M₀)
    (henergy : ∀ ξ : E, FiniteEnergy (fun k => f^[k] ξ) ∧
      Υ f ξ ≤ M₀ * ‖ξ‖ ^ 2) : GloballyExponentiallyStable f := by
  let M : ℝ := M₀ + 1
  let ρ : ℝ := 1 - M⁻¹
  have hM : 1 < M := by dsimp [M]; linarith
  have hMp : 0 < M := by linarith
  have hρp : 0 < ρ := by
    dsimp [ρ]
    have hi : M⁻¹ < 1 := (inv_lt_one₀ hMp).mpr hM
    linarith
  have hρ1 : ρ < 1 := by dsimp [ρ]; linarith [inv_pos.mpr hMp]
  have hupp (ξ : E) : Υ f ξ ≤ M * ‖ξ‖ ^ 2 := by
    exact (henergy ξ).2.trans (mul_le_mul_of_nonneg_right (by dsimp [M]; linarith)
      (sq_nonneg ‖ξ‖))
  have hlow (ξ : E) : ‖ξ‖ ^ 2 ≤ Υ f ξ := norm_sq_le_Υ f ξ (henergy ξ).1
  have hdecrease (ξ : E) : Υ f (f ξ) ≤ ρ * Υ f ξ := by
    rw [Υ_update f ξ (henergy ξ).1]
    have hdiv : Υ f ξ / M ≤ ‖ξ‖ ^ 2 :=
      (div_le_iff₀ hMp).2 (by simpa [mul_comm] using hupp ξ)
    simp only [div_eq_mul_inv] at hdiv
    dsimp [ρ]
    nlinarith
  have hiterate (k : ℕ) (ξ : E) : Υ f (f^[k] ξ) ≤ ρ ^ k * Υ f ξ := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      calc
        Υ f (f (f^[k] ξ)) ≤ ρ * Υ f (f^[k] ξ) := hdecrease _
        _ ≤ ρ * (ρ ^ k * Υ f ξ) := mul_le_mul_of_nonneg_left ih hρp.le
        _ = ρ ^ (k+1) * Υ f ξ := by ring
  have hsquared (ξ : E) (k : ℕ) : ‖f^[k] ξ‖ ^ 2 ≤ M * ρ ^ k * ‖ξ‖ ^ 2 := by
    calc
      ‖f^[k] ξ‖ ^ 2 ≤ Υ f (f^[k] ξ) := hlow _
      _ ≤ ρ ^ k * Υ f ξ := hiterate k ξ
      _ ≤ ρ ^ k * (M * ‖ξ‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (hupp ξ) (pow_nonneg hρp.le k)
      _ = M * ρ ^ k * ‖ξ‖ ^ 2 := by ring
  have hnorm (ξ : E) (k : ℕ) :
      ‖f^[k] ξ‖ ≤ Real.sqrt M * (Real.sqrt ρ) ^ k * ‖ξ‖ := by
    have hr : 0 ≤ Real.sqrt M * (Real.sqrt ρ) ^ k * ‖ξ‖ := by positivity
    have heq : (Real.sqrt M * (Real.sqrt ρ) ^ k * ‖ξ‖) ^ 2 =
        M * ρ ^ k * ‖ξ‖ ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hMp.le]
      rw [← pow_mul, Nat.mul_comm k 2, pow_mul, Real.sq_sqrt hρp.le]
    nlinarith [hsquared ξ k]
  refine ⟨?_, Real.sqrt M, Real.sqrt ρ, Real.sqrt_pos.2 hMp,
    Real.sqrt_pos.2 hρp, ?_, hnorm⟩
  · have hzero := hnorm 0 1
    simpa using norm_eq_zero.mp (le_antisymm (by simpa using hzero) (norm_nonneg _))
  · simpa using Real.sqrt_lt_sqrt hρp.le hρ1


/-- The paper's GAS conclusion, expanded into origin equilibrium, Lyapunov
stability at every discrete time, and attraction from every ambient state. -/
def GloballyAsymptoticallyStable (f : E → E) : Prop :=
  f 0 = 0 ∧
  (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ ξ₀, ‖ξ₀‖ < δ → ∀ k : ℕ, ‖f^[k] ξ₀‖ < ε) ∧
  (∀ ξ₀, Filter.Tendsto (fun k : ℕ => f^[k] ξ₀) Filter.atTop (nhds 0))

/-- Global exponential stability supplies exactly the GAS implication in
Definition 3 (`def:certificate`), with no hidden regional restriction. -/
theorem GloballyExponentiallyStable.gas {f : E → E}
    (hf : GloballyExponentiallyStable f) : GloballyAsymptoticallyStable f := by
  rcases hf with ⟨hzero,M,α,hM,hα,hα1,hbound⟩
  refine ⟨hzero,?_,?_⟩
  · intro ε hε
    refine ⟨ε/M, div_pos hε hM, ?_⟩
    intro ξ₀ hξ k
    have hp : α^k ≤ 1 := pow_le_one₀ hα.le hα1.le
    calc
      ‖f^[k] ξ₀‖ ≤ M * α^k * ‖ξ₀‖ := hbound ξ₀ k
      _ ≤ M * 1 * ‖ξ₀‖ := by gcongr
      _ < ε := by have := (lt_div_iff₀ hM).1 hξ; nlinarith
  · intro ξ₀
    apply tendsto_iff_norm_sub_tendsto_zero.2
    simp only [sub_zero]
    have hp := tendsto_pow_atTop_nhds_zero_of_lt_one hα.le hα1
    have hright : Filter.Tendsto (fun k : ℕ => M * α^k * ‖ξ₀‖)
        Filter.atTop (nhds 0) := by
      simpa using (tendsto_const_nhds.mul hp).mul tendsto_const_nhds
    exact squeeze_zero (fun k => norm_nonneg _) (hbound ξ₀) hright

end
end Populus.ModelReduction.Certified
