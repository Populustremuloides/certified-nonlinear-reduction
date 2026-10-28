import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Discrete signal energy for the certified-reduction manuscript

Paper: `stability_preserving_reduction_review_20261014/main.tex`.
This file uses genuine squared Euclidean/normed-space sequence energies.
The paper prefix `[0,K]` is `Finset.range (K+1)`, including the endpoint.
Infinite real sums below are used only after establishing `Summable`.
No finite-energy state assumption is inserted into a small-gain conclusion.
-/

namespace Populus.ModelReduction.Certified

open scoped BigOperators Topology

noncomputable section

variable {E : Type*} [NormedAddCommGroup E]

/-- Paper notation `‖z‖²_{ℓ₂[0,K]}`. -/
def prefixEnergy (z : ℕ → E) (K : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (K + 1), ‖z k‖ ^ 2

/-- Square summability, before any infinite real norm is used. -/
def FiniteEnergy (z : ℕ → E) : Prop := Summable (fun k => ‖z k‖ ^ 2)

/-- The summed energy used in `eq:summed-energy` and its Lyapunov construction.
Every theorem interpreting this as signal energy proves `FiniteEnergy` first. -/
def energy (z : ℕ → E) : ℝ := ∑' k, ‖z k‖ ^ 2

@[simp] theorem prefixEnergy_zero (z : ℕ → E) : prefixEnergy z 0 = ‖z 0‖ ^ 2 := by
  simp [prefixEnergy]

theorem prefixEnergy_nonneg (z : ℕ → E) (K : ℕ) : 0 ≤ prefixEnergy z K := by
  exact Finset.sum_nonneg (fun k _ => sq_nonneg ‖z k‖)

/-- Finite-prefix estimates establish summability rather than assuming it.
Corresponds to the monotone-limit steps in Appendix C. -/
theorem finiteEnergy_of_prefix_bound (z : ℕ → E) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ K, prefixEnergy z K ≤ C) : FiniteEnergy z := by
  apply summable_of_sum_range_le (fun k => sq_nonneg ‖z k‖)
  intro n
  cases n with
  | zero => simpa using hC
  | succ K => exact h K

/-- The same prefix estimate bounds the actual infinite sum. -/
theorem energy_le_of_prefix_bound (z : ℕ → E) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ K, prefixEnergy z K ≤ C) : energy z ≤ C := by
  apply Real.tsum_le_of_sum_range_le (fun k => sq_nonneg ‖z k‖)
  intro n
  cases n with
  | zero => simpa using hC
  | succ K => exact h K

/-- Every finite prefix is bounded by the actual infinite energy. -/
theorem prefixEnergy_le_energy (z : ℕ → E) (hz : FiniteEnergy z) (K : ℕ) :
    prefixEnergy z K ≤ energy z := by
  exact Summable.sum_le_tsum (Finset.range (K + 1))
    (fun k _ => sq_nonneg ‖z k‖) hz

/-- The small-gain rearrangement, for arbitrary signals, on finite prefixes.
No `FiniteEnergy z` hypothesis occurs. -/
theorem prefix_small_gain {U : Type*} [NormedAddCommGroup U]
    (z : ℕ → E) (u : ℕ → U) (a b : ℝ)
    (ha : 0 ≤ a) (hb : b < 1)
    (h : ∀ K, Real.sqrt (prefixEnergy z K) ≤
      a * Real.sqrt (prefixEnergy u K) + b * Real.sqrt (prefixEnergy z K)) :
    ∀ K, prefixEnergy z K ≤ (a / (1-b)) ^ 2 * prefixEnergy u K := by
  intro K
  have hp : 0 < 1-b := sub_pos.mpr hb
  have hlin : Real.sqrt (prefixEnergy z K) ≤
      a / (1-b) * Real.sqrt (prefixEnergy u K) := by
    have hm : Real.sqrt (prefixEnergy z K) * (1-b) ≤
        a * Real.sqrt (prefixEnergy u K) := by nlinarith [h K]
    have hd := (le_div_iff₀ hp).2 hm
    convert hd using 1 <;> ring
  have hright : 0 ≤ a / (1-b) * Real.sqrt (prefixEnergy u K) := by positivity
  have hs := sq_le_sq₀ (Real.sqrt_nonneg (prefixEnergy z K)) hright
  have hs' := hs.mpr hlin
  rw [Real.sq_sqrt (prefixEnergy_nonneg z K)] at hs'
  nlinarith [Real.sq_sqrt (prefixEnergy_nonneg u K)]

/-- Zero-state state-energy conclusion of Appendix C, obtained by closing
finite prefixes and only then proving square summability. -/
theorem small_gain_finite_energy {U : Type*} [NormedAddCommGroup U]
    (z : ℕ → E) (u : ℕ → U) (hu : FiniteEnergy u) (a b : ℝ)
    (ha : 0 ≤ a) (hb : b < 1)
    (h : ∀ K, Real.sqrt (prefixEnergy z K) ≤
      a * Real.sqrt (prefixEnergy u K) + b * Real.sqrt (prefixEnergy z K)) :
    FiniteEnergy z ∧ energy z ≤ (a / (1-b)) ^ 2 * energy u := by
  have hbound := prefix_small_gain z u a b ha hb h
  have henergy : 0 ≤ energy u := tsum_nonneg (fun k => sq_nonneg ‖u k‖)
  have hC : 0 ≤ (a / (1-b)) ^ 2 * energy u := mul_nonneg (sq_nonneg _) henergy
  have hp : ∀ K, prefixEnergy z K ≤ (a / (1-b)) ^ 2 * energy u := by
    intro K
    exact (hbound K).trans (mul_le_mul_of_nonneg_left
      (prefixEnergy_le_energy u hu K) (sq_nonneg _))
  exact ⟨finiteEnergy_of_prefix_bound z _ hC hp,
    energy_le_of_prefix_bound z _ hC hp⟩


/-- Paper prefix norm, defined for every signal without a summability premise. -/
def prefixNorm (z : ℕ → E) (K : ℕ) : ℝ := Real.sqrt (prefixEnergy z K)

private def prefixVector (z : ℕ → E) (K : ℕ) : PiLp 2 (fun _ : Fin (K+1) => E) :=
  WithLp.toLp 2 (fun k => z k)

private theorem norm_prefixVector (z : ℕ → E) (K : ℕ) :
    ‖prefixVector z K‖ = prefixNorm z K := by
  rw [PiLp.norm_eq_of_L2]
  change Real.sqrt (∑ k : Fin (K+1), ‖z k‖ ^ 2) =
    Real.sqrt (∑ k ∈ Finset.range (K+1), ‖z k‖ ^ 2)
  exact congrArg Real.sqrt (Fin.sum_univ_eq_sum_range (fun k => ‖z k‖ ^ 2) (K+1))

theorem prefixNorm_add_le (z w : ℕ → E) (K : ℕ) :
    prefixNorm (fun k => z k+w k) K ≤ prefixNorm z K+prefixNorm w K := by
  have heq : prefixVector (fun k => z k+w k) K = prefixVector z K+prefixVector w K := by
    ext k
    rfl
  rw [← norm_prefixVector,heq,← norm_prefixVector,← norm_prefixVector]
  exact norm_add_le _ _

theorem prefixNorm_mono {F : Type*} [NormedAddCommGroup F]
    (z : ℕ → E) (w : ℕ → F) (h : ∀ k, ‖z k‖ ≤ ‖w k‖) (K : ℕ) :
    prefixNorm z K ≤ prefixNorm w K := by
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro k _
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (h k)

theorem prefixNorm_mul_bound {F : Type*} [NormedAddCommGroup F]
    (z : ℕ → E) (w : ℕ → F) (c : ℝ) (hc : 0 ≤ c)
    (h : ∀ k, ‖z k‖ ≤ c*‖w k‖) (K : ℕ) :
    prefixNorm z K ≤ c*prefixNorm w K := by
  have hs : prefixEnergy z K ≤ c^2*prefixEnergy w K := by
    rw [prefixEnergy,prefixEnergy,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k _
    have ht := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hc (norm_nonneg _))).mpr (h k)
    nlinarith
  have hsq := Real.sqrt_le_sqrt hs
  simpa [prefixNorm,Real.sqrt_mul (sq_nonneg c),Real.sqrt_sq hc] using hsq

end
end Populus.ModelReduction.Certified
