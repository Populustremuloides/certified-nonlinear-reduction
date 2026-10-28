import Populus.Chapters.NonlinearModelReductionWithErrorBounds.CertifiedReduction.Feedback
import Populus.Chapters.NonlinearModelReductionWithErrorBounds.CertifiedReduction.SequenceNorm

/-!
# Actual induced channel gains and their finite-prefix interpretation

Paper: Definitions 5--6. The numerator is the extended ℓ₂ norm of the actual
zero-state observed linear response; the input is any nonzero ℓ₂ sequence.
An infinite output norm is never converted to a real zero. Causality and
finite input truncation derive finite-prefix bounds from the printed gain.
-/
namespace Populus.ModelReduction.Certified
open scoped Topology BigOperators ENNReal
noncomputable section
variable {d b o : ℕ}

/-- Definition 5/6's induced gain with arbitrary observation `O` (I, Vᵣ, C,
or C Vᵣ); the independent test input has precisely `B`'s column dimension. -/
def channelGain (A : Mat d d) (B : Mat d b) (O : Mat o d) : ℝ≥0∞ :=
  ⨆ w : ℕ → Rn b, ⨆ (_ : FiniteEnergy w), ⨆ (_ : w ≠ fun _ => 0),
    ℓ₂ (fun k => act O (linearResponse A B w k)) / ℓ₂ w

/-- The same gain bound as an inequality, before any output-membership result. -/
def HasChannelGain (A : Mat d d) (B : Mat d b) (O : Mat o d) (g : ℝ) : Prop :=
  0 ≤ g ∧ ∀ w, FiniteEnergy w →
    ℓ₂ (fun k => act O (linearResponse A B w k)) ≤ ENNReal.ofReal g*ℓ₂ w

/-- Supremum-of-ratios and inequality definitions agree on the paper's
nonzero finite-energy input domain, including the zero-input case. -/
theorem hasChannelGain_iff (A : Mat d d) (B : Mat d b) (O : Mat o d)
    (g : ℝ) (hg : 0 ≤ g) :
    HasChannelGain A B O g ↔ channelGain A B O ≤ ENNReal.ofReal g := by
  constructor
  · intro h
    refine iSup_le (fun w => iSup_le (fun hw => iSup_le (fun hne => ?_)))
    have hzero : ℓ₂ w ≠ 0 := by simpa [ℓ₂_eq_zero_iff] using hne
    have hfinite : ℓ₂ w ≠ ⊤ := (finiteEnergy_iff_ℓ₂_ne_top w).1 hw
    exact (ENNReal.div_le_iff hzero hfinite).2 (h.2 w hw)
  · intro h
    refine ⟨hg,fun w hw => ?_⟩
    by_cases hne : w=fun _ => 0
    · subst w
      simp [linearResponse_zero,ℓ₂,prefixNorm,prefixEnergy]
    · have hzero : ℓ₂ w ≠ 0 := by simpa [ℓ₂_eq_zero_iff] using hne
      have hfinite : ℓ₂ w ≠ ⊤ := (finiteEnergy_iff_ℓ₂_ne_top w).1 hw
      have hr0 : ℓ₂ (fun k => act O (linearResponse A B w k)) / ℓ₂ w ≤ channelGain A B O := by
        unfold channelGain
        exact le_iSup_of_le w (le_iSup_of_le hw (le_iSup_of_le hne le_rfl))
      have hr := hr0.trans h
      exact (ENNReal.div_le_iff hzero hfinite).1 hr

def truncate (w : ℕ → Rn b) (K : ℕ) (k : ℕ) : Rn b := if k ≤ K then w k else 0

/-- The truncated input has finite energy for every original input. -/
theorem truncate_finiteEnergy (w : ℕ → Rn b) (K : ℕ) : FiniteEnergy (truncate w K) := by
  apply (hasSum_sum_of_ne_finset_zero (s := Finset.range (K+1)) ?_).summable
  intro k hk
  have hlt : ¬k ≤ K := by simpa using hk
  simp [truncate,hlt]

/-- Its actual infinite energy is the original inclusive-prefix energy. -/
theorem energy_truncate (w : ℕ → Rn b) (K : ℕ) :
    energy (truncate w K)=prefixEnergy w K := by
  unfold energy
  rw [tsum_eq_sum (s := Finset.range (K+1)) (fun k hk => by
    have hlt : ¬k ≤ K := by simpa using hk
    simp [truncate,hlt])]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k ≤ K := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
  simp [truncate,hk',prefixEnergy]

/-- The response is causal in exactly the sense needed by the prefix proof. -/
theorem linearResponse_agrees_through (A : Mat d d) (B : Mat d b)
    (w v : ℕ → Rn b) (K : ℕ) (h : ∀ j ≤ K, w j=v j) :
    ∀ j ≤ K+1, linearResponse A B w j=linearResponse A B v j := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
    intro hj
    change act A (linearResponse A B w j)+act B (w j) =
      act A (linearResponse A B v j)+act B (v j)
    rw [ih (by omega),h j (by omega)]

private theorem prefixNorm_ext {E : Type*} [NormedAddCommGroup E]
    (z w : ℕ → E) (K : ℕ) (h : ∀ j ≤ K, z j=w j) : prefixNorm z K=prefixNorm w K := by
  apply congrArg Real.sqrt
  apply Finset.sum_congr rfl
  intro j hj
  rw [h j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))]

/-- The infinite-horizon gain controls arbitrary finite prefixes, by truncating
inputs and using causal agreement. The original input need not be in ℓ₂. -/
theorem hasPrefixChannelGain_of_hasChannelGain
    (A : Mat d d) (B : Mat d b) (O : Mat o d) (g : ℝ)
    (h : HasChannelGain A B O g) : HasPrefixChannelGain A B O g := by
  refine ⟨h.1,fun w K => ?_⟩
  have hout := h.2 (truncate w K) (truncate_finiteEnergy w K)
  rw [ℓ₂_eq_of_finiteEnergy _ (truncate_finiteEnergy w K),energy_truncate] at hout
  rw [← ENNReal.ofReal_mul h.1] at hout
  have hprefix := prefixNorm_le_of_ℓ₂_le
    (fun k => act O (linearResponse A B (truncate w K) k)) (g*prefixNorm w K)
    (mul_nonneg h.1 (prefixNorm_nonneg w K)) hout K
  have hagree := linearResponse_agrees_through A B (truncate w K) w K
    (fun j hj => by simp [truncate,hj])
  have heq := prefixNorm_ext
    (fun k => act O (linearResponse A B (truncate w K) k))
    (fun k => act O (linearResponse A B w k)) K
    (fun j hj => congrArg (act O) (hagree j (by omega)))
  rwa [heq] at hprefix

/-- Conversely, prefix bounds imply the full extended ℓ₂ inequality. -/
theorem hasChannelGain_of_hasPrefixChannelGain
    (A : Mat d d) (B : Mat d b) (O : Mat o d) (g : ℝ)
    (h : HasPrefixChannelGain A B O g) : HasChannelGain A B O g := by
  refine ⟨h.1,fun w hw => ?_⟩
  apply iSup_le
  intro K
  have hp := ENNReal.ofReal_le_ofReal (h.2 w K)
  rw [ENNReal.ofReal_mul h.1] at hp
  exact hp.trans (mul_le_mul_left' (le_iSup (fun N => ENNReal.ofReal (prefixNorm w N)) K) _)

/-- The finite-prefix formulation used in Appendix C is equivalent to a bound
on the actual induced gain in Definitions 5--6. -/
theorem prefix_channel_gain_iff_induced_gain_bound
    (A : Mat d d) (B : Mat d b) (O : Mat o d) (g : ℝ) (hg : 0 ≤ g) :
    HasPrefixChannelGain A B O g ↔ channelGain A B O ≤ ENNReal.ofReal g :=
  ⟨fun h => (hasChannelGain_iff A B O g hg).1
      (hasChannelGain_of_hasPrefixChannelGain A B O g h),
   fun h => hasPrefixChannelGain_of_hasChannelGain A B O g
      ((hasChannelGain_iff A B O g hg).2 h)⟩

end
end Populus.ModelReduction.Certified
