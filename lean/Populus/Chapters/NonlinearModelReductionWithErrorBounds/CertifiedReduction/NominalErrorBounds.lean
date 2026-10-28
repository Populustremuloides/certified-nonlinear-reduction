import Populus.Chapters.NonlinearModelReductionWithErrorBounds.CertifiedReduction.StrictBoundedReal
import Populus.Chapters.NonlinearModelReductionWithErrorBounds.CertifiedReduction.NominalError

/-!
# Finite bounds for the actual full-minus-reduced nominal realization

Both component nominal matrices are Schur. The joint realization therefore
has bounded actual forced and free responses, proved directly in its standard
Euclidean coordinates. This supplies a genuine strict storage witness for the
nominal error without assuming its gain finiteness as an extra hypothesis.
-/
namespace Populus.ModelReduction.Certified
open scoped Matrix.Norms.L2Operator
noncomputable section
variable {q r m p : ℕ}

theorem prefixNorm_pair_le {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    (x : ℕ → E) (y : ℕ → F) (K : ℕ) :
    prefixNorm (fun k => (x k,y k)) K≤prefixNorm x K+prefixNorm y K := by
  have heq : (fun k => (x k,y k))=fun k => (x k,(0 : F))+((0 : E),y k) := by funext k; simp
  rw [heq]
  have h := prefixNorm_add_le (fun k => (x k,(0 : F))) (fun k => ((0 : E),y k)) K
  simpa [prefixNorm,prefixEnergy,Prod.norm_mk] using h

theorem error_free_state (A : Mat q q) (A_hat : Mat r r) (x : Rn (q+r)) (k : ℕ) :
    errorCoordinates (freeResponse (errorA A A_hat) x k)=
      (freeResponse A (errorCoordinates x).1 k,freeResponse A_hat (errorCoordinates x).2 k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [freeResponse_succ,act_errorA,ContinuousLinearEquiv.apply_symm_apply,ih]
    simp only [freeResponse_succ]

/-- The actual nominal output difference has the sum of the individual
nominal-output bounds, independently of how useful that upper is numerically. -/
theorem error_output_prefix_bound (A : Mat q q) (A_hat : Mat r r)
    (B : Mat q m) (B_hat : Mat r m) (C : Mat p q) (C_hat : Mat p r)
    (g g_hat : ℝ) (hg : HasPrefixChannelGain A B C g)
    (hg_hat : HasPrefixChannelGain A_hat B_hat C_hat g_hat) :
    HasPrefixChannelGain (errorA A A_hat) (errorB B B_hat) (errorC C C_hat) (g+g_hat) := by
  refine ⟨add_nonneg hg.1 hg_hat.1,fun u K => ?_⟩
  simp only [nominal_error_output]
  have heq : (fun k => act C (linearResponse A B u k)-act C_hat (linearResponse A_hat B_hat u k))=
      fun k => act C (linearResponse A B u k)+ -(act C_hat (linearResponse A_hat B_hat u k)) := by rfl
  rw [heq]
  have htri := prefixNorm_add_le (fun k => act C (linearResponse A B u k))
    (fun k => -(act C_hat (linearResponse A_hat B_hat u k))) K
  have hneg : prefixNorm (fun k => -(act C_hat (linearResponse A_hat B_hat u k))) K=
      prefixNorm (fun k => act C_hat (linearResponse A_hat B_hat u k)) K := by simp [prefixNorm,prefixEnergy]
  rw [hneg] at htri
  exact htri.trans (by simpa [add_mul] using add_le_add (hg.2 u K) (hg_hat.2 u K))

theorem error_state_prefix_bound (A : Mat q q) (A_hat : Mat r r)
    (B : Mat q m) (B_hat : Mat r m) (g g_hat : ℝ)
    (hg : HasPrefixChannelGain A B (1 : Mat q q) g)
    (hg_hat : HasPrefixChannelGain A_hat B_hat (1 : Mat r r) g_hat) :
    HasPrefixChannelGain (errorA A A_hat) (errorB B B_hat) (1 : Mat (q+r) (q+r))
      (‖(errorCoordinates : Rn (q+r) ≃L[ℝ] Rn q×Rn r).symm.toContinuousLinearMap‖*(g+g_hat)) := by
  let E : Rn (q+r) ≃L[ℝ] Rn q×Rn r := errorCoordinates
  refine ⟨mul_nonneg (norm_nonneg _) (add_nonneg hg.1 hg_hat.1),fun u K => ?_⟩
  have heq : (fun k => act (1 : Mat (q+r) (q+r)) (linearResponse (errorA A A_hat) (errorB B B_hat) u k))=
      fun k => E.symm (linearResponse A B u k,linearResponse A_hat B_hat u k) := by
    funext k
    rw [act_one,← nominal_error_state A A_hat B B_hat u k,E.symm_apply_apply]
  rw [heq]
  calc
    _ ≤ ‖E.symm.toContinuousLinearMap‖*prefixNorm
        (fun k => (linearResponse A B u k,linearResponse A_hat B_hat u k)) K :=
      prefixNorm_mul_bound _ _ _ (norm_nonneg _) (fun k => E.symm.toContinuousLinearMap.le_opNorm _) K
    _ ≤ ‖E.symm.toContinuousLinearMap‖*(prefixNorm (linearResponse A B u) K+
        prefixNorm (linearResponse A_hat B_hat u) K) :=
      mul_le_mul_of_nonneg_left (prefixNorm_pair_le _ _ K) (norm_nonneg _)
    _ ≤ ‖E.symm.toContinuousLinearMap‖*(g*prefixNorm u K+g_hat*prefixNorm u K) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact add_le_add (by simpa only [act_one] using hg.2 u K)
        (by simpa only [act_one] using hg_hat.2 u K)
    _ = _ := by ring

theorem error_free_prefix_bound (A : Mat q q) (A_hat : Mat r r) (c c_hat : ℝ)
    (hc : HasFreePrefixBound A (1 : Mat q q) c)
    (hc_hat : HasFreePrefixBound A_hat (1 : Mat r r) c_hat) :
    HasFreePrefixBound (errorA A A_hat) (1 : Mat (q+r) (q+r))
      (‖(errorCoordinates : Rn (q+r) ≃L[ℝ] Rn q×Rn r).symm.toContinuousLinearMap‖*
       (c+c_hat)*‖(errorCoordinates : Rn (q+r) ≃L[ℝ] Rn q×Rn r).toContinuousLinearMap‖) := by
  let E : Rn (q+r) ≃L[ℝ] Rn q×Rn r := errorCoordinates
  refine ⟨mul_nonneg (mul_nonneg (norm_nonneg _) (add_nonneg hc.1 hc_hat.1)) (norm_nonneg _),fun x K => ?_⟩
  have heq : (fun k => act (1 : Mat (q+r) (q+r)) (freeResponse (errorA A A_hat) x k))=
      fun k => E.symm (freeResponse A (E x).1 k,freeResponse A_hat (E x).2 k) := by
    funext k
    rw [act_one,← error_free_state A A_hat x k,E.symm_apply_apply]
  rw [heq]
  calc
    _ ≤ ‖E.symm.toContinuousLinearMap‖*prefixNorm
        (fun k => (freeResponse A (E x).1 k,freeResponse A_hat (E x).2 k)) K :=
      prefixNorm_mul_bound _ _ _ (norm_nonneg _) (fun k => E.symm.toContinuousLinearMap.le_opNorm _) K
    _ ≤ ‖E.symm.toContinuousLinearMap‖*(prefixNorm (freeResponse A (E x).1) K+
        prefixNorm (freeResponse A_hat (E x).2) K) :=
      mul_le_mul_of_nonneg_left (prefixNorm_pair_le _ _ K) (norm_nonneg _)
    _ ≤ ‖E.symm.toContinuousLinearMap‖*(c*‖(E x).1‖+c_hat*‖(E x).2‖) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact add_le_add (by simpa only [act_one] using hc.2 (E x).1 K)
        (by simpa only [act_one] using hc_hat.2 (E x).2 K)
    _ ≤ ‖E.symm.toContinuousLinearMap‖*((c+c_hat)*‖E x‖) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      have h₁ := mul_le_mul_of_nonneg_left (norm_fst_le (E x)) hc.1
      have h₂ := mul_le_mul_of_nonneg_left (norm_snd_le (E x)) hc_hat.1
      nlinarith
    _ ≤ ‖E.symm.toContinuousLinearMap‖*((c+c_hat)*(‖E.toContinuousLinearMap‖*‖x‖)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (E.toContinuousLinearMap.le_opNorm x)
        (add_nonneg hc.1 hc_hat.1)) (norm_nonneg _)
    _ = _ := by ring

/-- A free-state bound gives the free bound for any physical observation. -/
theorem free_output_bound_of_state_bound (A : Mat q q) (C : Mat p q) (c : ℝ)
    (hc : HasFreePrefixBound A (1 : Mat q q) c) : HasFreePrefixBound A C (‖C‖*c) := by
  refine ⟨mul_nonneg (norm_nonneg _) hc.1,fun x K => ?_⟩
  have hs : prefixNorm (freeResponse A x) K≤c*‖x‖ := by simpa only [act_one] using hc.2 x K
  calc
    _ ≤ ‖C‖*prefixNorm (freeResponse A x) K :=
      prefixNorm_mul_bound _ _ _ (norm_nonneg _) (fun k => norm_act_le C _) K
    _ ≤ ‖C‖*(c*‖x‖) := mul_le_mul_of_nonneg_left hs (norm_nonneg _)
    _ = _ := by ring

end
end Populus.ModelReduction.Certified
