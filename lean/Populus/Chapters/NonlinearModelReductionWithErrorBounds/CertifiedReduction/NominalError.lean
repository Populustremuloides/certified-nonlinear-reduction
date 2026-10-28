import Populus.Chapters.NonlinearModelReductionWithErrorBounds.CertifiedReduction.StorageWitnessAdapter

/-!
# Actual nominal error realization

Paper: `eq:nominal-error-upper`, Appendix B.2. The joint state consists of the
full and reduced nominal states. Its matrices below are obtained from the
explicit product linear maps in the Euclidean coordinate basis; no error-gain
fact is postulated. A bounded-real witness for these matrices bounds precisely
the difference of the two physical outputs driven by the same applied input.
-/
namespace Populus.ModelReduction.Certified
open scoped ENNReal
noncomputable section
variable {q r m p : ℕ}

abbrev errorCoordinates : Rn (q+r) ≃L[ℝ] Rn q×Rn r := EuclideanSpace.finAddEquivProd

def errorA (A : Mat q q) (A_hat : Mat r r) : Mat (q+r) (q+r) :=
  Matrix.toEuclideanLin.symm (errorCoordinates.symm.toLinearMap.comp
    (((Matrix.toEuclideanLin A).prodMap (Matrix.toEuclideanLin A_hat)).comp
      errorCoordinates.toLinearMap))
def errorB (B : Mat q m) (B_hat : Mat r m) : Mat (q+r) m :=
  Matrix.toEuclideanLin.symm (errorCoordinates.symm.toLinearMap.comp
    ((Matrix.toEuclideanLin B).prod (Matrix.toEuclideanLin B_hat)))
def errorC (C : Mat p q) (C_hat : Mat p r) : Mat p (q+r) :=
  Matrix.toEuclideanLin.symm (((Matrix.toEuclideanLin C).comp (LinearMap.fst ℝ (Rn q) (Rn r))-
    (Matrix.toEuclideanLin C_hat).comp (LinearMap.snd ℝ (Rn q) (Rn r))).comp
      errorCoordinates.toLinearMap)

@[simp] theorem act_errorA (A : Mat q q) (A_hat : Mat r r) (z : Rn (q+r)) :
    act (errorA A A_hat) z=errorCoordinates.symm
      (act A (errorCoordinates z).1,act A_hat (errorCoordinates z).2) := by
  simp [act,errorA]
@[simp] theorem act_errorB (B : Mat q m) (B_hat : Mat r m) (u : Rn m) :
    act (errorB B B_hat) u=errorCoordinates.symm (act B u,act B_hat u) := by
  simp [act,errorB]
@[simp] theorem act_errorC (C : Mat p q) (C_hat : Mat p r) (z : Rn (q+r)) :
    act (errorC C C_hat) z=act C (errorCoordinates z).1-act C_hat (errorCoordinates z).2 := by
  simp [act,errorC]

/-- The joint realization has exactly the two actual nominal states. -/
theorem nominal_error_state (A : Mat q q) (A_hat : Mat r r)
    (B : Mat q m) (B_hat : Mat r m) (u : ℕ → Rn m) (k : ℕ) :
    errorCoordinates (linearResponse (errorA A A_hat) (errorB B B_hat) u k)=
      (linearResponse A B u k,linearResponse A_hat B_hat u k) := by
  induction k with
  | zero =>
    change errorCoordinates (0 : Rn (q+r))=(0,0)
    rw [map_zero]
    rfl
  | succ k ih =>
    change errorCoordinates (act (errorA A A_hat) (linearResponse (errorA A A_hat) (errorB B B_hat) u k)+
      act (errorB B B_hat) (u k)) = _
    simp only [act_errorA,act_errorB,map_add,ContinuousLinearEquiv.apply_symm_apply,ih]
    rfl

/-- The error realization output is exactly the physical nominal difference. -/
theorem nominal_error_output (A : Mat q q) (A_hat : Mat r r)
    (B : Mat q m) (B_hat : Mat r m) (C : Mat p q) (C_hat : Mat p r)
    (u : ℕ → Rn m) (k : ℕ) :
    act (errorC C C_hat) (linearResponse (errorA A A_hat) (errorB B B_hat) u k)=
      act C (linearResponse A B u k)-act C_hat (linearResponse A_hat B_hat u k) := by
  rw [act_errorC,nominal_error_state]

/-- A finite block storage witness gives precisely the nominal error upper
used by the nonlinear certificate. -/
theorem nominal_error_storage_bound (A : Mat q q) (A_hat : Mat r r)
    (B : Mat q m) (B_hat : Mat r m) (C : Mat p q) (C_hat : Mat p r)
    (X : Mat (q+r) (q+r)) (b_r0 : ℝ) (hb : 0≤b_r0) (hX : X.PosDef)
    (hQ : (-boundedRealMatrix (errorA A A_hat) (errorB B B_hat) (errorC C C_hat) X b_r0).PosSemidef) :
    inducedGain (fun u k => act C (linearResponse A B u k)-
      act C_hat (linearResponse A_hat B_hat u k)) ≤ ENNReal.ofReal b_r0 := by
  have h := matrix_storage_channel_gain (errorA A A_hat) (errorB B B_hat) (errorC C C_hat) X b_r0 hb hX hQ
  simpa only [channelGain,inducedGain,nominal_error_output] using h

end
end Populus.ModelReduction.Certified
