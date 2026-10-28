import Populus.Chapters.NonlinearModelReductionWithErrorBounds.CertifiedReduction.Feedback

namespace Populus.ModelReduction.Certified
noncomputable section
variable {d b o : ℕ}

theorem act_smul (A : Mat d b) (t : ℝ) (x : Rn b) : act A (t • x)=t • act A x := map_smul _ _ _

theorem linearResponse_add (A : Mat d d) (B : Mat d b) (u v : ℕ → Rn b) :
    linearResponse A B (fun k => u k+v k)=fun k => linearResponse A B u k+linearResponse A B v k := by
  funext k
  induction k with
  | zero => simp [linearResponse,rollout]
  | succ k ih =>
    change act A (linearResponse A B (fun j => u j+v j) k)+act B (u k+v k)=_
    rw [ih,act_add,act_add]
    change _=(act A (linearResponse A B u k)+act B (u k))+
      (act A (linearResponse A B v k)+act B (v k))
    abel

theorem linearResponse_smul (A : Mat d d) (B : Mat d b) (t : ℝ) (u : ℕ → Rn b) :
    linearResponse A B (fun k => t • u k)=fun k => t • linearResponse A B u k := by
  funext k
  induction k with
  | zero => simp [linearResponse,rollout]
  | succ k ih =>
    change act A (linearResponse A B (fun j => t • u j) k)+act B (t • u k)=_
    rw [ih,act_smul,act_smul,← smul_add]
    rfl

/-- Actual arbitrary-initial-state nominal response decomposes into its free
trajectory and zero-state forced response. -/
theorem linear_trajectory_decomposition (A : Mat d d) (B : Mat d b)
    (x : Rn d) (u : ℕ → Rn b) (k : ℕ) :
    rollout (fun z v => act A z+act B v) x u k=freeResponse A x k+linearResponse A B u k := by
  induction k with
  | zero => simp [rollout,linearResponse]
  | succ k ih =>
    change act A (rollout (fun z v => act A z+act B v) x u k)+act B (u k)=_
    rw [ih,act_add,freeResponse_succ]
    change _=act A (freeResponse A x k)+(act A (linearResponse A B u k)+act B (u k))
    abel

end
end Populus.ModelReduction.Certified
