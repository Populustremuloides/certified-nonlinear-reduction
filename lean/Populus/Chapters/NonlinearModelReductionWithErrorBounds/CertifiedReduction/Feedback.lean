import Populus.Chapters.NonlinearModelReductionWithErrorBounds.CertifiedReduction.Dynamics
import Populus.Chapters.NonlinearModelReductionWithErrorBounds.CertifiedReduction.AutonomousStability
import Populus.Chapters.NonlinearModelReductionWithErrorBounds.CertifiedReduction.RealSchur

/-!
# Nonlinear feedback estimates from actual discrete channel responses

Paper: Appendix C, full and reconstructed reduced energy estimates.
`O` is the state driving the nonlinear residuals: identity for the full
predictor and `V_r` for the reduced predictor. Channel bounds below are
finite-prefix bounds on actual linear recurrences. Their equivalence to the
paper's infinite-horizon induced-gain hypotheses is a separate adapter.
-/
namespace Populus.ModelReduction.Certified
noncomputable section

variable {d q m p p_u p_z b o : ℕ}

def linearResponse (A : Mat d d) (B : Mat d b) (w : ℕ → Rn b) : ℕ → Rn d :=
  rollout (fun z v => act A z+act B v) 0 w

@[simp] theorem linearResponse_zero (A : Mat d d) (B : Mat d b) :
    linearResponse A B (fun _ => 0) = fun _ => 0 := by
  funext k
  induction k with
  | zero => rfl
  | succ k ih => simpa [linearResponse,rollout] using congrArg (fun z => act A z) ih

@[simp] theorem freeResponse_zero (A : Mat d d) (k : ℕ) : freeResponse A 0 k=0 := by
  simp [freeResponse]

@[simp] theorem freeResponse_initial (A : Mat d d) (z₀ : Rn d) : freeResponse A z₀ 0=z₀ := by
  simp [freeResponse]

@[simp] theorem freeResponse_succ (A : Mat d d) (z₀ : Rn d) (k : ℕ) :
    freeResponse A z₀ (k+1)=act A (freeResponse A z₀ k) := by
  simp [freeResponse,pow_succ',act_mul]

/-- Genuine observed nominal channel bound, valid without input summability. -/
def HasPrefixChannelGain (A : Mat d d) (B : Mat d b) (O : Mat o d) (g : ℝ) : Prop :=
  0 ≤ g ∧ ∀ w K, prefixNorm (fun k => act O (linearResponse A B w k)) K ≤ g*prefixNorm w K

/-- A single formulation of the full and reconstructed reduced feedback loops. -/
def drivenUpdate (N : NominalMatrices d m p p_u p_z) (O : Mat q d)
    (Δ_z : Rn q → Rn p_z) (Δ_u : Rn q → Rn m → Rn p_u)
    (z : Rn d) (u : Rn m) : Rn d :=
  act N.A z+act N.B_u u+act N.B_δu (Δ_u (act O z) u)+act N.B_δz (Δ_z (act O z))

/-- Superposition is derived for the nonlinear trajectory by treating its
actual residual signals as inputs to the nominal channels. -/
theorem trajectory_decomposition
    (N : NominalMatrices d m p p_u p_z) (O : Mat q d)
    (Δ_z : Rn q → Rn p_z) (Δ_u : Rn q → Rn m → Rn p_u)
    (z₀ : Rn d) (u : ℕ → Rn m) :
    let z := rollout (drivenUpdate N O Δ_z Δ_u) z₀ u
    ∀ k, z k=freeResponse N.A z₀ k+linearResponse N.A N.B_u u k+
      linearResponse N.A N.B_δu (fun j => Δ_u (act O (z j)) (u j)) k+
      linearResponse N.A N.B_δz (fun j => Δ_z (act O (z j))) k := by
  dsimp only
  intro k
  induction k with
  | zero => simp [rollout,linearResponse]
  | succ k ih =>
    change drivenUpdate N O Δ_z Δ_u
      (rollout (drivenUpdate N O Δ_z Δ_u) z₀ u k) (u k) = _
    have hlinear := congrArg (act N.A) ih
    simp only [act_add] at hlinear
    rw [drivenUpdate,hlinear,freeResponse_succ]
    simp only [linearResponse,rollout,act_add]
    abel

/-- Finite-prefix small gain for the state that actually drives the residuals. -/
theorem observed_state_prefix_estimate
    (N : NominalMatrices d m p p_u p_z) (O : Mat q d)
    (Δ_z : Rn q → Rn p_z) (Δ_u : Rn q → Rn m → Rn p_u)
    (hz : ∀ z, ‖Δ_z z‖ ≤ ‖z‖) (hu : ∀ z u, ‖Δ_u z u‖ ≤ ‖u‖)
    (g_u g_δu g_δz : ℝ)
    (hg_u : HasPrefixChannelGain N.A N.B_u O g_u)
    (hg_δu : HasPrefixChannelGain N.A N.B_δu O g_δu)
    (hg_δz : HasPrefixChannelGain N.A N.B_δz O g_δz)
    (u : ℕ → Rn m) (K : ℕ) :
    let z := rollout (drivenUpdate N O Δ_z Δ_u) 0 u
    prefixNorm (fun k => act O (z k)) K ≤
      (g_u+g_δu)*prefixNorm u K+g_δz*prefixNorm (fun k => act O (z k)) K := by
  have hgu : 0 ≤ g_u := hg_u.1
  have hgdu : 0 ≤ g_δu := hg_δu.1
  have hgdz : 0 ≤ g_δz := hg_δz.1
  let z := rollout (drivenUpdate N O Δ_z Δ_u) 0 u
  let δ_u := fun k => Δ_u (act O (z k)) (u k)
  let δ_z := fun k => Δ_z (act O (z k))
  have hdecomp : (fun k => act O (z k)) = fun k =>
      (act O (linearResponse N.A N.B_u u k)+act O (linearResponse N.A N.B_δu δ_u k))+
       act O (linearResponse N.A N.B_δz δ_z k) := by
    funext k
    have h := trajectory_decomposition N O Δ_z Δ_u 0 u k
    change z k=_ at h
    rw [h]
    simp [act_add,δ_u,δ_z,z]
  change prefixNorm (fun k => act O (z k)) K ≤ _
  calc
    _ = prefixNorm (fun k =>
      (act O (linearResponse N.A N.B_u u k)+act O (linearResponse N.A N.B_δu δ_u k))+
       act O (linearResponse N.A N.B_δz δ_z k)) K := congrArg (fun s => prefixNorm s K) hdecomp
    _ ≤ (prefixNorm (fun k => act O (linearResponse N.A N.B_u u k)) K+
         prefixNorm (fun k => act O (linearResponse N.A N.B_δu δ_u k)) K)+
         prefixNorm (fun k => act O (linearResponse N.A N.B_δz δ_z k)) K := by
      exact (prefixNorm_add_le _ _ K).trans (add_le_add (prefixNorm_add_le _ _ K) le_rfl)
    _ ≤ (g_u*prefixNorm u K+g_δu*prefixNorm δ_u K)+g_δz*prefixNorm δ_z K :=
      add_le_add (add_le_add (hg_u.2 u K) (hg_δu.2 δ_u K)) (hg_δz.2 δ_z K)
    _ ≤ (g_u*prefixNorm u K+g_δu*prefixNorm u K)+
         g_δz*prefixNorm (fun k => act O (z k)) K := by
      gcongr
      · exact prefixNorm_mono δ_u u (fun k => hu _ _) K
      · exact prefixNorm_mono δ_z (fun k => act O (z k)) (fun k => hz _) K
    _ = _ := by ring

/-- Actual square summability and state-energy bound after feedback closure. -/
theorem observed_state_finite_energy
    (N : NominalMatrices d m p p_u p_z) (O : Mat q d)
    (Δ_z : Rn q → Rn p_z) (Δ_u : Rn q → Rn m → Rn p_u)
    (hz : ∀ z, ‖Δ_z z‖ ≤ ‖z‖) (hu : ∀ z u, ‖Δ_u z u‖ ≤ ‖u‖)
    (g_u g_δu g_δz : ℝ)
    (hg_u : HasPrefixChannelGain N.A N.B_u O g_u)
    (hg_δu : HasPrefixChannelGain N.A N.B_δu O g_δu)
    (hg_δz : HasPrefixChannelGain N.A N.B_δz O g_δz)
    (hsmall : g_δz<1) (u : ℕ → Rn m) (hinput : FiniteEnergy u) :
    let η := fun k => act O (rollout (drivenUpdate N O Δ_z Δ_u) 0 u k)
    FiniteEnergy η ∧ energy η ≤ ((g_u+g_δu)/(1-g_δz))^2*energy u := by
  apply small_gain_finite_energy _ u hinput (g_u+g_δu) g_δz
    (add_nonneg hg_u.1 hg_δu.1) hsmall
  intro K
  exact observed_state_prefix_estimate N O Δ_z Δ_u hz hu g_u g_δu g_δz
    hg_u hg_δu hg_δz u K

end
end Populus.ModelReduction.Certified
