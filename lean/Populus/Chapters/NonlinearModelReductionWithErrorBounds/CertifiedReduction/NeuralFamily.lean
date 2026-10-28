import Populus.Chapters.NonlinearModelReductionWithErrorBounds.CertifiedReduction.FittingWithFixedWitnesses
import Populus.Chapters.NonlinearModelReductionWithErrorBounds.CertifiedReduction.ReferenceClass

/-!
# The universal finite neural family and its reduction certificate

The residual channel dimensions and finite computation trees are parameter
data. Matrices, physical decoder/readout, projection and gain witnesses also
belong to the parameter, exactly as in Definition 7. Reconstruction and
projection identities are standing restrictions on this parameter domain.
-/
namespace Populus.ModelReduction.Certified
open scoped ENNReal
noncomputable section
variable {n q r m p N H : ℕ}

structure Θ (n q r m p : ℕ) where
  p_u : ℕ
  p_z : ℕ
  nominal : NominalMatrices q m p p_u p_z
  C_x : Mat n q
  S_y : Mat p n
  output_identity : nominal.C=S_y*C_x
  reconstruction_inverse : C_x*C_x_dagger C_x=1
  W_r : Mat r q
  V_r : Mat q r
  left_inverse : W_r*V_r=1
  networks : NeuralParameter n q m p_u p_z
  witnesses : ReductionWitnesses q r

namespace Θ

def Φ (θ : Θ n q r m p) : Rn n → Rn q := Φ_θ θ.C_x θ.networks.ψ
def F_tilde (θ : Θ n q r m p) : Rn q → Rn m → Rn q :=
  neuralUpdate θ.nominal θ.networks.a θ.networks.c
def F_hat (θ : Θ n q r m p) : Rn r → Rn m → Rn r :=
  θ.nominal.reducedUpdate θ.W_r θ.V_r (Δ_z θ.networks.a) (Δ_u θ.networks.c)
def 𝒢 (θ : Θ n q r m p) : (ℕ → Rn m) → ℕ → Rn p :=
  nonlinearResponse θ.nominal (1 : Mat q q) (Δ_z θ.networks.a) (Δ_u θ.networks.c)
def 𝒢_hat (θ : Θ n q r m p) : (ℕ → Rn m) → ℕ → Rn p :=
  nonlinearResponse (θ.nominal.reduced θ.W_r θ.V_r) θ.V_r (Δ_z θ.networks.a) (Δ_u θ.networks.c)
def 𝓑_r (θ : Θ n q r m p) : ℝ≥0∞ := θ.witnesses.B_r θ.nominal θ.W_r θ.V_r

def 𝓛_pred (θ : Θ n q r m p) (F : Rn n → Rn m → Rn n)
    (x₀ : Fin N → Rn n) (u : Fin N → ℕ → Rn m) (H : ℕ) : ℝ :=
  L_pred θ.nominal θ.C_x F x₀ u θ.networks H

theorem reconstruction (θ : Θ n q r m p) : (∀ x, act θ.C_x (θ.Φ x)=x) ∧ θ.Φ 0=0 := by
  let Φ₀ : Rn n → Rn q := fun x => act (C_x_dagger θ.C_x) x
  have hΦ₀ (x : Rn n) : act θ.C_x (Φ₀ x)=x := by
    simp only [Φ₀,← act_mul,θ.reconstruction_inverse,act_one]
  exact neural_lifting_identities θ.C_x Φ₀ hΦ₀ θ.networks.ψ

theorem continuous_Φ (θ : Θ n q r m p) : Continuous θ.Φ := continuous_Φ_θ θ.C_x θ.networks.ψ

theorem continuous_F_tilde (θ : Θ n q r m p) :
    Continuous (fun v : Rn q×Rn m => θ.F_tilde v.1 v.2) := by
  have hA := (Matrix.toEuclideanLin θ.nominal.A).continuous_of_finiteDimensional
  have hBu := (Matrix.toEuclideanLin θ.nominal.B_u).continuous_of_finiteDimensional
  have hBdu := (Matrix.toEuclideanLin θ.nominal.B_δu).continuous_of_finiteDimensional
  have hBdz := (Matrix.toEuclideanLin θ.nominal.B_δz).continuous_of_finiteDimensional
  exact ((hA.comp continuous_fst).add (hBu.comp continuous_snd)).add
    (hBdu.comp (continuous_Δ_u θ.networks.c)) |>.add
      (hBdz.comp ((continuous_Δ_z θ.networks.a).comp continuous_fst))

theorem F_tilde_eq_driven (θ : Θ n q r m p) : θ.F_tilde=
    drivenUpdate θ.nominal (1 : Mat q q) (Δ_z θ.networks.a) (Δ_u θ.networks.c) := by
  funext z u
  simp [F_tilde,neuralUpdate,NominalMatrices.fullUpdate,drivenUpdate]

theorem F_hat_eq_driven (θ : Θ n q r m p) : θ.F_hat=
    drivenUpdate (θ.nominal.reduced θ.W_r θ.V_r) θ.V_r (Δ_z θ.networks.a) (Δ_u θ.networks.c) := by
  funext z u
  exact θ.nominal.reducedUpdate_eq θ.W_r θ.V_r (Δ_z θ.networks.a) (Δ_u θ.networks.c) z u

theorem 𝒢_eq_actual_output (θ : Θ n q r m p) (u : ℕ → Rn m) (k : ℕ) :
    θ.𝒢 u k=act θ.nominal.C (rollout θ.F_tilde 0 u k) := by
  rw [θ.F_tilde_eq_driven]
  rfl

theorem 𝒢_hat_eq_actual_output (θ : Θ n q r m p) (u : ℕ → Rn m) (k : ℕ) :
    θ.𝒢_hat u k=act (θ.nominal.C*θ.V_r) (rollout θ.F_hat 0 u k) := by
  rw [θ.F_hat_eq_driven]
  rfl

end Θ

/-- Definition 3, with stronger exponential-stability conclusions retained.
The certificate is the same map for every member of the universal family. -/
def IsReductionCertificate (B_r : Θ n q r m p → ℝ≥0∞) : Prop :=
  ∀ θ, B_r θ≠⊤ → ReductionGuarantees θ.𝒢 θ.𝒢_hat
    (fun z => θ.F_tilde z 0) (fun z => θ.F_hat z 0) (B_r θ)

theorem neural_family_certificate [NeZero q] [NeZero r] :
    IsReductionCertificate (Θ.𝓑_r : Θ n q r m p → ℝ≥0∞) := by
  intro θ hfinite
  rw [θ.F_tilde_eq_driven,θ.F_hat_eq_driven]
  exact certified_nonlinear_state_reduction θ.nominal θ.W_r θ.V_r θ.witnesses hfinite
    (Δ_z θ.networks.a) (Δ_z θ.networks.a) (Δ_u θ.networks.c) (Δ_u θ.networks.c)
    (norm_Δ_z_le θ.networks.a) (norm_Δ_u_le θ.networks.c)
    (norm_Δ_z_le θ.networks.a) (norm_Δ_u_le θ.networks.c)

end
end Populus.ModelReduction.Certified
