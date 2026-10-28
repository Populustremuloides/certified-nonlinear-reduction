import Populus.Chapters.NonlinearModelReductionWithErrorBounds.CertifiedReduction.ReductionWitnessExistence
import Populus.Chapters.NonlinearModelReductionWithErrorBounds.CertifiedReduction.Lifting

/-!
# The manuscript's exact gain-bounded reference class and feasibility

`𝓕_q` is a set in the explicit ambient space of physical updates. Its
membership witness contains precisely a continuous lifting, physical decoder,
continuous global residual factors, exact lifted identity and Schur nominal A.
A feasible projection adds the standing left-inverse relation, Schur reduced
A and the two strict actual state-channel margins, not desired neural fit or
matrix-witness existence. The latter is proved from these data.
-/
namespace Populus.ModelReduction.Certified
noncomputable section
variable {n q r m p : ℕ}

structure GainBoundedReference (n q m : ℕ) (F : Rn n → Rn m → Rn n) where
  p_u : ℕ
  p_z : ℕ
  nominal : NominalMatrices q m n p_u p_z
  Φ : Rn n → Rn q
  Δ_z : Rn q → Rn p_z
  Δ_u : Rn q → Rn m → Rn p_u
  continuous_F : Continuous (fun v : Rn n×Rn m => F v.1 v.2)
  continuous_Φ : Continuous Φ
  continuous_Δ_z : Continuous Δ_z
  continuous_Δ_u : Continuous (fun v : Rn q×Rn m => Δ_u v.1 v.2)
  Φ_zero : Φ 0=0
  reconstruct : ∀ x, act nominal.C (Φ x)=x
  envelope_z : ∀ z, ‖Δ_z z‖≤‖z‖
  envelope_u : ∀ z u, ‖Δ_u z u‖≤‖u‖
  identity : ∀ x u, nominal.fullUpdate Δ_z Δ_u (Φ x) u=Φ (F x u)
  schur : Schur nominal.A

def 𝓕_q (n q m : ℕ) : Set (Rn n → Rn m → Rn n) :=
  {F | Nonempty (GainBoundedReference n q m F)}

namespace GainBoundedReference

variable {F : Rn n → Rn m → Rn n}

/-- The physical output readout is applied after the exact decoder. Reference
membership itself is independent of the selected measured physical outputs. -/
def observedNominal (ρ : GainBoundedReference n q m F) (S_y : Mat p n) :
    NominalMatrices q m p ρ.p_u ρ.p_z where
  A := ρ.nominal.A
  B_u := ρ.nominal.B_u
  B_δu := ρ.nominal.B_δu
  B_δz := ρ.nominal.B_δz
  C := S_y*ρ.nominal.C

structure FeasibleProjection (ρ : GainBoundedReference n q m F) (r : ℕ) where
  W_r : Mat r q
  V_r : Mat q r
  left_inverse : W_r*V_r=1
  schur_reduced : Schur (ρ.nominal.reduced W_r V_r).A
  margin : (channelGain ρ.nominal.A ρ.nominal.B_δz (1 : Mat q q)).toReal<1
  margin_reduced : (channelGain (ρ.nominal.reduced W_r V_r).A
    (ρ.nominal.reduced W_r V_r).B_δz V_r).toReal<1

/-- The finite matrix witnesses required by the constructed certificate follow
from reference feasibility; they are not added to the definition of the class. -/
theorem matrix_witnesses [NeZero q] [NeZero r]
    (ρ : GainBoundedReference n q m F) (P : ρ.FeasibleProjection r) (S_y : Mat p n) :
    ∃ R : ReductionWitnesses q r, R.Valid (ρ.observedNominal S_y) P.W_r P.V_r :=
  reduction_matrix_witnesses_exist (ρ.observedNominal S_y) P.W_r P.V_r
    (reconstruction_injective_of_left_inverse P.W_r P.V_r P.left_inverse)
    ρ.schur P.schur_reduced P.margin P.margin_reduced

end GainBoundedReference

/-- Assumption 1: one of the reference representations admits a feasible
projection. No finite dataset is asserted to verify its global identity. -/
def ReferenceFeasible (F : Rn n → Rn m → Rn n) (q r : ℕ) : Prop :=
  ∃ ρ : GainBoundedReference n q m F, Nonempty (ρ.FeasibleProjection r)

end
end Populus.ModelReduction.Certified
