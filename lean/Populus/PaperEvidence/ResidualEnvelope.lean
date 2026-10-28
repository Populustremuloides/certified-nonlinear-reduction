import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-!
# Residual-envelope contract for the frozen MEMS implementation

Exact-real statements only. No Python or IEEE floating-point semantics are
assumed to have been verified by compiling this file. See the evidence card
`residual-envelope` for the reviewed tensor/coordinate interpretation.
-/

namespace Populus.PaperEvidence.ModelReduction

noncomputable section

abbrev Rn (n : ℕ) := EuclideanSpace ℝ (Fin n)

def append {α β : Type*} [Fintype α] [Fintype β]
    (a : EuclideanSpace ℝ α) (b : EuclideanSpace ℝ β) :
    EuclideanSpace ℝ (α ⊕ β) :=
  WithLp.toLp 2 (Sum.elim a b)

theorem norm_append_sq {α β : Type*} [Fintype α] [Fintype β]
    (a : EuclideanSpace ℝ α) (b : EuclideanSpace ℝ β) :
    ‖append a b‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2 := by
  simp [EuclideanSpace.real_norm_sq_eq, append, Fintype.sum_sum_type]

/-- The radial projection printed in equation `eq:neural`. -/
def rad {p : ℕ} (a : Rn p) : Rn p := (max 1 ‖a‖)⁻¹ • a

theorem norm_rad_le_one {p : ℕ} (a : Rn p) : ‖rad a‖ ≤ 1 := by
  have hd : 0 < max (1 : ℝ) ‖a‖ := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  rw [rad, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hd)]
  calc
    (max 1 ‖a‖)⁻¹ * ‖a‖ ≤ (max 1 ‖a‖)⁻¹ * max 1 ‖a‖ :=
      mul_le_mul_of_nonneg_left (le_max_right _ _) (le_of_lt (inv_pos.mpr hd))
    _ = 1 := inv_mul_cancel₀ (ne_of_gt hd)

def Δ_z_rad {q p_z : ℕ} (a : Rn q → Rn p_z) (z : Rn q) : Rn p_z := ‖z‖ • rad (a z)
def Δ_u_rad {q m p_u : ℕ} (c : Rn q → Rn m → Rn p_u) (z : Rn q) (u : Rn m) : Rn p_u :=
  ‖u‖ • rad (c z u)

theorem norm_Δ_z_rad_le {q p_z : ℕ} (a : Rn q → Rn p_z) (z : Rn q) :
    ‖Δ_z_rad a z‖ ≤ ‖z‖ := by
  simpa [Δ_z_rad, norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg z)] using
    mul_le_mul_of_nonneg_left (norm_rad_le_one (a z)) (norm_nonneg z)

theorem norm_Δ_u_rad_le {q m p_u : ℕ} (c : Rn q → Rn m → Rn p_u) (z : Rn q) (u : Rn m) :
    ‖Δ_u_rad c z u‖ ≤ ‖u‖ := by
  simpa [Δ_u_rad, norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg u)] using
    mul_le_mul_of_nonneg_left (norm_rad_le_one (c z u)) (norm_nonneg u)

/-- Two groups of eight coefficients are the sixteen-output autonomous head. -/
abbrev AutCoefficients := EuclideanSpace ℝ (Fin 8 ⊕ Fin 8)
def prefix₈ (h : AutCoefficients) : Rn 8 := WithLp.toLp 2 (fun i => h (Sum.inl i))
def suffix (h : AutCoefficients) : Rn 8 := WithLp.toLp 2 (fun i => h (Sum.inr i))

theorem norm_prefix_le (h : AutCoefficients) : ‖prefix₈ h‖ ≤ ‖h‖ := by
  have hh : append (prefix₈ h) (suffix h) = h := by
    ext i
    cases i <;> rfl
  have hs := norm_append_sq (prefix₈ h) (suffix h)
  rw [hh] at hs
  nlinarith [norm_nonneg (prefix₈ h), norm_nonneg h, sq_nonneg ‖suffix h‖]

def denominator {α : Type*} [Fintype α] (h : EuclideanSpace ℝ α) : ℝ :=
  Real.sqrt (1 + ‖h‖ ^ 2)

theorem denominator_pos {α : Type*} [Fintype α] (h : EuclideanSpace ℝ α) :
    0 < denominator h := by
  unfold denominator
  positivity

theorem norm_le_denominator {α : Type*} [Fintype α] (h : EuclideanSpace ℝ α) :
    ‖h‖ ≤ denominator h := by
  have hs : denominator h ^ 2 = 1 + ‖h‖ ^ 2 := Real.sq_sqrt (by positivity)
  nlinarith [norm_nonneg h, le_of_lt (denominator_pos h)]

/-- The reservoir in `eq:reservoir`, evaluated at arbitrary coefficient and driving vectors. -/
def Ω {α β : Type*} [Fintype α] [Fintype β]
    (w : EuclideanSpace ℝ α) (h : EuclideanSpace ℝ β) : EuclideanSpace ℝ (β ⊕ α) :=
  (denominator h)⁻¹ • append (‖w‖ • h) w

theorem norm_Ω_eq {α β : Type*} [Fintype α] [Fintype β]
    (w : EuclideanSpace ℝ α) (h : EuclideanSpace ℝ β) : ‖Ω w h‖ = ‖w‖ := by
  have hd := denominator_pos h
  have hs : denominator h ^ 2 = 1 + ‖h‖ ^ 2 := Real.sq_sqrt (by positivity)
  have he := norm_append_sq (‖w‖ • h) w
  simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg w)] at he
  have ha : ‖append (‖w‖ • h) w‖ = ‖w‖ * denominator h := by
    have hn := norm_nonneg (append (‖w‖ • h) w)
    have hp : 0 ≤ ‖w‖ * denominator h := mul_nonneg (norm_nonneg w) (le_of_lt hd)
    nlinarith
  rw [Ω, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hd), ha]
  field_simp

/-- `nz*h[:,:8]/sqrt(1+sum(h*h))`, with the complete head in the denominator. -/
def autHead {q : ℕ} (z : Rn q) (h : AutCoefficients) : Rn 8 :=
  (‖z‖ / denominator h) • prefix₈ h

theorem norm_autHead_le {q : ℕ} (z : Rn q) (h : AutCoefficients) :
    ‖autHead z h‖ ≤ ‖z‖ := by
  have hd := denominator_pos h
  rw [autHead, norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg (norm_nonneg z) (le_of_lt hd))]
  calc
    ‖z‖ / denominator h * ‖prefix₈ h‖ ≤ ‖z‖ / denominator h * denominator h :=
      mul_le_mul_of_nonneg_left ((norm_prefix_le h).trans (norm_le_denominator h))
        (div_nonneg (norm_nonneg z) (le_of_lt hd))
    _ = ‖z‖ := div_mul_cancel₀ _ (ne_of_gt hd)

abbrev InputHead := EuclideanSpace ℝ (Fin 16 ⊕ Unit)
def scalar (u : ℝ) : EuclideanSpace ℝ Unit := WithLp.toLp 2 (fun _ => u)

@[simp] theorem norm_scalar (u : ℝ) : ‖scalar u‖ = |u| := by
  rw [EuclideanSpace.norm_eq]
  simp [scalar, Real.sqrt_sq_eq_abs]

/-- The seventeenth reservoir coordinate is the scalar input itself. -/
def inputHead (u : ℝ) (h : Rn 16) : InputHead :=
  (denominator h)⁻¹ • append (|u| • h) (scalar u)

theorem norm_inputHead_eq (u : ℝ) (h : Rn 16) : ‖inputHead u h‖ = |u| := by
  have hd := denominator_pos h
  have hs : denominator h ^ 2 = 1 + ‖h‖ ^ 2 := Real.sq_sqrt (by positivity)
  have ha : ‖append (|u| • h) (scalar u)‖ = |u| * denominator h := by
    have he := norm_append_sq (|u| • h) (scalar u)
    simp only [norm_smul, Real.norm_eq_abs, abs_abs, norm_scalar] at he
    have hn := norm_nonneg (append (|u| • h) (scalar u))
    have hp : 0 ≤ |u| * denominator h := mul_nonneg (abs_nonneg u) (le_of_lt hd)
    nlinarith [sq_nonneg (‖append (|u| • h) (scalar u)‖ - |u| * denominator h)]
  rw [inputHead, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hd), ha]
  field_simp

/-- The actual autonomous factor paired with the injection `2*K`. -/
def Δ_z {q : ℕ} (a₁ a₂ : Rn q → AutCoefficients) (z : Rn q) : Rn 8 :=
  (1 / 2 : ℝ) • (autHead z (a₁ z) + autHead z (a₂ z))

theorem norm_Δ_z_le {q : ℕ} (a₁ a₂ : Rn q → AutCoefficients) (z : Rn q) :
    ‖Δ_z a₁ a₂ z‖ ≤ ‖z‖ := by
  rw [Δ_z, norm_smul]
  norm_num
  have hsum := norm_add_le (autHead z (a₁ z)) (autHead z (a₂ z))
  have h₁ := norm_autHead_le z (a₁ z)
  have h₂ := norm_autHead_le z (a₂ z)
  linarith

/-- The actual control factor paired with `sqrt(2)*[P₁ P₂]`. -/
def Δ_u {q : ℕ} (c₁ c₂ : Rn q → ℝ → Rn 16) (z : Rn q) (u : ℝ) :
    EuclideanSpace ℝ ((Fin 16 ⊕ Unit) ⊕ (Fin 16 ⊕ Unit)) :=
  (Real.sqrt 2)⁻¹ • append (inputHead u (c₁ z u)) (inputHead u (c₂ z u))

theorem norm_Δ_u_eq {q : ℕ} (c₁ c₂ : Rn q → ℝ → Rn 16) (z : Rn q) (u : ℝ) :
    ‖Δ_u c₁ c₂ z u‖ = |u| := by
  have hd : 0 < Real.sqrt 2 := by positivity
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have he := norm_append_sq (inputHead u (c₁ z u)) (inputHead u (c₂ z u))
  rw [norm_inputHead_eq, norm_inputHead_eq] at he
  have ha : ‖append (inputHead u (c₁ z u)) (inputHead u (c₂ z u))‖ = |u| * Real.sqrt 2 := by
    have hn := norm_nonneg (append (inputHead u (c₁ z u)) (inputHead u (c₂ z u)))
    have hp : 0 ≤ |u| * Real.sqrt 2 := mul_nonneg (abs_nonneg u) (le_of_lt hd)
    nlinarith
  rw [Δ_u, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hd), ha]
  field_simp

theorem autonomous_scaling_cancel (d₁ d₂ : Rn 8) :
    (2 : ℝ) • ((1 / 2 : ℝ) • (d₁ + d₂)) = d₁ + d₂ := by
  rw [smul_smul]
  norm_num

theorem input_scaling_cancel (d : EuclideanSpace ℝ ((Fin 16 ⊕ Unit) ⊕ (Fin 16 ⊕ Unit))) :
    Real.sqrt 2 • ((Real.sqrt 2)⁻¹ • d) = d := by
  rw [smul_smul, mul_inv_cancel₀ (ne_of_gt (show 0 < Real.sqrt 2 by positivity)), one_smul]

#print axioms norm_Δ_z_rad_le
#print axioms norm_Δ_u_rad_le
#print axioms norm_Ω_eq
#print axioms norm_Δ_z_le
#print axioms norm_Δ_u_eq

end
end Populus.PaperEvidence.ModelReduction
