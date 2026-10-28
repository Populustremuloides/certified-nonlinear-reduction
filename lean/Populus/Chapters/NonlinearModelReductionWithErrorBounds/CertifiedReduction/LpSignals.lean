import Populus.Chapters.NonlinearModelReductionWithErrorBounds.CertifiedReduction.SequenceNorm
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# Actual finite-energy signals as a Hilbert space

This adapter does not change the paper's norm or input domain. It identifies
the already-defined square-summable sequences with Mathlib's Hilbert `lp 2`
space, for the strict bounded-real witness existence argument.
-/
namespace Populus.ModelReduction.Certified
open scoped ENNReal
noncomputable section
variable {E : Type*} [NormedAddCommGroup E]

abbrev L2 (E : Type*) [NormedAddCommGroup E] := lp (fun _ : ℕ => E) 2

theorem finiteEnergy_iff_memℓp (z : ℕ → E) : FiniteEnergy z ↔ Memℓp z 2 := by
  have hp : 0<(2 : ℝ≥0∞).toReal := by norm_num
  rw [memℓp_gen_iff hp]
  norm_num [FiniteEnergy,Real.rpow_natCast]

def toL2 (z : ℕ → E) (hz : FiniteEnergy z) : L2 E := ⟨z,(finiteEnergy_iff_memℓp z).1 hz⟩

@[simp] theorem toL2_apply (z : ℕ → E) (hz : FiniteEnergy z) (k : ℕ) : toL2 z hz k=z k := rfl

theorem L2.finiteEnergy (z : L2 E) : FiniteEnergy (fun k => z k) :=
  (finiteEnergy_iff_memℓp _).2 z.prop

theorem L2.norm_sq_eq_energy (z : L2 E) : ‖z‖^2=energy (fun k => z k) := by
  have h := lp.norm_rpow_eq_tsum (by norm_num : 0<(2 : ℝ≥0∞).toReal) z
  simpa only [ENNReal.toReal_ofNat,Real.rpow_two,energy] using h

theorem L2.norm_eq_sqrt_energy (z : L2 E) : ‖z‖=Real.sqrt (energy (fun k => z k)) := by
  rw [← L2.norm_sq_eq_energy,Real.sqrt_sq (norm_nonneg _)]

theorem L2.ℓ₂_eq_norm (z : L2 E) : ℓ₂ (fun k => z k)=ENNReal.ofReal ‖z‖ := by
  rw [ℓ₂_eq_of_finiteEnergy _ (L2.finiteEnergy z),← L2.norm_eq_sqrt_energy z]

def prependSignal (x : E) (z : ℕ → E) : ℕ → E
  | 0 => x
  | k+1 => z k

/-- Prepending a finite initial sample preserves finite energy. -/
theorem prepend_finiteEnergy (x : E) (z : ℕ → E) (hz : FiniteEnergy z) :
    FiniteEnergy (prependSignal x z) := by
  apply (summable_nat_add_iff 1).1
  simpa [FiniteEnergy,prependSignal,Nat.add_comm] using hz

/-- Exact energy decomposition for a prepended sample. -/
theorem energy_prepend (x : E) (z : ℕ → E) (hz : FiniteEnergy z) :
    energy (prependSignal x z)=‖x‖^2+energy z := by
  have h := (prepend_finiteEnergy x z hz).tsum_eq_zero_add
  simpa [energy,prependSignal] using h

def L2.prepend (x : E) (z : L2 E) : L2 E := toL2 (prependSignal x (fun k => z k))
  (prepend_finiteEnergy x _ (L2.finiteEnergy z))

@[simp] theorem L2.prepend_zero (x : E) (z : L2 E) : L2.prepend x z 0=x := rfl
@[simp] theorem L2.prepend_succ (x : E) (z : L2 E) (k : ℕ) : L2.prepend x z (k+1)=z k := rfl

theorem L2.norm_prepend_sq (x : E) (z : L2 E) : ‖L2.prepend x z‖^2=‖x‖^2+‖z‖^2 := by
  rw [L2.norm_sq_eq_energy,L2.norm_sq_eq_energy]
  exact energy_prepend x _ (L2.finiteEnergy z)

end
end Populus.ModelReduction.Certified
