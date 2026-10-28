import Populus.Chapters.NonlinearModelReductionWithErrorBounds.CertifiedReduction.NominalError

/-!
# Euclidean concatenation and zero injection columns

Finite sums and Euclidean norms are preserved literally. These definitions
use Fin-indexed matrices so they share the exact signal/channel types used
by the rest of the paper formalization.
-/
namespace Populus.ModelReduction.Certified
open scoped BigOperators ENNReal
noncomputable section
variable {q a b c : ℕ}

def join (x : Rn a) (y : Rn b) : Rn (a+b) := WithLp.toLp 2 (Fin.addCases x y)
def take (x : Rn (a+b)) : Rn a := WithLp.toLp 2 (fun i => x (Fin.castAdd b i))
def drop (x : Rn (a+b)) : Rn b := WithLp.toLp 2 (fun i => x (Fin.natAdd a i))

@[simp] theorem take_join (x : Rn a) (y : Rn b) : take (join x y)=x := by ext i; simp [take,join]
@[simp] theorem drop_join (x : Rn a) (y : Rn b) : drop (join x y)=y := by ext i; simp [drop,join]
@[simp] theorem take_smul (t : ℝ) (x : Rn (a+b)) : take (t • x)=t • take x := by ext i; rfl
@[simp] theorem take_zero : take (0 : Rn (a+b))=(0 : Rn a) := by ext i; rfl

/-- The actual Euclidean squared norm, not the product supremum norm. -/
theorem norm_join_sq (x : Rn a) (y : Rn b) : ‖join x y‖^2=‖x‖^2+‖y‖^2 := by
  simp only [EuclideanSpace.real_norm_sq_eq,Real.norm_eq_abs,sq_abs]
  simp [join,Fin.sum_univ_add]

theorem join_take_drop (x : Rn (a+b)) : join (take x) (drop x)=x := by
  ext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [join,take,drop]

theorem norm_take_le (x : Rn (a+b)) : ‖take x‖≤‖x‖ := by
  have h := norm_join_sq (take x) (drop x)
  rw [join_take_drop] at h
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 (by nlinarith [sq_nonneg ‖drop x‖])

@[simp] theorem norm_join_zero (x : Rn a) : ‖join x (0 : Rn b)‖=‖x‖ := by
  have h := norm_join_sq x (0 : Rn b)
  simp only [norm_zero,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,zero_pow,add_zero] at h
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h

/-- Literal `[B 0]`, with `b` appended zero columns. -/
def zeroExtension (B : Mat q a) (b : ℕ) : Mat q (a+b) :=
  fun i => Fin.addCases (B i) (fun _ => 0)

@[simp] theorem act_zeroExtension (B : Mat q a) (x : Rn (a+b)) :
    act (zeroExtension B b) x=act B (take x) := by
  ext i
  simp [act,Matrix.toEuclideanLin,Matrix.mulVec,dotProduct,zeroExtension,take,Fin.sum_univ_add]

/-- Appending zero columns preserves exactly the Gramian injection product. -/
theorem zeroExtension_gram (B : Mat q a) (b : ℕ) :
    zeroExtension B b*(zeroExtension B b).transpose=B*B.transpose := by
  ext i j
  simp [Matrix.mul_apply,Matrix.transpose_apply,zeroExtension,Fin.sum_univ_add]

/-- All actual nominal responses of the extended injection ignore its zero
columns, rather than merely satisfying a presumed gain relation. -/
theorem zeroExtension_response (A : Mat q q) (B : Mat q a) (u : ℕ → Rn (a+b)) (k : ℕ) :
    linearResponse A (zeroExtension B b) u k=linearResponse A B (fun j => take (u j)) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change act A (linearResponse A (zeroExtension B b) u k)+act (zeroExtension B b) (u k)=_
    rw [ih,act_zeroExtension]
    rfl

theorem ℓ₂_mono_of_norm_le {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    (x : ℕ → E) (y : ℕ → F) (h : ∀ k, ‖x k‖≤‖y k‖) : ℓ₂ x≤ℓ₂ y := by
  apply iSup_le
  intro K
  exact (ENNReal.ofReal_le_ofReal (prefixNorm_mono _ _ h K)).trans (le_iSup (fun N => ENNReal.ofReal (prefixNorm y N)) K)

theorem take_finiteEnergy (u : ℕ → Rn (a+b)) (hu : FiniteEnergy u) :
    FiniteEnergy (fun k => take (u k)) := by
  exact Summable.of_nonneg_of_le (fun k => sq_nonneg _) (fun k =>
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 (norm_take_le _)) hu

@[simp] theorem ℓ₂_join_zero (u : ℕ → Rn a) : ℓ₂ (fun k => join (u k) (0 : Rn b))=ℓ₂ u := by
  simp only [ℓ₂,prefixNorm,prefixEnergy,norm_join_zero]

theorem join_zero_finiteEnergy (u : ℕ → Rn a) (hu : FiniteEnergy u) :
    FiniteEnergy (fun k => join (u k) (0 : Rn b)) := by
  simpa only [FiniteEnergy,norm_join_zero] using hu

/-- Zero injection columns preserve the actual induced gain, including the
possibility of an infinite gain for a non-Schur nominal realization. -/
theorem zeroExtension_channel_gain (A : Mat q q) (B : Mat q a) (O : Mat c q) (b : ℕ) :
    channelGain A (zeroExtension B b) O=channelGain A B O := by
  apply le_antisymm
  · unfold channelGain
    refine iSup_le (fun u => iSup_le (fun hu => iSup_le (fun hne => ?_)))
    let v : ℕ → Rn a := fun k => take (u k)
    have hv : FiniteEnergy v := take_finiteEnergy u hu
    have hresp : (fun k => act O (linearResponse A (zeroExtension B b) u k))=
        fun k => act O (linearResponse A B v k) := by
      funext k
      rw [zeroExtension_response]
    rw [hresp]
    by_cases hv0 : v=fun _ => 0
    · simp [hv0,linearResponse_zero,ℓ₂,prefixNorm,prefixEnergy]
    · have hden : ℓ₂ v≤ℓ₂ u := ℓ₂_mono_of_norm_le v u (fun k => norm_take_le _)
      calc
        _ ≤ ℓ₂ (fun k => act O (linearResponse A B v k))/ℓ₂ v := ENNReal.div_le_div_left hden _
        _ ≤ channelGain A B O := by
          unfold channelGain
          exact le_iSup_of_le v (le_iSup_of_le hv (le_iSup_of_le hv0 le_rfl))
  · unfold channelGain
    refine iSup_le (fun u => iSup_le (fun hu => iSup_le (fun hne => ?_)))
    let v : ℕ → Rn (a+b) := fun k => join (u k) 0
    have hv : FiniteEnergy v := join_zero_finiteEnergy u hu
    have hvne : v≠fun _ => 0 := by
      intro hv0
      apply hne
      funext k
      have h := congrArg (fun z : ℕ → Rn (a+b) => take (z k)) hv0
      simpa [v] using h
    have hresp : (fun k => act O (linearResponse A (zeroExtension B b) v k))=
        fun k => act O (linearResponse A B u k) := by
      funext k
      rw [zeroExtension_response]
      simp [v]
    have hratio : ℓ₂ (fun k => act O (linearResponse A B u k))/ℓ₂ u=
        ℓ₂ (fun k => act O (linearResponse A (zeroExtension B b) v k))/ℓ₂ v := by
      rw [hresp]
      simp [v]
    rw [hratio]
    exact le_iSup_of_le v (le_iSup_of_le hv (le_iSup_of_le hvne le_rfl))

end
end Populus.ModelReduction.Certified
