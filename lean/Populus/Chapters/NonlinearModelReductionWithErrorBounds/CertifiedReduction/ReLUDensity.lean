import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

/-!
# Finite ReLU coefficient networks and uniform approximation

Paper: Appendix A (`lem:fixed-envelope`, `prop:density`) and Appendix E.
The coefficient language below has only affine scalar gates and ReLU gates.
An expression is a finite feedforward computation, not an arbitrary continuous
function or a network-density assumption. A vector network has finitely many
such outputs. Max/min are explicitly realized with ReLU, and the lattice
Stone--Weierstrass theorem supplies density on an arbitrary compact set.
-/

namespace Populus.ModelReduction.Certified
noncomputable section

abbrev Rn (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- Finite feedforward ReLU computation with affine output gates. -/
inductive ReLUExpr (n : ℕ) where
  | const : ℝ → ReLUExpr n
  | coord : Fin n → ReLUExpr n
  | add : ReLUExpr n → ReLUExpr n → ReLUExpr n
  | smul : ℝ → ReLUExpr n → ReLUExpr n
  | relu : ReLUExpr n → ReLUExpr n

namespace ReLUExpr

def eval {n : ℕ} : ReLUExpr n → Rn n → ℝ
  | .const c, _ => c
  | .coord i, x => x i
  | .add f g, x => f.eval x + g.eval x
  | .smul c f, x => c * f.eval x
  | .relu f, x => max (f.eval x) 0

theorem continuous_eval {n : ℕ} (e : ReLUExpr n) : Continuous e.eval := by
  induction e with
  | const => exact continuous_const
  | coord i => exact (EuclideanSpace.proj i).continuous
  | add f g hf hg => exact hf.add hg
  | smul c f hf => exact continuous_const.mul hf
  | relu f hf => exact hf.max continuous_const

def maximum {n : ℕ} (f g : ReLUExpr n) : ReLUExpr n :=
  .add g (.relu (.add f (.smul (-1) g)))

def minimum {n : ℕ} (f g : ReLUExpr n) : ReLUExpr n :=
  .add f (.smul (-1) (.relu (.add f (.smul (-1) g))))

@[simp] theorem eval_maximum {n : ℕ} (f g : ReLUExpr n) (x : Rn n) :
    (maximum f g).eval x = max (f.eval x) (g.eval x) := by
  change g.eval x + max (f.eval x + -1 * g.eval x) 0 = _
  by_cases h : f.eval x ≤ g.eval x
  · rw [max_eq_right (by linarith), max_eq_right h]; ring
  · rw [max_eq_left (by linarith), max_eq_left (by linarith)]; ring

@[simp] theorem eval_minimum {n : ℕ} (f g : ReLUExpr n) (x : Rn n) :
    (minimum f g).eval x = min (f.eval x) (g.eval x) := by
  change f.eval x + -1 * max (f.eval x + -1 * g.eval x) 0 = _
  by_cases h : f.eval x ≤ g.eval x
  · rw [max_eq_right (by linarith), min_eq_left h]; ring
  · rw [max_eq_left (by linarith), min_eq_right (by linarith)]; ring

/-- Restrict an actual finite network to the compact approximation domain. -/
def restrict {n : ℕ} (K : Set (Rn n)) (e : ReLUExpr n) : C(K, ℝ) :=
  ⟨fun x => e.eval x, e.continuous_eval.comp continuous_subtype_val⟩

def restrictions {n : ℕ} (K : Set (Rn n)) : Set C(K, ℝ) := Set.range (restrict K)

/-- Affine coefficient networks interpolate any two input points, exactly. -/
theorem restrictions_separate_strongly {n : ℕ} (K : Set (Rn n)) :
    (restrictions K).SeparatesPointsStrongly := by
  intro v x y
  by_cases hxy : x = y
  · refine ⟨restrict K (.const (v x)), ⟨.const (v x), rfl⟩, rfl, ?_⟩
    simpa [hxy] using (show (restrict K (.const (v x))) x = v x from rfl)
  · have hd : ∃ i : Fin n, (x : Rn n) i ≠ (y : Rn n) i := by
      by_contra h
      push Not at h
      apply hxy
      apply Subtype.ext
      ext i
      exact h i
    obtain ⟨i, hi⟩ := hd
    let a : ℝ := (v x - v y) / ((x : Rn n) i - (y : Rn n) i)
    let b : ℝ := v x - a * (x : Rn n) i
    let e : ReLUExpr n := .add (.smul a (.coord i)) (.const b)
    refine ⟨restrict K e, ⟨e, rfl⟩, ?_, ?_⟩
    · dsimp [restrict, e, eval, b]; ring
    · dsimp [restrict, e, eval, b, a]
      field_simp [sub_ne_zero.mpr hi]
      <;> ring

/-- The scalar ReLU density theorem, with no activation-density hypothesis. -/
theorem uniform_scalar_relu_approximation {n : ℕ}
    (K : Set (Rn n)) (hK : IsCompact K) (f : C(K, ℝ))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ e : ReLUExpr n, ∀ x : K, |e.eval x - f x| < ε := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hnonempty : (restrictions K).Nonempty := ⟨restrict K (.const 0), ⟨.const 0, rfl⟩⟩
  have hinf : ∀ f ∈ restrictions K, ∀ g ∈ restrictions K, f ⊓ g ∈ restrictions K := by
    rintro f ⟨e, rfl⟩ g ⟨d, rfl⟩
    refine ⟨minimum e d, ?_⟩
    ext x
    exact eval_minimum e d x
  have hsup : ∀ f ∈ restrictions K, ∀ g ∈ restrictions K, f ⊔ g ∈ restrictions K := by
    rintro f ⟨e, rfl⟩ g ⟨d, rfl⟩
    refine ⟨maximum e d, ?_⟩
    ext x
    exact eval_maximum e d x
  have hdense := ContinuousMap.sublattice_closure_eq_top (restrictions K)
    hnonempty hinf hsup (restrictions_separate_strongly K)
  have hf : f ∈ closure (restrictions K) := by rw [hdense]; trivial
  obtain ⟨g, ⟨e, rfl⟩, hg⟩ := Metric.mem_closure_iff.1 hf ε hε
  refine ⟨e, fun x => ?_⟩
  have hpoint : dist ((restrict K e) x) (f x) ≤ dist (restrict K e) f :=
    ContinuousMap.dist_apply_le_dist x
  exact lt_of_le_of_lt (by simpa [Real.dist_eq, restrict] using hpoint)
    (by simpa [dist_comm] using hg)

end ReLUExpr

/-- A finite-output coefficient network. All nonlinear gates are ReLU. -/
abbrev ReLUNetwork (n p : ℕ) := Fin p → ReLUExpr n

def ReLUNetwork.eval {n p : ℕ} (N : ReLUNetwork n p) (x : Rn n) : Rn p :=
  WithLp.toLp 2 (fun i => (N i).eval x)

/-- Subtype-domain form: the continuous target need only exist on the compact
set, as in the paper's fixed-envelope lemma. -/
theorem uniform_vector_relu_approximation_on_compact {n p : ℕ}
    (K : Set (Rn n)) (hK : IsCompact K) (f : C(K, Rn p))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ReLUNetwork n p, ∀ x : K, ‖N.eval x - f x‖ < ε := by
  let δ : ℝ := ε / ((p : ℝ) + 1)
  have hp : 0 ≤ (p : ℝ) := Nat.cast_nonneg p
  have hδ : 0 < δ := div_pos hε (by linarith)
  let g (i : Fin p) : C(K, ℝ) :=
    ⟨fun x => f x i, (EuclideanSpace.proj i).continuous.comp f.continuous⟩
  have hcoord (i : Fin p) := ReLUExpr.uniform_scalar_relu_approximation K hK (g i) δ hδ
  choose N hN using hcoord
  refine ⟨N, fun x => ?_⟩
  have heach (i : Fin p) : |(N i).eval x - f x i| ≤ δ := (hN i x).le
  have hs : ‖ReLUNetwork.eval N x - f x‖ ^ 2 ≤ (p : ℝ) * δ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc
      _ ≤ ∑ i : Fin p, δ ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        simpa [ReLUNetwork.eval, Real.norm_eq_abs] using
          (sq_le_sq₀ (abs_nonneg _) hδ.le).mpr (heach i)
      _ = (p : ℝ) * δ ^ 2 := by simp
  have hcoef : (p : ℝ) < ((p : ℝ) + 1)^2 := by nlinarith [sq_nonneg (p : ℝ)]
  have hstrict := mul_lt_mul_of_pos_right hcoef (sq_pos_of_pos hδ)
  have hproduct : ((p : ℝ) + 1)^2 * δ ^ 2 = ε ^ 2 := by
    dsimp [δ]
    field_simp
  have hlt : ‖ReLUNetwork.eval N x - f x‖ ^ 2 < ε ^ 2 :=
    hs.trans_lt (by simpa [hproduct] using hstrict)
  nlinarith [norm_nonneg (ReLUNetwork.eval N x - f x)]

/-- Compact uniform Euclidean approximation by finite ReLU networks. -/
theorem uniform_vector_relu_approximation {n p : ℕ}
    (K : Set (Rn n)) (hK : IsCompact K) (f : Rn n → Rn p)
    (hf : ContinuousOn f K) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ReLUNetwork n p, ∀ x ∈ K, ‖N.eval x - f x‖ < ε := by
  let δ : ℝ := ε / ((p : ℝ) + 1)
  have hp : 0 ≤ (p : ℝ) := Nat.cast_nonneg p
  have hδ : 0 < δ := div_pos hε (by linarith)
  let g (i : Fin p) : C(K, ℝ) :=
    ⟨fun x => f x i, ((EuclideanSpace.proj i).continuous.comp_continuousOn hf).restrict⟩
  have hcoord (i : Fin p) := ReLUExpr.uniform_scalar_relu_approximation K hK (g i) δ hδ
  choose N hN using hcoord
  refine ⟨N, fun x hx => ?_⟩
  have heach (i : Fin p) : |(N i).eval x - f x i| ≤ δ := (hN i ⟨x,hx⟩).le
  have hs : ‖ReLUNetwork.eval N x - f x‖ ^ 2 ≤ (p : ℝ) * δ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc
      _ ≤ ∑ i : Fin p, δ ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        simpa [ReLUNetwork.eval, Real.norm_eq_abs] using
          (sq_le_sq₀ (abs_nonneg _) hδ.le).mpr (heach i)
      _ = (p : ℝ) * δ ^ 2 := by simp
  have hcoef : (p : ℝ) < ((p : ℝ) + 1)^2 := by nlinarith [sq_nonneg (p : ℝ)]
  have hstrict := mul_lt_mul_of_pos_right hcoef (sq_pos_of_pos hδ)
  have hproduct : ((p : ℝ) + 1)^2 * δ ^ 2 = ε ^ 2 := by
    dsimp [δ]
    field_simp
  have hlt : ‖ReLUNetwork.eval N x - f x‖ ^ 2 < ε ^ 2 :=
    hs.trans_lt (by simpa [hproduct] using hstrict)
  nlinarith [norm_nonneg (ReLUNetwork.eval N x - f x)]

end
end Populus.ModelReduction.Certified
