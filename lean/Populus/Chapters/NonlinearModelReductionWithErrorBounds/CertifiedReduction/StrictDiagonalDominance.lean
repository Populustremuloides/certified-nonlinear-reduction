import Populus.Chapters.NonlinearModelReductionWithErrorBounds.CertifiedReduction.MatrixStorage
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Exact positive-definiteness certificates by strict diagonal dominance

Numerical preprocessing may propose a congruence, but the final premises are
finite exact inequalities. This theorem supplies their analytic implication.
-/
namespace Populus.ModelReduction.Certified
open scoped BigOperators
noncomputable section
variable {n : Type*} [Fintype n] [DecidableEq n]

def offAbs (M : Matrix n n ℝ) (i j : n) : ℝ := if i=j then 0 else |M i j|

theorem offAbs_symm (M : Matrix n n ℝ) (hs : M.transpose=M) (i j : n) :
    offAbs M i j=offAbs M j i := by
  have hij : M i j=M j i := by
    exact (congrArg (fun A : Matrix n n ℝ => A j i) hs)
  by_cases he : i=j
  · subst j
    rfl
  · simp [offAbs,he,Ne.symm he,hij]

theorem quadratic_term_lower_bound (a x y : ℝ) :
    - |a| *(x^2+y^2)≤2*x*a*y := by
  have h := neg_abs_le (x*a*y)
  have habs : |x*a*y|=|a| *|x| *|y| := by rw [abs_mul,abs_mul]; ring
  rw [habs] at h
  have hxy := sq_nonneg (|x|-|y|)
  have hxabs : |x|^2=x^2 := sq_abs x
  have hyabs : |y|^2=y^2 := sq_abs y
  have hxy2 : 2*|x| *|y|≤x^2+y^2 := by nlinarith
  have hm := mul_le_mul_of_nonneg_left hxy2 (abs_nonneg a)
  nlinarith


theorem symmetric_quadratic_lower_bound (M : Matrix n n ℝ) (hs : M.transpose=M) (x : n → ℝ) :
    (∑ i, (M i i-∑ j,offAbs M i j)*(x i)^2)≤
      dotProduct x (Matrix.mulVec M x) := by
  have hterm (i j : n) :
      (if i=j then 2*M i i*(x i)^2 else -offAbs M i j*((x i)^2+(x j)^2))≤
        2*x i*M i j*x j := by
    by_cases hij : i=j
    · subst j
      simp only [if_pos rfl]
      ring_nf
      exact le_rfl
    · simp only [if_neg hij,offAbs,if_neg hij]
      exact quadratic_term_lower_bound _ _ _
  have hsum := Finset.sum_le_sum (fun i (_ : i∈Finset.univ) =>
    Finset.sum_le_sum (fun j (_ : j∈Finset.univ) => hterm i j))
  have hsymmetric : (∑ i,∑ j,offAbs M i j*(x j)^2)=∑ i,∑ j,offAbs M i j*(x i)^2 := by
    rw [Finset.sum_comm]
    congr 1
    ext i
    congr 1
    ext j
    rw [offAbs_symm M hs]
  have hleft : (∑ i,∑ j,if i=j then 2*M i i*(x i)^2 else
      -offAbs M i j*((x i)^2+(x j)^2))=
        2*(∑ i,(M i i-∑ j,offAbs M i j)*(x i)^2) := by
    have hsplit (i j : n) : (if i=j then 2*M i i*(x i)^2 else
        -offAbs M i j*((x i)^2+(x j)^2))=
      (if i=j then 2*M i i*(x i)^2 else 0)-
        offAbs M i j*(x i)^2-offAbs M i j*(x j)^2 := by
      by_cases hij : i=j
      · subst j
        simp [offAbs]
      · simp only [if_neg hij]
        ring
    simp_rw [hsplit]
    simp_rw [Finset.sum_sub_distrib]
    rw [hsymmetric]
    simp only [Finset.sum_ite_eq,Finset.mem_univ,if_true]
    simp_rw [← Finset.sum_mul]
    simp_rw [← Finset.sum_sub_distrib]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hright : (∑ i,∑ j,2*x i*M i j*x j)=2*dotProduct x (Matrix.mulVec M x) := by
    simp only [dotProduct,Matrix.mulVec]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hleft,hright] at hsum
  linarith

theorem posDef_of_strict_diagonal_dominance (M : Matrix n n ℝ)
    (hs : M.transpose=M) (hdom : ∀ i, ∑ j,offAbs M i j<M i i) : M.PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · simpa only [Matrix.IsHermitian,Matrix.conjTranspose,star_trivial] using hs
  · intro x hx
    have hne : ∃ i, x i≠0 := by
      by_contra hn
      apply hx
      funext i
      exact Classical.byContradiction (fun hi => hn ⟨i,hi⟩)
    obtain ⟨i,hi⟩ := hne
    have hnonneg (j : n) : 0≤(M j j-∑ k,offAbs M j k)*(x j)^2 :=
      mul_nonneg (sub_nonneg.2 (hdom j).le) (sq_nonneg _)
    have hpos : 0<(M i i-∑ j,offAbs M i j)*(x i)^2 :=
      mul_pos (sub_pos.2 (hdom i)) (sq_pos_of_ne_zero hi)
    have hsum : 0<∑ j,(M j j-∑ k,offAbs M j k)*(x j)^2 :=
      (Finset.sum_pos_iff_of_nonneg (fun j _ => hnonneg j)).2 ⟨i,Finset.mem_univ i,hpos⟩
    simpa only [star_trivial] using hsum.trans_le (symmetric_quadratic_lower_bound M hs x)

/-- A proposed congruence need not come with an assumed inverse. Positivity
of the checked congruence itself forces that inverse to exist. -/
theorem posDef_of_congruence_posDef (M R : Matrix n n ℝ)
    (h : (R.transpose*M*R).PosDef) : M.PosDef := by
  have hd : (R.transpose*M*R).det≠0 := by
    exact isUnit_iff_ne_zero.1 ((Matrix.isUnit_iff_isUnit_det _).1 h.isUnit)
  have hRdet : R.det≠0 := by
    intro hz
    apply hd
    simp only [Matrix.det_mul,Matrix.det_transpose,hz,zero_mul,mul_zero]
  have hR : IsUnit R := (Matrix.isUnit_iff_isUnit_det R).2 (isUnit_iff_ne_zero.2 hRdet)
  apply (Matrix.IsUnit.posDef_star_left_conjugate_iff hR).1
  simpa only [Matrix.star_eq_conjTranspose,Matrix.conjTranspose,star_trivial] using h

/-- Only finite exact equalities and strict row inequalities remain after
this supporting theorem. Numerical code may suggest R and S but cannot
supply the analytic conclusion without checking these premises. -/
theorem posDef_of_checked_diagonal_congruence (M R S : Matrix n n ℝ)
    (hproduct : R.transpose*M*R=S) (hs : S.transpose=S)
    (hdom : ∀ i,∑ j,offAbs S i j<S i i) : M.PosDef := by
  apply posDef_of_congruence_posDef M R
  rw [hproduct]
  exact posDef_of_strict_diagonal_dominance S hs hdom

end
end Populus.ModelReduction.Certified
