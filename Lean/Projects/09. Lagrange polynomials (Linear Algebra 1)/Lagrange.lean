import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Data.Nat.WithBot
import Mathlib.Data.Nat.Order.Lemmas
import Mathlib.Data.Nat.Count
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Finite
import Mathlib.LinearAlgebra.Basis
import Mathlib.Algebra.Group.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finsupp.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.LinearAlgebra.FiniteDimensional
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Monomial
import Mathlib.Algebra.Polynomial.Degree.Definitions
import Mathlib.LinearAlgebra.Dimension.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.SetTheory.Cardinal.Basic

variable {n : ℕ}(x : Fin (n + 1) → ℝ) (hx : Function.Injective x)

open Polynomial

noncomputable  def Monomials (i : Fin (n + 1)) : Polynomial ℝ := Polynomial.X ^ (i : ℕ)

noncomputable def LagrangePolynomials (i : Fin (n + 1)) : Polynomial ℝ :=
  ∏ j in {j | i ≠ j}, (Polynomial.C (x i - x j)⁻¹) * (Polynomial.X - Polynomial.C (x j))

noncomputable def Pn := Polynomial.degreeLT ℝ (n + 1)

--eventuell
theorem monomials_linear_independent :
  LinearIndependent ℝ (λ i : Fin (n + 1) ↦ Monomials i) := by
  sorry

theorem Monomials_in_Pn : ∀ i : Fin (n + 1), Monomials i ∈ Polynomial.degreeLT ℝ (n + 1) := by
  intro i
  rw [Monomials]
  rw [Polynomial.mem_degreeLT]
  rw [Polynomial.degree_X_pow]
  exact WithBot.coe_lt_coe.mpr (Fin.is_lt i)

--eventuell
theorem MonomialsspanPn : Submodule.span ℝ (Set.range (λ i : Fin (n + 1) ↦ Monomials i)) = Polynomial.degreeLT ℝ (n + 1) := by
  sorry

--eventuell
theorem Monomials_basis : is_basis ℝ  (λ i :  Fin (n + 1) ↦ Polynomial.X ^ (i)) := by
  sorry




--falls nicht direkt drauf zugreifbar
theorem dimPn_eq_npl1 (n : ℕ) : FiniteDimensional.finrank  ℝ (Polynomial.degreeLT ℝ (n + 1)) = n + 1 := by
  sorry

theorem degfactor_of_LagrangePolynomialseq1 (i j : Fin (n + 1)) (hij : i ≠ j) :
  ((Polynomial.C ((x i - x j)⁻¹)) * (Polynomial.X - Polynomial.C (x j))).degree = 1 := by
  have h_nonzero : (x i - x j)⁻¹ ≠ 0 := by
    apply inv_ne_zero
    exact sub_ne_zero_of_ne (hx.ne hij)
  rw [Polynomial.degree_C_mul h_nonzero]
  rw [Polynomial.degree_X_sub_C]



theorem LagrangePolynomials_has_n_factors (i : Fin (n + 1)) : (Finset.univ.filter (λ j => i ≠ j)).card = n := by
  have h1 : (Finset.filter _ Finset.univ).card + (Finset.filter _ Finset.univ).card = Finset.univ.card :=
    Finset.filter_card_add_filter_neg_card_eq_card (fun j : Fin (n + 1) ↦ i ≠ j)
  simp only [ne_eq, Decidable.not_not, Finset.card_univ, Fintype.card_fin] at h1
  have h2 : (Finset.filter (λ a => i = a) Finset.univ) = {i} := by
    ext j
    simp [Finset.mem_filter, Finset.mem_univ]
    rw[eq_comm]
  rw [h2] at h1
  have h3 : (Finset.filter (λ j => i ≠ j) Finset.univ).card + 1 = n + 1 := h1
  have h4 : (Finset.filter (λ j => i ≠ j) Finset.univ).card = n := by
    injection h3 with h_eq
  exact h4


theorem degLagrangePolynomialsisn : (LagrangePolynomials x i).degree = (n : WithBot ℕ) := by
  unfold LagrangePolynomials
  rw [Polynomial.degree_prod]
  convert_to ∑ j ∈ {j | i ≠ j}, 1 = (n : WithBot ℕ)
  · apply Finset.sum_congr
    · rfl
    · intro j hj
      simp at hj
      exact degfactor_of_LagrangePolynomialseq1 x hx i j hj
  · simp only [Finset.sum_const, nsmul_eq_mul, mul_one, Nat.cast_inj]
    have h1 : {j | i ≠ j}.toFinset.card = n := by
      have h1_1 : {j | i ≠ j}.toFinset = (Finset.univ.filter (λ j => i ≠ j)) := by
        ext j
        simp
      rw [h1_1]
      rw [LagrangePolynomials_has_n_factors]
    exact h1


noncomputable def LagrangePolynomials_in_Pn (i : Fin (n + 1)) (hx : Function.Injective x) : Polynomial.degreeLT ℝ (n + 1) where
  val := LagrangePolynomials x i
  property := by
    rw [Polynomial.mem_degreeLT]
    rw [degLagrangePolynomialsisn]
    swap
    exact hx
    exact WithBot.coe_lt_coe.mpr (lt_add_one n)


open BigOperators

theorem LagrangePolynomials_Kronecker_Delta (i j : Fin (n + 1)) :
  Polynomial.eval (x j) (LagrangePolynomials x i) = if i = j then 1 else 0 := by
  rw [LagrangePolynomials]
  split_ifs with h
  { subst h
    rw [Polynomial.eval_prod]
    simp only [Finset.mem_univ, Finset.mem_filter, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_mul, Polynomial.eval_sub]
    have (j: Fin (n + 1)): ∏ k in (Finset.univ.filter (λ k ↦ j ≠ k)), (x j - x k)⁻¹ * (x j - x k) = 1 := by
      apply Finset.prod_eq_one
      intros k hk
      rw [Finset.mem_filter] at hk
      field_simp [hx.ne hk.2]
      have h : x j ≠ x k := by exact hx.ne hk.2
      rw [div_self]
      exact sub_ne_zero_of_ne h
    convert this i
    simp
  }
  { rw [Polynomial.eval_prod]
    simp only [Finset.mem_univ, Finset.mem_filter, Finset.prod_eq_zero_iff, Polynomial.eval_C, Polynomial.eval_X,
      Polynomial.eval_mul, Polynomial.eval_sub]
    use j
    simp [h, Polynomial.eval_sub]
  }


lemma LagrangePolynomials_linearly_independent (hx : Function.Injective x) :
  LinearIndependent ℝ (λ i : Fin (n + 1) ↦ LagrangePolynomials x i) := by
  rw [linearIndependent_iff]
  intros l hl
  have h_eval : ∀ j : Fin (n + 1), Polynomial.eval (x j) (Finsupp.total (Fin (n + 1)) (Polynomial ℝ) ℝ (λ i ↦ LagrangePolynomials x i) l) = 0 := by
    intro j
    rw [hl, Polynomial.eval_zero]
  ext i
  specialize h_eval i
  simp only [Finsupp.total_apply, Finsupp.sum, Polynomial.eval_finset_sum, Polynomial.eval_smul] at h_eval
  have : ∑ j in l.support, l j * Polynomial.eval (x i) ( LagrangePolynomials x j) = 0 := by
    simpa using h_eval
  have h_li : l i * 1 = l i := by ring
  simp only [ LagrangePolynomials_Kronecker_Delta, Finset.sum_ite_eq', Finset.mem_univ, if_true, mul_one, Finset.sum_const_zero] at this
  by_cases hi : i ∈ l.support
  ·{have h_li_nonzero : l i ≠ 0 := by
      exact Finsupp.mem_support_iff.mp hi
    have allotheraddends0insupport (j:(Fin (n + 1))) (p: j∈ l.support) (b : j ≠ i) : l j * Polynomial.eval (x i) ( LagrangePolynomials x j) = 0 := by
      rw [ LagrangePolynomials_Kronecker_Delta]
      have h_lj_nonzero : l j ≠ 0 := by
        exact Finsupp.mem_support_iff.mp p
      have h_mulj : l j * (if j = i then 1 else 0) = l j * 0 := by
        refine (IsUnit.mul_right_inj ?hi).mpr ?_
        refine (IsUnit.neg_iff (l j)).mp ?hi.a
        simp
        exact h_lj_nonzero
        simp
        exact b
      have lj_eq_ljmulzero (j:Fin (n + 1)) : l j * 0 = 0 := by
        rw [mul_zero]
      rw [h_mulj]
      rw [lj_eq_ljmulzero]
      exact hx
    have lieq0 : l i = 0 := by
      have limulxi_eq_zero: l i * Polynomial.eval (x i) ( LagrangePolynomials x i) = 0 := by
        rw [Finset.sum_eq_add_sum_diff_singleton hi] at this
        have withouti: ∑ x_1 ∈ l.support \ {i}, l x_1 * Polynomial.eval (x i) ( LagrangePolynomials x x_1) =
  0:= by
          apply Finset.sum_eq_zero
          intros j hj
          apply allotheraddends0insupport
          { exact (Finset.mem_sdiff.mp hj).left }
          { intro hji
            apply (Finset.mem_sdiff.mp hj).right
            exact Finset.mem_singleton.mpr hji }
        rw [withouti] at this
        rw [add_zero] at this
        exact this
      rw [ LagrangePolynomials_Kronecker_Delta] at limulxi_eq_zero
      simp at limulxi_eq_zero
      exact limulxi_eq_zero
      exact hx
    exact lieq0
    }
  ·{have h_li_zero : l i = 0 := by
      exact Finsupp.not_mem_support_iff.mp hi
    exact h_li_zero}


theorem LagrangePolynomials_is_basis : is_basis() :=by
  sorry
