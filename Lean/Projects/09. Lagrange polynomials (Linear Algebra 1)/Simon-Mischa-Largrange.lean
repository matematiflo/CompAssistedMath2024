

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.LinearAlgebra.FiniteDimensional



variable {n : ℕ} (x : Fin (n + 1) → ℝ) (hx : Function.Injective x )



noncomputable  def Monomial (i : Fin (n + 1)) : Polynomial ℝ := Polynomial.X ^ (i : ℕ)



noncomputable def LagrangePolynomial (i : Fin (n + 1)) : Polynomial ℝ := ∏ j in {j | i ≠ j}, (Polynomial.C (x i - x j)⁻¹) * (Polynomial.X - Polynomial.C (x j))



noncomputable def Pn := Polynomial.degreeLT ℝ (n + 1)



theorem deg_of_factor_Lagrange_eq_1 (i j : Fin (n + 1)) (hij : i ≠ j) : ((Polynomial.C ((x i - x j)⁻¹)) * (Polynomial.X - Polynomial.C (x j))).degree = 1 := by
  have denominator_nonzero : (x i - x j)⁻¹ ≠ 0 := by
    apply inv_ne_zero
    exact sub_ne_zero_of_ne (hx.ne hij)
  rw [Polynomial.degree_C_mul denominator_nonzero]
  rw [Polynomial.degree_X_sub_C]



theorem Lagrange_has_n_factors (i : Fin (n + 1)) : (Finset.univ.filter (λ j => i ≠ j)).card = n := by
  have sum_compl_card : (Finset.filter _ Finset.univ).card + (Finset.filter _ Finset.univ).card = Finset.univ.card :=
    Finset.filter_card_add_filter_neg_card_eq_card (fun j : Fin (n + 1) ↦ i ≠ j)
  simp only [ne_eq, Decidable.not_not, Finset.card_univ, Fintype.card_fin] at sum_compl_card
  have singletonFinset : (Finset.filter (λ a => i = a) Finset.univ) = {i} := by
    ext j
    simp [Finset.mem_filter, Finset.mem_univ]
    rw[eq_comm]
  rw [singletonFinset] at sum_compl_card
  have card_Pl1 : (Finset.filter (λ j => i ≠ j) Finset.univ).card + 1 = n + 1 := sum_compl_card
  have card : (Finset.filter (λ j => i ≠ j) Finset.univ).card = n := by
    injection card_Pl1 with h
  exact card



theorem deg_Lagrange_is_n : (LagrangePolynomial x i).degree = (n : WithBot ℕ) := by
  unfold LagrangePolynomial
  rw [Polynomial.degree_prod]
  convert_to ∑ j ∈ {j | i ≠ j}, 1 = (n : WithBot ℕ)
  · apply Finset.sum_congr
    · rfl
    · intro j hj
      simp at hj
      exact deg_of_factor_Lagrange_eq_1 x hx i j hj
  · simp only [Finset.sum_const, nsmul_eq_mul, mul_one, Nat.cast_inj]
    have degree : {j | i ≠ j}.toFinset.card = n := by
      have Finseteq : {j | i ≠ j}.toFinset = (Finset.univ.filter (λ j => i ≠ j)) := by
        ext j
        simp
      rw [Finseteq]
      rw [Lagrange_has_n_factors]
    exact degree



noncomputable def LagrangePolynomial_Pn (i : Fin (n + 1)) : Polynomial.degreeLT ℝ (n + 1) where
  val := LagrangePolynomial x i
  property := by
    rw [Polynomial.mem_degreeLT]
    rw [deg_Lagrange_is_n]
    swap
    exact hx
    exact WithBot.coe_lt_coe.mpr (lt_add_one n)



theorem Lagrange_Kronecker_Delta (i j : Fin (n + 1)) : Polynomial.eval (x j) (LagrangePolynomial x i) = if i = j then 1 else 0 := by
  rw [LagrangePolynomial]
  split_ifs with h
  {
    subst h
    rw [Polynomial.eval_prod]
    simp only [Finset.mem_univ, Finset.mem_filter, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_mul, Polynomial.eval_sub]
    have (j: Fin (n + 1)) : ∏ k in (Finset.univ.filter (λ k ↦ j ≠ k)), (x j - x k)⁻¹ * (x j - x k) = 1 := by
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
  {
    rw [Polynomial.eval_prod]
    simp only [Finset.mem_univ, Finset.mem_filter, Finset.prod_eq_zero_iff, Polynomial.eval_C, Polynomial.eval_X,
      Polynomial.eval_mul, Polynomial.eval_sub]
    use j
    simp [h, Polynomial.eval_sub]
  }



lemma Lagrange_linear_independent :
  LinearIndependent ℝ (λ i : Fin (n+1) ↦ LagrangePolynomial_Pn x hx i) := by
  rw [linearIndependent_iff]
  intros l hl
  have LinearCombEval0 : ∀ j : Fin (n + 1), Polynomial.eval (x j) (Finsupp.total (Fin (n + 1)) ↥(Polynomial.degreeLT ℝ (n + 1)) ℝ (λ i ↦ LagrangePolynomial_Pn x hx i) l) = 0 := by
    intro j
    rw [hl]
    have: Polynomial.eval (x j) ↑(0 : ↥(Polynomial.degreeLT ℝ (n + 1))) = Polynomial.eval (x j) 0 := by
      exact rfl
    rw[this]
    rw[Polynomial.eval_zero]
  ext i
  specialize LinearCombEval0 i
  unfold LagrangePolynomial_Pn at LinearCombEval0
  rw [Finsupp.total_apply] at LinearCombEval0
  rw[Finsupp.sum] at LinearCombEval0
  simp at LinearCombEval0
  rw[Polynomial.eval_finset_sum] at LinearCombEval0
  simp at LinearCombEval0
  by_cases hi : i ∈ l.support
  ·{
    have terms_j_unequal_i_0 (j:(Fin (n + 1))) (jsupp: j∈ l.support) (juneqi : j ≠ i) : l j * Polynomial.eval (x i) (LagrangePolynomial x j) = 0 := by
      rw [Lagrange_Kronecker_Delta]
      have lj_nonzero : l j ≠ 0 := by
        exact Finsupp.mem_support_iff.mp jsupp
      have Kronecker0 : l j * (if j = i then 1 else 0) = l j * 0 := by
        refine (IsUnit.mul_right_inj ?hi).mpr ?_
        simp
        exact lj_nonzero
        simp
        exact juneqi
      rw [Kronecker0]
      rw [mul_zero]
      exact hx
    rw [Finset.sum_eq_add_sum_diff_singleton hi] at LinearCombEval0
    have specialcaseli : l i * Polynomial.eval (x i) ( LagrangePolynomial x i) = 0 := by
      have LinearCombWithoutLi: ∑ x_1 ∈ l.support \ {i}, l x_1 * Polynomial.eval (x i) ( LagrangePolynomial x x_1) = 0:= by
        apply Finset.sum_eq_zero
        intros j hj
        apply terms_j_unequal_i_0
        { exact (Finset.mem_sdiff.mp hj).left }
        {
          intro hji
          apply (Finset.mem_sdiff.mp hj).right
          exact Finset.mem_singleton.mpr hji
        }
      rw [LinearCombWithoutLi] at LinearCombEval0
      rw [add_zero] at LinearCombEval0
      exact LinearCombEval0
    rw [Lagrange_Kronecker_Delta] at specialcaseli
    simp at specialcaseli
    exact specialcaseli
    exact hx
  }
  ·{ exact Finsupp.not_mem_support_iff.mp hi }



lemma Monomial_in_Pn : ∀ i : Fin (n + 1), Monomial i ∈ Polynomial.degreeLT ℝ (n + 1) := by
  intro i
  unfold Monomial
  rw [Polynomial.mem_degreeLT]
  rw [Polynomial.degree_X_pow]
  exact WithBot.coe_lt_coe.mpr (Fin.is_lt i)



lemma Monomials_span_Pn : Polynomial.degreeLT ℝ (n + 1) = Submodule.span ℝ (Set.range (λ i : Fin (n+1) ↦ Monomial i)) := by
  rw [Polynomial.degreeLT_eq_span_X_pow]
  have: (Finset.image (fun n => Polynomial.X ^ n) (Finset.range (n + 1))).toSet = Set.range (λ i : Fin (n+1) ↦ Monomial i) := by
    refine Set.ext ?h
    rw [Finset.coe_image]
    rw [<-Set.image_univ]
    unfold Monomial
    simp
    intro x
    constructor
    · intro h
      rcases h with ⟨x_1, h₁, h₂, hx_1⟩
      use Fin.ofNat x_1
      refine (UniqueFactorizationMonoid.pow_eq_pow_iff ?h.ha0 ?h.ha1).mpr ?h.a
      exact Polynomial.X_ne_zero
      exact Polynomial.not_isUnit_X
      rw [Fin.ofNat]
      exact Nat.mod_eq_of_lt h₁
    · intro h
      rcases h with ⟨x_1, h₁, h₂, hx_1⟩
      use x_1
      constructor
      exact x_1.isLt
      rfl
  rw[this]



theorem DimPn_SmEq_nPl1 : FiniteDimensional.finrank ℝ (Polynomial.degreeLT ℝ (n + 1)) ≤ n + 1 := by
  have DimSpanSmallerCard: FiniteDimensional.finrank ℝ (Submodule.span ℝ (Set.range (λ i : Fin (n+1) ↦ Monomial i))) ≤ Finset.card (Set.toFinset (Set.range (λ i : Fin (n+1) ↦ Monomial i))) := by
    exact finrank_span_le_card (Set.range (λ i : Fin (n+1) ↦ Monomial i))
  have CardMonomials: Finset.card (Set.toFinset (Set.range (λ i : Fin (n+1) ↦ Monomial i))) = n+1 := by
    unfold Monomial
    simp
    rw[Finset.card_image_of_injective]
    · exact Finset.card_fin (n + 1)
    · intro i j hij
      simp at hij
      have: Polynomial.monomial (R := ℝ) i 1 = Polynomial.monomial j 1 := by
        repeat rw [Polynomial.monomial_one_right_eq_X_pow]
        exact hij
      rw [Polynomial.monomial_left_inj] at this
      omega
      exact Ne.symm (zero_ne_one' ℝ)
  rw [CardMonomials] at DimSpanSmallerCard
  rw[Monomials_span_Pn]
  exact DimSpanSmallerCard


instance DimPn_finite : Module.Finite ℝ (Polynomial.degreeLT ℝ (n + 1)) := by
  rw [Module.Finite.iff_fg]
  use Finset.image (λ i : Fin (n+1) ↦ Monomial i) Finset.univ
  simp
  exact Eq.symm (Monomials_span_Pn)



theorem DimPn_GtEq_nPl1 : n + 1 ≤ FiniteDimensional.finrank ℝ (Polynomial.degreeLT ℝ (n + 1)) := by
  simpa using LinearIndependent.fintype_card_le_finrank (Lagrange_linear_independent x hx)



lemma DimPn_Eq_nPl1 : FiniteDimensional.finrank ℝ (Polynomial.degreeLT ℝ (n + 1)) = n+1 := by
  apply le_antisymm
  · exact DimPn_SmEq_nPl1
  · exact DimPn_GtEq_nPl1 x hx



noncomputable def LangrangeBasisPn : Basis (Fin (n + 1)) ℝ (Polynomial.degreeLT ℝ (n + 1)) := by
  apply basisOfLinearIndependentOfCardEqFinrank (b := LagrangePolynomial_Pn x hx)
  · exact Lagrange_linear_independent x hx
  · simp
    exact (DimPn_Eq_nPl1 x hx).symm
