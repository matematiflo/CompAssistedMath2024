```lean
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.LinearAlgebra.FiniteDimensional


-- definition n for Pn and the injective Function for values of Lagr.

variable {n : ℕ} (x : Fin (n + 1) → ℝ) (hx : Function.Injective x )


-- definition n+1 Monomials that span Pn

noncomputable  def Monomial (i : Fin (n + 1)) : Polynomial ℝ := Polynomial.X ^ (i : ℕ)


-- defintion n+1 Lagrange Polynomials for interpolation points given by function X

noncomputable def LagrangePolynomial (i : Fin (n + 1)) : Polynomial ℝ := ∏ j in {j | i ≠ j}, (Polynomial.C (x i - x j)⁻¹) * (Polynomial.X - Polynomial.C (x j))


-- Pn is Submodule of ℝ[X] with degree less than n+1

noncomputable def Pn := Polynomial.degreeLT ℝ (n + 1)


--Degree of one of the n factors of a Lagrange Polynomial is 1

theorem deg_of_factor_Lagrange_eq_1 (i j : Fin (n + 1)) (hij : i ≠ j) : ((Polynomial.C ((x i - x j)⁻¹)) * (Polynomial.X - Polynomial.C (x j))).degree = 1 := by

  --no division by zero because
  have denominator_nonzero : (x i - x j)⁻¹ ≠ 0 := by
    -- (x i - x j = a) ≠ 0 → a⁻¹ ≠ 0
    apply inv_ne_zero
    -- wegen hij : i ≠ j und inj x i ≠ x j
    exact sub_ne_zero_of_ne (hx.ne hij)
  -- multiplication with constant doesnt influence degree
  rw [Polynomial.degree_C_mul denominator_nonzero]
  -- degree (X - const) is degree X
  rw [Polynomial.degree_X_sub_C]


-- Lagrange Polynomial has n factors

theorem Lagrange_has_n_factors (i : Fin (n + 1)) : (Finset.univ.filter (λ j => i ≠ j)).card = n := by

  -- card total Finset is summ of cards of 2 complements (applied on Filters j ≠ i and j = i)
  have sum_compl_card : (Finset.filter _ Finset.univ).card + (Finset.filter _ Finset.univ).card = Finset.univ.card :=
    Finset.filter_card_add_filter_neg_card_eq_card (fun j : Fin (n + 1) ↦ i ≠ j)
  -- simplify ≠ and use card Fintype Fin (n + 1) = n+1
  simp only [ne_eq, Decidable.not_not, Finset.card_univ, Fintype.card_fin] at sum_compl_card
  -- Filtered finset j = i contains only element i
  have singletonFinset : (Finset.filter (λ a => i = a) Finset.univ) = {i} := by
    ext j
    simp [Finset.mem_filter, Finset.mem_univ]
    rw[eq_comm]
  rw [singletonFinset] at sum_compl_card
  -- card {i} is 1
  have card_Pl1 : (Finset.filter (λ j => i ≠ j) Finset.univ).card + 1 = n + 1 := sum_compl_card
  -- injection uses that natural numbers can be created by induction
  have card : (Finset.filter (λ j => i ≠ j) Finset.univ).card = n := by
    injection card_Pl1 with h
  exact card


--degree of any Lagrange Polynom is n

theorem deg_Lagrange_is_n : (LagrangePolynomial x i).degree = (n : WithBot ℕ) := by
  unfold LagrangePolynomial
  --degree of product of polynomials is sum of degrees of factors
  rw [Polynomial.degree_prod]
  --rewrite every factor as 1 by deg_of_factor_Lagrange_eq_1
  convert_to ∑ j ∈ {j | i ≠ j}, 1 = (n : WithBot ℕ)
  · apply Finset.sum_congr
    · rfl
    · intro j hj
      simp at hj
      exact deg_of_factor_Lagrange_eq_1 x hx i j hj
  --sum over const is card of indexset (n from Lagrange_has_n_factors) * const
  · simp only [Finset.sum_const, nsmul_eq_mul, mul_one, Nat.cast_inj]
    have degree : {j | i ≠ j}.toFinset.card = n := by
      have Finseteq : {j | i ≠ j}.toFinset = (Finset.univ.filter (λ j => i ≠ j)) := by
        ext j
        simp
      rw [Finseteq]
      rw [Lagrange_has_n_factors]
    exact degree


--definition of Lagrage Polynomials with type Polynomial of Pn (need to show that can be of type Pn, that it is in Pn)

noncomputable def LagrangePolynomial_Pn (i : Fin (n + 1)) : Polynomial.degreeLT ℝ (n + 1) where
  val := LagrangePolynomial x i
  property := by
    -- in Pn means degree smaller n+1
    rw [Polynomial.mem_degreeLT]
    rw [deg_Lagrange_is_n]
    swap
    exact hx
    -- n<n+1 in natural numbers can be transfered to exponent type WithBot
    exact WithBot.coe_lt_coe.mpr (lt_add_one n)


-- Lagragepolynomials can be evaluated with Kronecker Delta

theorem Lagrange_Kronecker_Delta (i j : Fin (n + 1)) : Polynomial.eval (x j) (LagrangePolynomial x i) = if i = j then 1 else 0 := by
  rw [LagrangePolynomial]
  -- 2 cases i = j and not
  split_ifs with h
  {
    subst h
    rw [Polynomial.eval_prod]
    simp only [Finset.mem_univ, Finset.mem_filter, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_mul, Polynomial.eval_sub]
    --proof that every factor 1
    have (j: Fin (n + 1)) : ∏ k in (Finset.univ.filter (λ k ↦ j ≠ k)), (x j - x k)⁻¹ * (x j - x k) = 1 := by
      apply Finset.prod_eq_one
      intros k hk
      rw [Finset.mem_filter] at hk
      field_simp [hx.ne hk.2]
      -- no division by 0
      have h : x j ≠ x k := by exact hx.ne hk.2
      rw [div_self]
      exact sub_ne_zero_of_ne h
    convert this i
    simp
  }
  {
    rw [Polynomial.eval_prod]
    -- if one factor 0 then product 0
    simp only [Finset.mem_univ, Finset.mem_filter, Finset.prod_eq_zero_iff, Polynomial.eval_C, Polynomial.eval_X,
      Polynomial.eval_mul, Polynomial.eval_sub]
    use j
    simp [h, Polynomial.eval_sub]
  }


-- lagrange Polynomials linear independent

lemma Lagrange_linear_independent :
  LinearIndependent ℝ (λ i : Fin (n+1) ↦ LagrangePolynomial_Pn x hx i) := by

  --linear independence definition that linearcomb zero => all coefficients zero
  rw [linearIndependent_iff]
  intros l hl
  -- linear combination is zero => concrete evaluation points xj also 0
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
  -- show separately for cases coefficients already 0 (means not in support) and 0 (means in support)
  by_cases hi : i ∈ l.support
  ·{
    -- evaluated on xi all Lagrangepolynom xj is 0
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
    -- Lagrange Polynom xi eval at xi is 1 and rest of lin comb 0, therefore li zero
    have lieq0 : l i * Polynomial.eval (x i) ( LagrangePolynomial x i) = 0 := by
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
    rw [Lagrange_Kronecker_Delta] at lieq0
    simp at lieq0
    exact lieq0
    exact hx
  }
  --def of not in support => li = 0
  ·{ exact Finsupp.not_mem_support_iff.mp hi }


-- (proof that) Monomials element Pn

lemma Monomial_in_Pn : ∀ i : Fin (n + 1), Monomial i ∈ Polynomial.degreeLT ℝ (n + 1) := by
  intro i
  unfold Monomial
  rw [Polynomial.mem_degreeLT]
  rw [Polynomial.degree_X_pow]
  exact WithBot.coe_lt_coe.mpr (Fin.is_lt i)


-- Monomials span Pn

lemma Monomials_span_Pn : Polynomial.degreeLT ℝ (n + 1) = Submodule.span ℝ (Set.range (λ i : Fin (n+1) ↦ Monomial i)) := by
  --use Definition that internal Monomials (x^i for i<n+1) span Pn
  rw [Polynomial.degreeLT_eq_span_X_pow]
  -- show that the internal set of Monomials is the exact same set of Polynomials like ours
  have: (Finset.image (fun n => Polynomial.X ^ n) (Finset.range (n + 1))).toSet = Set.range (λ i : Fin (n+1) ↦ Monomial i) := by
    refine Set.ext ?h
    rw [Finset.coe_image]
    rw [<-Set.image_univ]
    unfold Monomial
    simp
    intro x
    -- split 2 ways, when in first set then has to be in second and other way
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


-- Dimension of Pn is smaller or equal n+1

theorem DimPn_SmEq_nPl1 : FiniteDimensional.finrank ℝ (Polynomial.degreeLT ℝ (n + 1)) ≤ n + 1 := by
  -- Dimension of Span of a Set is smaller or equal card
  have DimSpan_SmEq_Card: FiniteDimensional.finrank ℝ (Submodule.span ℝ (Set.range (λ i : Fin (n+1) ↦ Monomial i))) ≤ Finset.card (Set.toFinset (Set.range (λ i : Fin (n+1) ↦ Monomial i))) := by
    exact finrank_span_le_card (Set.range (λ i : Fin (n+1) ↦ Monomial i))
  -- card of our Set of Monomials is n+1
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
  rw [CardMonomials] at DimSpan_SmEq_Card
  rw[Monomials_span_Pn]
  exact DimSpan_SmEq_Card


-- Problem that Finrank dimension defined as 0 for infinite dimensional vetor spaces, therefore proof that Pn is can be finitely spanned with Monomials

instance DimPn_finite : Module.Finite ℝ (Polynomial.degreeLT ℝ (n + 1)) := by
  rw [Module.Finite.iff_fg]
  use Finset.image (λ i : Fin (n+1) ↦ Monomial i) Finset.univ
  simp
  exact Eq.symm (Monomials_span_Pn)


-- card independent set of Polynomials in vectorspace is smaller or equal dim of this vecotorspace
-- this only works because Pn not infinite dimensional and therefore defined as Finrank 0

theorem DimPn_GtEq_nPl1 : n + 1 ≤ FiniteDimensional.finrank ℝ (Polynomial.degreeLT ℝ (n + 1)) := by
  simpa using LinearIndependent.fintype_card_le_finrank (Lagrange_linear_independent x hx)


-- dimension (finrank) of Pn is n+1 by applys the 2 previous boundaries

lemma DimPn_Eq_nPl1 : FiniteDimensional.finrank ℝ (Polynomial.degreeLT ℝ (n + 1)) = n+1 := by
  apply le_antisymm
  · exact DimPn_SmEq_nPl1
  · exact DimPn_GtEq_nPl1 x hx


-- the Lagrange Polynomials form a Basis of Pn because they are a linear independent set of elements of Pn which has cardinality of the Dimension of Pn and this is only true for a basis

noncomputable def LangrangeBasisPn : Basis (Fin (n + 1)) ℝ (Polynomial.degreeLT ℝ (n + 1)) := by
  apply basisOfLinearIndependentOfCardEqFinrank (b := LagrangePolynomial_Pn x hx)
  · exact Lagrange_linear_independent x hx
  · simp
    exact (DimPn_Eq_nPl1 x hx).symm
```
