import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Data.Nat.WithBot
import Mathlib.Data.Nat.Order.Lemmas


variable {n : ℕ} (x : Fin (n + 1) → ℝ) (hx : Function.Injective x)

noncomputable def LagrangePolynomial (i : Fin (n + 1)) : Polynomial ℝ :=
  ∏ j in {j | i ≠ j}, (Polynomial.C (x i - x j)⁻¹) * (Polynomial.X - Polynomial.C (x j))

-- Proof that all our defined Lagrange polynomials lay in Pn, therefore have degree of n or lower:

-- Proof that every factor of ∏ of every lagrange polynomial is of degree 1
-- Proof that every factor of ∏ of every lagrange polynomial is of degree 1


lemma degree_factor_eq (i j : Fin (n + 1)) (hij : i ≠ j) :
  ((Polynomial.C ((x i - x j)⁻¹)) * (Polynomial.X - Polynomial.C (x j))).degree = 1 := by
  -- Verify that the constant term (x i - x j)⁻¹ is non-zero
  have h_nonzero : (x i - x j)⁻¹ ≠ 0 := by
    -- Since x is injective, x i ≠ x j, hence their difference is non-zero
    apply inv_ne_zero
    exact sub_ne_zero_of_ne (hx.ne hij)

  -- Simplify the degree of the product
  rw [Polynomial.degree_C_mul h_nonzero]
  -- Simplify the degree of the constant term
  rw [Polynomial.degree_X_sub_C]
  -- Degree of X is 1 and Degree of C(x j) is 0

-- proof that number of ∏ factors=n, property of finite set is (needed?) for cardinality
lemma support_card_eq (i : Fin (n + 1)) : (Finset.univ.filter (λ j => i ≠ j)).card = n := by
  have h1 : (Finset.filter _ Finset.univ).card + (Finset.filter _ Finset.univ).card = Finset.univ.card :=
    Finset.filter_card_add_filter_neg_card_eq_card (fun j : Fin (n + 1) ↦ i ≠ j)-- uses theorem that card of a filtered set + card of its negated filter set = card of unfiltered set on the first filter and set of h1
  simp only [ne_eq, Decidable.not_not, Finset.card_univ, Fintype.card_fin] at h1 -- ≠  ¬ = for easier processing and fill in n+1 for card of total set
  have h2 : (Finset.filter (λ a => i = a) Finset.univ) = {i} := by
    ext j
    simp [Finset.mem_filter, Finset.mem_univ]
    rw[eq_comm]

  rw [h2] at h1 -- replaces second filtered set with card one set {i}
  have h3 : (Finset.filter (λ j => i ≠ j) Finset.univ).card + 1 = n + 1 := h1 -- evaluates {i}.card

  have h4 : (Finset.filter (λ j => i ≠ j) Finset.univ).card = n := by
    injection h3 with h_eq
     -- subtracts 1 on each side
 -- formally rewrites h4 to exactly suit final type
  exact h4


lemma degree_eq : (LagrangePolynomial x i).degree = (n : WithBot ℕ) := by
  unfold LagrangePolynomial
  rw [Polynomial.degree_prod] -- proof/rule that degree of product of polynomials is sum of degrees of factors
  convert_to ∑ j ∈ {j | i ≠ j}, 1 = (n : WithBot ℕ)
  · apply Finset.sum_congr
    · rfl
    · intro j hj
      simp at hj
      exact degree_factor_eq x hx i j hj
  · simp only [Finset.sum_const, nsmul_eq_mul, mul_one, Nat.cast_inj]
    have h1 : {j | i ≠ j}.toFinset.card = n := by
      have h1_1 : {j | i ≠ j}.toFinset = (Finset.univ.filter (λ j => i ≠ j)) := by
        ext j
        simp
      rw [h1_1]
      rw [support_card_eq]
    exact h1

-- show for lagrange polynomial of (arbitrary?) point xi that degree is n, based on the previous proofs that n factors all with degree 1




  -- uses proof to show that for any i in domain of X  ∑ j ∈ {j | i ≠ j} has always n addends
 -- rw [support_card_eq j]
 -- rw [Finset.sum_const, nat.smul_one_eq_coe] -- rewrites the addends to 1s and proof that sum of n addends of a constant value a is n*(const a)
 -- exact n






noncomputable def LagrangePolynomial' (i : Fin (n + 1)) (hx : Function.Injective x) : Polynomial.degreeLT ℝ (n + 1) where
  val := LagrangePolynomial x i
  property := by
    rw [Polynomial.mem_degreeLT]
    rw [degree_eq]
    swap
    exact hx
    exact WithBot.coe_lt_coe.mpr (lt_add_one n)



lemma LagrangePolynomials_linear_independent (hx : Function.Injective x) :
  LinearIndependent ℝ (λ i : Fin (n + 1) ↦ LagrangePolynomial x i) := by
  rw [linearIndependent_iff]
  intros l hl
  have h_eval : ∀ j : Fin (n + 1), Polynomial.eval (x j) (Finsupp.total (Fin (n + 1)) (Polynomial ℝ) ℝ (λ i ↦ LagrangePolynomial x i) l) = 0 := by
    intro j
    rw [hl, Polynomial.eval_zero]
  ext i
  specialize h_eval i
  simp only [Finsupp.total_apply, Finsupp.sum, Polynomial.eval_finset_sum, Polynomial.eval_smul] at h_eval
  have : ∑ j in l.support, l j * Polynomial.eval (x i) (LagrangePolynomial x j) = 0 := by
    simpa using h_eval
  have h_li : l i * 1 = l i := by ring
  simp only [LagrangePolynomial, Polynomial.eval_prod, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_sub, Polynomial.eval_C] at this
  have : (if i ∈ l.support then l i else 0) = l i := by
    by_cases h : i ∈ l.support
    · rw [if_pos h]
    · rw [if_neg h]
      simp only [Finsupp.not_mem_support_iff] at h
      exact h.symm
