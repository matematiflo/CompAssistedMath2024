# Lagrange polynomials

By Judith Ludwig, Christian Merten and Florent Schaffhauser,
Proseminar on computer-assisted mathematics,
Heidelberg, Summer Semester 2024

In this project sketch, we define Lagrange polynomials and show that they form a basis of the vector space of polynomials $'P_n'$ of a finite degree $'n \in N_0'$. This is also called the 'Lagrange Interpolation Theorem'.

```lean
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.RingTheory.Polynomial.Basic
```

We can find lemma names by using the library search tactic `exact?`.

```lean
example (x y : ℝ) : |x + y| ≤ |x| + |y| := by
  exact?

open BigOperators Polynomial
```

We fix a natural number `n` (can be zero) and distinct real numbers `x i` for `0 ≤ i < n + 1` (the 'distinct' is expressed by the fact that the function `x` is injective!).

The reason why we use the upper bound `n + 1` is avoid subtractions: This way the degree of the Lagrange polynomial is `n` and not `n - 1`.

```lean
variable {n : ℕ} (x : Fin (n + 1) → ℝ) (hx : Function.Injective x)
```

The type of polynomials is spelled `ℝ[X]` and the variable is simply `X`:

```lean
#check (X : ℝ[X])
```

The constant polynomials are accessed by `C`:

```lean
#check (C 3 : ℝ[X])
```

The `i`-th Lagrange polynomial.

```lean
noncomputable def LagrangePolynomial (i : Fin (n + 1)) : ℝ[X] :=
  ∏ j ∈ {j | i ≠ j}, (x i - x j)⁻¹ • (X - C (x i))

namespace LagrangePolynomial
```

The first goal is to show that the degree of `LagrangePolynomial` is indeed `n`.

In Lean the type of the degree of a polynomial is `WithBot ℕ` reflecting that it is either a non-negative integer or `- ∞` which is spelled `⊥` (the 'bottom' element). You can always check this with `#check`:

```lean
#check Polynomial.degree

lemma support_card_eq (i : Fin (n + 1)) : {j | i ≠ j}.toFinset.card = n := by
  have h1 : (Finset.filter _ Finset.univ).card + (Finset.filter _ Finset.univ).card = Finset.univ.card :=
    Finset.filter_card_add_filter_neg_card_eq_card (fun j : Fin (n + 1) ↦ i ≠ j)
  simp only [ne_eq, Decidable.not_not, Finset.card_univ, Fintype.card_fin] at h1
  have h2 : (Finset.filter (fun a => i = a) Finset.univ) = {i} := by
    -- We can show equality of finsets in exactly the same way as we show equality of sets.
    sorry
  simpa [h2] using h1
```

Each of the factors of `LagrangePolynomial` has degree one.

```lean
lemma degree_factor_eq (i j : Fin (n + 1)) (hij : i ≠ j) :
    ((x i - x j)⁻¹ • (X - C (x i))).degree = 1 := by
  -- Try to understand why this proof works!
  have : x i ≠ x j := fun a => hij (hx a)
  sorry

lemma degree_eq : (LagrangePolynomial x i).degree = (n : WithBot ℕ) := by
  unfold LagrangePolynomial
  rw [Polynomial.degree_prod]
  show ∑ j ∈ {j | i ≠ j}, ((x i - x j)⁻¹ • (X - C (x i))).degree = (n : WithBot ℕ)
  convert_to ∑ j ∈ {j | i ≠ j}, 1 = (n : WithBot ℕ)
  · apply Finset.sum_congr
    · rfl
    · intro j hj
      simp at hj
      exact degree_factor_eq x hx i j hj
  · simp only [Finset.sum_const, nsmul_eq_mul, mul_one, Nat.cast_inj]
    exact support_card_eq i
```

We now want to consider the `ℝ`-subvectorspace of polynomials with bounded degree.

```lean
#check Polynomial.degreeLT ℝ (n + 1)
```

The underlying type of `degreeLT ℝ (n + 1)` is a subtype defined by some property,
which is implemented as a `structure`. To inspect the fields of `Subtype`,
you can use the `#print` command:

```lean
#print Subtype
```

To construct a term of a type defined by a `structure`, you can use the `def foo : bar where` syntax.

For convenience, we define a modified `LagrangePolynomial'` that is a term of type
`Polynomial.degreeLT ℝ (n + 1)`.

Remark: There is also the type `Polynomial.degreeLE ℝ n` which is of course mathematically
equivalent. But we use `Polynomial.degreeLT` here, since it has better library support.

```lean
noncomputable def LagrangePolynomial' (i : Fin (n + 1)) : Polynomial.degreeLT ℝ (n + 1) where
  val := LagrangePolynomial x i
  property := by
    rw [Polynomial.mem_degreeLT]
    -- Complete the proof using `degree_eq`
    sorry
```

Technical note: Here, slightly more is going on: As we saw above, the type of `Polynomial.degreeLT ℝ (n + 1)` is `Submodule ℝ ℝ[X]`, which has a coercion (https://leanprover.github.io/theorem_proving_in_lean/interacting_with_lean.html#coercions) to `Type`.

```lean
#synth CoeSort (Submodule ℝ ℝ[X]) Type
```

This allows Lean to interpret `Submodule ℝ ℝ[X]` as a type and hence allows us to define terms of type `degreeLT ℝ (n + 1)`.

We now want to show that the family of `LagrangePolynomial'` is a basis of `Polynomial.degreeLT`. For this, we first want to show that they are `LinearIndependent`.

*Hint 1:* To conclude that the `LagrangePolynomial'`s are a basis, you can use that the `Module.rank` (aka dimension) of `Polynomial.degreeLT ℝ (n + 1)` is `n`.

*Hint 2:* You can combine two theorems from the library to calculate the rank. Browse the mathlib 4 documentation (https://leanprover-community.github.io/mathlib4_docs/index.html)
on `Polynomial.degreeLT` and search via `loogle` (https://loogle.lean-lang.org/) for related results.
