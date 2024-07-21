/-
# Euclidean rings

By Judith Ludwig, Christian Merten and Florent Schaffhauser,
Proseminar on computer-assisted mathematics,
Heidelberg, Summer Semester 2024

In this project sketch, we introduce principal ideal domains and Euclidean rings. We explore some examples and show that every Euclidean domain is a principal ideal domain.

A possible further goal could be stating (and possibly proving) the existence of the Smith Normalform.
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.RingTheory.Polynomial.Basic

/-
We can find lemma names by using the library search tactic `exact?`.
-/

example (a b : ℤ) : a % b + b * (a / b) = a := by
  --exact?
  exact Int.emod_add_ediv a b

/-
A commutative ring is a *principal ideal domain* (PID) if it is a domain and every ideal is principal.
-/

structure IsPID (R : Type) [CommRing R] : Prop where
  isDomain : IsDomain R
  ideal_principal : ∀ (I : Ideal R), ∃ (x : R), Ideal.span {x} = I

/-
Note: We used the `structure` command to define `IsPID`. If you encounter a structure, you can inspect its fields with the `#print` command:
-/

#print IsPID

/-
To construct a term of a type defined by `structure`, use the `def foo : bar where` (or `theorem foo : bar where`) syntax.

For more information about structures, see https://lean-lang.org/theorem_proving_in_lean4/structures_and_records.html

Next we prove that a field is a principal ideal domain.
-/







/- `IsDomain` is a so-called 'typeclass'. We don't get into the details here, but this means that we can use `inferInstance` to ask Lean to automatically fill in a proof.
  In this case `IsDomain` is already proven for any field. -/


lemma isPID_of_field (k : Type) [Field k] : IsPID k where
  isDomain := inferInstance
  ideal_principal := by
    intro I
    by_cases h : I = 0
    -- Case 1: I = 0
    · subst h
      use 0
      simp
    -- Case 2: I ≠ 0
    · simp at h   --i dont think this does much...
      have h2 : ∃ x ∈ I, x ≠ 0 := by
        --since k is a field and I is a non zero ideal, it must contain a non zero element
        -- exact?
        exact Submodule.exists_mem_ne_zero_of_ne_bot h

      -- Let x be a nonzero element of I
      obtain ⟨x, hx, hnezero⟩ := h2
      use x
      apply Ideal.ext
      intro y
      constructor
      · intro
        have hxu: IsUnit x := by {
          rw[isUnit_iff_ne_zero]
          exact hnezero
        }
        have h2 : I = ⊤ := by exact Ideal.eq_top_of_isUnit_mem I hx hxu
        rw[h2]
        exact trivial

      · intro
        have hxu: IsUnit x := by {
          rw[isUnit_iff_ne_zero]
          exact hnezero
        }
        rw[← Ideal.span_singleton_eq_top] at hxu
        rw[hxu]
        exact trivial

/-
A *Euclidean function* on a commutative ring is a height function `R → ℕ` and a division with remainder, where the height of the remainder is smaller than the denominator.

Note: This is not merely a proposition, but contains the data of a height function. This height function is not unique, so the datum of a ring `R` with a term `h : Euclidean R` is not equivalent to the notion of a Euclidean domain (see `IsEuclideanDomain`).
-/

structure EuclideanFunction ( R : Type) [CommRing R] where
  /-- Height function. -/
  height : R → WithBot ℕ
  zero_of_bot (x : R) : height x = ⊥ → x = 0
  /-- Division by zero -/
  division (a b : R) (hb : b ≠ 0) : ∃ q r, a = b * q + r ∧ (r = 0 ∨ height r < height b)

/-
An integral domain is called a Euclidean domain if it admits a Euclidean function.
-/

structure IsEuclideanDomain (R : Type) [CommRing R] : Prop where
  isDomain : IsDomain R
  exists_euclideanFunction : Nonempty (EuclideanFunction R)

/-
A Euclidean structure on a field `k`.

Note 1: Observe that we can change the `42` in the proof below to an arbitrary value. In particular, the height function is not unique!
Note 2: This is a `def` and not a `theorem`, because it contains data. Try to see what happens if you replace `def` by `theorem`!
-/

def euclideanOfField (k : Type) [Field k] : EuclideanFunction k where
  height _ := 42
  zero_of_bot x h := by simp_all;/- absurd h; decide-/
  division a b hb := by
    use a / b
    use 0
    /- found by `simp?` -/
    simp only [add_zero, lt_self_iff_false, or_false, and_true]
    field_simp

theorem isEuclidean_of_field (k : Type) [Field k] : IsEuclideanDomain k where
  isDomain := inferInstance
  exists_euclideanFunction := ⟨euclideanOfField k⟩

/-
The absolute value of an integer.
-/

#check Int.natAbs

/-
The canonical Euclidean structure on ℤ.
Hint: The remainder of integer division of `a : ℤ` by `b : ℤ` is `a % b`.
-/

def Int.euclidean : EuclideanFunction ℤ where
  height := λ n => n.natAbs
  zero_of_bot := by
    intro a
    simp
  division a b hb := by
    let q := a / b
    let r := a % b

    -- Proof that a = b * q + r
    have h1 : a = b * q + r := by{
      nth_rewrite 1 [← Int.emod_add_ediv a b, add_comm]
      rfl
    }
    --proof 0 ≤ r
    have h2 : 0 ≤ r := by{
      --exact?
      exact emod_nonneg a hb
    }
        --proof r = |r|
    have h3 :   r = |r| := by{
      rw [← abs_eq_self] at h2
      symm
      exact h2}
    --proof |r| < |b|
    have h4 :  natAbs r < natAbs b := by{
      zify
      rw[← h3]
      exact emod_lt a hb
    }
    use q, r
    constructor
    · apply h1
    · right
      simp
      exact h4



theorem Int.isEuclidean : IsEuclideanDomain ℤ where
  isDomain := inferInstance
  exists_euclideanFunction := ⟨Int.euclidean⟩

/-
Any Euclidean ring (domain) is a principal ideal domain.
-/

theorem isPID_of_euclidean (R : Type) [CommRing R] (h : IsEuclideanDomain R) : IsPID R where
  isDomain := h.isDomain
  ideal_principal := by
    intro I
    by_cases h : I = 0
    -- Case 1: I = 0
    · subst h
      use 0
      simp
    -- Case 2: I ≠ 0
    · simp at h   --i dont think this does much...
      have h2 : ∃ x ∈ I, x ≠ 0 := by
        --since k is a field and I is a non zero ideal, it must contain a non zero element
        -- exact?
        exact Submodule.exists_mem_ne_zero_of_ne_bot h

      -- Let x be a nonzero element of I
      obtain ⟨x, hx, hnezero⟩ := h2
      use x

      apply Ideal.ext
      intro y
      constructor
      · intro hy
        -- Since `x` generates the ideal, `y` should be in the ideal generated by `x`
        rw [Ideal.mem_span_singleton] at hy
        obtain ⟨q, rlf⟩ := hy

        apply Ideal.mul_mem_right q at hx
        subst rlf
        exact hx

        sorry



      · intro hy
        rw [Ideal.mem_span_singleton]
        obtain ⟨q, rfl⟩ := hy
        exact Ideal.mul_mem_right I q hx
        sorry

      -- Use the Euclidean function to generate the principal ideal






open Polynomial

/-
The canonical Euclidean function on the polynomial ring in one variable over a field.
-/
def Polynomial.euclidean (k : Type) [Field k] : EuclideanFunction k[X] where
  height f := f.degree
  zero_of_bot f hf := by
    exact degree_eq_bot.mp hf

  division := by
    intro a
    intro b
    intro hb
    --let q :=
    --let r :=
    sorry


theorem Polynomial.isEuclidean_of_field (k : Type) [Field k] : IsEuclideanDomain k[X] := by
  sorry

/-
`Polynomial.isEuclidean_of_field` is wrong if we drop the field assumption. For example:
-/

theorem not_isPID_Zx : ¬ IsPID (Polynomial ℤ) := by
  sorry

example : ¬ IsEuclideanDomain ℤ[X] := by
  have h1 := not_isPID_Zx
  have h2 := isPID_of_euclidean

  intro h
  apply h2 at h
  apply h1 at h
  exact h
