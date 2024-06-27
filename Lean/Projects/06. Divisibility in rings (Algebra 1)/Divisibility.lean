/-
# Divisibility

By Judith Ludwig, Christian Merten and Florent Schaffhauser,
Proseminar on computer-assisted mathematics,
Heidelberg, Summer Semester 2024

In this project sketch we define irreducible and prime elements of a commutative ring. The goal is to define factorial rings and to show that in a factorial ring, every irreducible element is prime.

We can find lemma names by using the library search tactic `exact?`.
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real

example {R : Type} [CommRing R] [IsDomain R] (x y : R) (hx : x ≠ 0) (h : x * y = x) : y = 1 := by
  exact (mul_eq_left₀ hx).mp h

variable {R : Type} [CommRing R]

/-
We put the following definitions in a namespace, to avoid naming clashes with the library.
-/

namespace Algebra'

/-
We say that `x` divides `y` if and only if `y` is a multiple of `x`.
-/

def Divides (x y : R) : Prop :=
  ∃ a, y = a * x

/-
We introduce the notation `x | y` for `Divides x y`.
-/

notation x " | " y => Divides x y

/-
If zero divides `x`, then `x` is zero.
-/

lemma zero_of_zero_divides (x : R) (hx : 0 | x) : x = 0 := by
  obtain ⟨a, ha⟩ := hx
  simpa using ha

/-
Hint: If you want to know what a specific tactic does, use the `#help tactic` command. For example:
-/

#help tactic subst

/-
If `x` divides a non-zero element `y`, `x` is non-zero.
-/

lemma ne_zero_of_divides_of_ne_zero (x y : R) (hy : y ≠ 0) (hxy : x | y) : x ≠ 0 := by
  intro hx
  subst hx
  -- Try to understand what's going on here!
  exact hy (zero_of_zero_divides y hxy)

/-
We say that `x` and `y` are associated if and only if `x` and `y` agree up to a unit.
-/

def IsAssociated (x y : R) : Prop :=
  ∃ (a : Rˣ), y = a * x

/-
Every element is associated to itself.
-/

lemma isAssociated_of_eq (x : R) : IsAssociated x x := by
  use 1
  simp

/-
If two elements are associated, they divide each other.
-/

lemma divides_divides_of_isAssociated (x y : R) (h : IsAssociated x y) :
    (x | y) ∧ (y | x) := by
  obtain ⟨a, ha⟩ := h
  constructor
  · use a
  · use a.inv
    rw [ha]
    simp

/-
In a domain, two elements are associated if they divide each other.
-/

lemma isAssociated_of_divides_divides_of_domain [IsDomain R] (x y : R) (hxy : x | y) (hyx : y | x) :
    IsAssociated x y := by
  by_cases hx : x = 0
  · subst hx
    have h1 : y = 0 := zero_of_zero_divides y hxy
    subst h1
    apply isAssociated_of_eq
  · simp at hx
    have hy : (y ≠ 0) :=
      ne_zero_of_divides_of_ne_zero y x hx hyx
    obtain ⟨a, ha⟩ := hxy
    obtain ⟨b, hb⟩ := hyx
    have hba : b * a = 1 := by
      rw [ha, ← mul_assoc] at hb
      exact (mul_eq_right₀ hx).mp hb.symm
    have hab : a * b = 1 := by
      rw [mul_comm a b]
      exact hba
    let a' : Rˣ := {
      val := a,
      inv := b,
      val_inv := hab,
      inv_val := hba
    }
    use a'

/-
In a domain, two elements are associated if and only if they divide each other.
-/

lemma isAssociated_iff_divides_divides_of_domain [IsDomain R] (x y : R) :
    IsAssociated x y ↔ (x | y) ∧ (y | x) := by
  constructor
  · exact divides_divides_of_isAssociated x y
  · intro ⟨hxy, hyx⟩
    sorry

/-
We say an element `x : R` is non-trivial, if it is neither zero nor a unit.
-/

def IsNontrivial (x : R) : Prop := x ≠ 0 ∧ ¬ (IsUnit x)

/-
An irreducible element `x : R` is a non-trivial element such that whenever `x = a * b`, either `a` is a unit or `b` is a unit.
-/

def IsIrreducible (x : R) : Prop :=
  IsNontrivial x ∧ ∀ a b, x = a * b → IsUnit a ∨ IsUnit b

/-
An element `x` of a ring is prime, if it is non-trivial and whenever `x` divides a product, it divides one of the factors.
-/

def IsPrime (x : R) : Prop :=
  IsNontrivial x ∧ ∀ a b, (x | a * b) → (x | a) ∨ (x | b)

/-
In an integral domain, every prime element is irreducible.
-/

theorem isIrreducible_of_isPrime [IsDomain R] (x : R) (h : IsPrime x) : IsIrreducible x := by
  obtain ⟨hnontrivial, hdiv⟩ := h
  sorry

/-
Now define factorial rings (also called unique factorization domains) and show that in any factorial ring,
also the converse of `isIrreducible_of_isPrime` holds, i.e. every irreducible element is prime.
-/

end Algebra'
