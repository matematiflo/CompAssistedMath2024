/-
# Noetherian rings

By Judith Ludwig, Christian Merten and Florent Schaffhauser,
Proseminar on computer-assisted mathematics,
Heidelberg, Summer Semester 2024

In this project sketch we define Noetherian rings and show a basic characterisation.
-/

import Mathlib.RingTheory.Finiteness

namespace Algebra'

variable {R : Type} [CommRing R]

/-
We can find lemma names by using the library search tactic `exact?`.
-/

example (x y : R) (I : Ideal R) (hx : x ∈ I) (hy : y ∈ I) : x + y ∈ I := by
  exact?

/-
We say that a sequence of ideals is an ascending chain, if for every `n`, the `n`-th ideal is contained in the `n+1`-th ideal.
-/

def IsAscendingChain (I : ℕ → Ideal R) : Prop :=
  ∀ n, I n ≤ I (n + 1)

lemma monotone_of_isAscendingChain {I : ℕ → Ideal R} (hI : IsAscendingChain I) :
    Monotone I := by
  apply monotone_nat_of_le_succ
  exact hI

lemma le_of_le_of_isAscendingChain {I : ℕ → Ideal R} (hI : IsAscendingChain I) {m n : ℕ}
    (hmn : m ≤ n) : I m ≤ I n :=
  monotone_of_isAscendingChain hI hmn

/-
`Ideal R` is defined as `Submodule R R` which is a `structure`. To see the fields of `Submodule`, you can use the `#print` command:
-/

#print Submodule

/-
`Submodule` has a field `toAddSubmonoid`, which itself has a type defined by a structure, whose fields you can also check by:
-/

#print AddSubmonoid

/-
To define a term of a type defined by a structure, you can use the `def foo : bar where` syntax.

The union over all ideals in an ascending chain is an ideal.
-/

def ChainLimit (I : ℕ → Ideal R) (hI : IsAscendingChain I) : Ideal R where
  carrier := Set.iUnion (fun n : ℕ ↦ I n)
  add_mem' {x y} hx hy := by
    simp at hx hy
    obtain ⟨i, hi⟩ := hx
    obtain ⟨j, hj⟩ := hy
    /- Found using `simp?` -/
    simp only [Set.mem_iUnion, SetLike.mem_coe]
    use i ⊔ j
    apply Ideal.add_mem
    · apply le_of_le_of_isAscendingChain hI le_sup_left hi
    · sorry
  zero_mem' := by simp
  smul_mem' := sorry

/-
For more insight on structures, see https://lean-lang.org/theorem_proving_in_lean4/structures_and_records.html

A chain of ideals is stationary, if there exists `n : ℕ` such that `I n = I m` for all
`m ≥ n`.
-/

def IsStationary (I : ℕ → Ideal R) : Prop :=
  ∃ n, ∀ m ≥ n, I n = I m

variable (R)

/-
A ring is called noetherian, if every ascending chain is stationary.
-/

def IsNoetherian : Prop :=
  ∀ (I : ℕ → Ideal R), IsAscendingChain I → IsStationary I

variable {R}

/-
If every ideal of `R` is finitely generated, `R` is Noetherian.
-/

theorem isNoetherian_of_forall_ideal_fg (h : ∀ (I : Ideal R), I.FG) : IsNoetherian R := by
  intro I hI
  let J : Ideal R := ChainLimit I hI
  obtain ⟨s, hs⟩ := h J
  sorry

/-
Any field is Noetherian.
-/

theorem isNoetherian_of_field {R : Type} [Field R] : IsNoetherian R := by
  apply isNoetherian_of_forall_ideal_fg
  intro I
  by_cases h : I = 0
  · subst h
    use ∅
    simp
  · have h1 : ∃ x ∈ I, x ≠ 0 := by
      by_contra h2
      simp at h2
      have : I = 0 := by
        apply le_antisymm
        · intro x hx
          simp
          apply h2 x hx
        · simp
      contradiction
    obtain ⟨x, hx1, hx2⟩ := h1
    use {x}
    apply le_antisymm
    · sorry
    · sorry

/-
The integers are Noetherian.
-/

example : IsNoetherian ℤ := by
  sorry

/-
Now state and show the following:

- Every non-empty set `s` of ideals of `R` contains (at least) one maximal element, i.e. an ideal `I` in `s` that is not contained in any other (i.e. different from `I`) element of `s`.
- The converse of `isNoetherian_of_forall_ideal_fg`, i.e. every ideal in a Noetherian ring is finitely generated.

Hint: for the first, do a proof by contradiction as in the proof of `isNoetherian_of_field`.
-/

/-
Further ideas: Define Artinian rings and show that a ring is Artinian if and only if it is a Noetherian ring where every prime ideal is maximal.
-/

end Algebra'
