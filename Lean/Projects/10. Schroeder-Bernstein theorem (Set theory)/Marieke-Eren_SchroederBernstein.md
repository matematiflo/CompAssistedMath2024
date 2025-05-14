# The Schröder-Bernstein Theorem

Project by Marieke and Eren,
Stub file by Judith Ludwig, Christian Merten and Florent Schaffhauser,
Proseminar on computer-assisted mathematics,
Heidelberg, Summer Semester 2024

In this project, we prove the Schröder-Bernstein Theorem:
If two sets `X` and `Y` have injections `X → Y` and `Y → X`,
there exists a bijection `X → Y`.
You can find the set theoretic proof in our slides.

Since Lean is based on type theory (as opposed to set theory in the sense of ZFC),
we show the analogous statement where `X` and `Y` are types.

The idea and the setup is taken from the book Mathematics in Lean
by Jeremy Avigad and Patrick Massot (last accessed: 14.07.2024)
(https://leanprover-community.github.io/mathematics_in_lean/C04_Sets_and_Functions.html).
The example at the very end takes inspiration from the book How To Prove It With Lean
by Daniel Velleman (last accessed: 14.07.2024)
(https://djvelleman.github.io/HTPIwL/Chap8.html).

```lean
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Function
import Mathlib.Tactic.Ring
```

We want to do proofs by contradition and use the axiom of choice.
To make the code lighter we open the classical namespace.

```lean
open Classical

variable {α β : Type}

section SchroederBernsteinConstruction
```

We assume `Nonempty β` first. If `β` is empty, see `schroeder_bernstein` below.

```lean
variable [Nonempty β] (f : α → β) (g : β → α)
```

We define the following auxiliary function to help us define `sbSet f g`.
`sbAux f g n` corresponds to `Sₙ` from the maths part.

```lean
def sbAux : ℕ → Set α
  | 0 => Set.univ \ g '' Set.univ
  | n + 1 => g '' (f '' sbAux n)
```

We define `sbSet f g` as the union of `sbAux f g n` for all `n : ℕ`.
`sbSet f g` corresponds to `S` from the maths part.

```lean
def sbSet : Set α :=
  ⋃ n, sbAux f g n
```

We define our candidate for the bijection `α → β` : `sbFun`.
In the maths part we call this function `h`.

To do this, we need `Function.invFun g`.

`Function.invFun g` is a function `α → β` that chooses (an arbitrary) pre-image of `x : α` under `g`,
whenever such a pre-image exists and any element of `β` if it does not (here we use that `β` is non-empty
and the axiom of choice).

```lean
#check Function.invFun


noncomputable def sbFun (x : α) : β :=
  if x ∈ sbSet f g then f x else Function.invFun g x
```

In general, `Function.invFun` is not a right-inverse of `g` (because `g` is in general not surjective).
But outside of our auxiliary set `sbSet f g`, it is a right-inverse, as the next theorem shows.

```lean
theorem sb_right_inv {x : α} (hx : x ∉ sbSet f g) : g (Function.invFun g x) = x := by
```

We show that any `x`in the complement of `sbSet f g` is in fact in the image of `g`.

```lean
have : x ∈ g '' Set.univ := by
    contrapose! hx
    rw [sbSet, Set.mem_iUnion]
    use 0
    rw [sbAux, Set.mem_diff]
    constructor
    · simp
    · exact hx
```

Therefore we have a preimage `y` for any such `x`.

```lean
have : ∃ y, g y = x := by
    simp at this
    exact this
  obtain ⟨y, hy⟩ := this

  apply Function.invFun_eq
  use y
```

Remember that `sbFun`is our candidate for the bijection.
Therefore we want to show that it is both injective and surjective.

In the proof of surjectivity we'd like to use the `wlog` tactic.
It is similar to writing "without loss of generality" in informal maths.

```lean
#help tactic wlog


theorem sb_injective (hf : Function.Injective f) : Function.Injective (sbFun f g) := by
```

Remember that we'd like to call `sbSet f g` `S`and `sbFun f g` `h`.

```lean
set S := sbSet f g with S_def
  set h := sbFun f g with h_def

  intro x₁ x₂ (hxeq : h x₁ = h x₂)
  simp only [h_def, sbFun, ← S_def] at hxeq
```

Remember that we defined h on a case by case basis.

```lean
by_cases xS : x₁ ∈ S ∨ x₂ ∈ S
```

`x₁ ∈ S ∨ x₂ ∈ S`. In the following we'd like to assume `x₁ ∈ S`.

```lean
· wlog x₁S : x₁ ∈ S generalizing x₁ x₂ hxeq xS
```

This is the proof of the `wlog` statement.

```lean
· symm
      apply this hxeq.symm xS.symm (xS.resolve_left x₁S)

    · have x₂S : x₂ ∈ S := by

        apply _root_.not_imp_self.mp
        intro (x₂nS : x₂ ∉ S)
        rw [if_pos x₁S, if_neg x₂nS] at hxeq
        rw [S_def, sbSet, Set.mem_iUnion] at x₁S
        have x₂eq : x₂ = g (f x₁) := by
          rw [hxeq]
          rw [S_def] at x₂nS
          exact (sb_right_inv f g x₂nS).symm
        rcases x₁S with ⟨n, hn⟩
        rw [S_def, sbSet, Set.mem_iUnion]
        use n + 1
        simp [sbAux]
        exact ⟨x₁, hn, x₂eq.symm⟩

      rw[if_pos x₁S, if_pos x₂S] at hxeq
      apply hf at hxeq
      exact hxeq
```

`¬ x₁ ∈ S ∨ x₂ ∈ S`

```lean
· simp at xS
    rw[if_neg xS.left, if_neg xS.right] at hxeq
    rw[(sb_right_inv f g xS.left).symm, (sb_right_inv f g xS.right).symm, hxeq]
```

The definition `Function.Injective` is in the `Function` namespace,
as indicated by the prefix `Function.`.
If we want to save some characters, we can drop the `Function.`
by opening the `Function` namespace:

```lean
open Function

theorem sb_surjective (hg : Injective g) : Function.Surjective (sbFun f g) := by
```

As in the above proof, we rename `sbSet` and `sbFun`.

```lean
set S := sbSet f g with S_def
  set h := sbFun f g with h_def

  intro y
  by_cases gyS : g y ∈ S
```

`g y ∈ S`

```lean
· rw [S_def, sbSet, Set.mem_iUnion] at gyS
    rcases gyS with ⟨n, hn⟩
    rcases n with _ | n
    · simp [sbAux] at hn
    · simp [sbAux] at hn
      rcases hn with ⟨x, xmem, hx⟩
      use x
      have : x ∈ S := by
        rw [S_def, sbSet, Set.mem_iUnion]
        exact ⟨n, xmem⟩
      simp only [h_def, sbFun, if_pos this]
      exact hg hx
```

`g y ∉ S`

```lean
· simp [S_def] at gyS
    use g y
    simp [h_def, sbFun, if_neg gyS]
    rw [leftInverse_invFun]
    exact hg

end SchroederBernsteinConstruction

open Function
```

The Schröder-Bernstein Theorem for non-empty `β`.

```lean
theorem schroeder_bernstein_of_nonempty [Nonempty β] {f : α → β} {g : β → α} (hf : Injective f)
    (hg : Injective g) : ∃ h : α → β, Bijective h :=
  ⟨sbFun f g, sb_injective f g hf, sb_surjective f g hg⟩
```

In the proof of the Schröder Bernstein theorem for empty β we want to use that there exists a bijection
from an empty type to another empty type.

```lean
theorem empty_to_empty_bijection [h1 : IsEmpty α] [h2 : IsEmpty β] :
    ∃ h : α → β, Bijective h := by
  apply Equiv.equivEmpty at h1
  apply Equiv.equivEmpty at h2
  apply Equiv.symm at h2
  apply Equiv.trans h1 at h2
  obtain ⟨h, h_inv, l_inv, r_inv⟩ := h2
  use h
  rw [bijective_iff_has_inverse]
  use h_inv
```

The Schröder-Bernstein Theorem:
If we have an injection from `α` to `β` and an injection from `β` to `α`,
there exists a bijection from `α` to `β`.

```lean
theorem schroeder_bernstein {f : α → β} {g : β → α} (hf : Injective f)
    (hg : Injective g) : ∃ h : α → β, Bijective h := by
  by_cases h : Nonempty β
  · exact schroeder_bernstein_of_nonempty hf hg
  · have : IsEmpty α := by
      by_contra h1
      simp at h1
      obtain ⟨a⟩ := h1
      apply h
      use f a
    simp at h
    exact empty_to_empty_bijection
```

# Example
As an application of the Schröder-Bernstein theorem we can show that there exists
a bijection from `ℕ` to `ℤ`.

We define fnz : ℕ → ℤ as the inclusion of ℕ  in ℤ.

```lean
def fnz (n : Nat) : Int :=
  Int.ofNat n
```

We define fzn : ℤ → ℕ as the function that sends nonnegative integers to the even numbers
and negative integers to the odd numbers.

```lean
def fzn (z : Int) : Nat :=
  if 0 ≤ z then 2 * Int.toNat z
  else 2 * Int.toNat (-z - 1) + 1
```

Schröder-Bernstein requires that the functions are injective, we prove this in the following theorems.

```lean
theorem fnz_inj : Injective fnz := by
  intro x y
  rw [fnz, fnz]
  exact Int.ofNat.inj



theorem fzn_inj : Injective fzn := by

  intro a b h
  contrapose! h
  rw [fzn, fzn]
  have h2: 2 ≠ 0 := by exact two_ne_zero

  by_cases ha : 0 ≤ a

  · by_cases hb : 0 ≤ b
```

`0 ≤ a` and `0 ≤ b`

```lean
· rw [if_pos ha, if_pos hb, Nat.mul_ne_mul_right h2]
      rw[← Int.toNat_of_nonneg ha, ← Int.toNat_of_nonneg hb] at h
      contrapose! h
      rw[Int.ofNat_inj]
      exact h
```

`0 ≤ a` and `b < 0`

```lean
· rw[if_pos ha, if_neg hb]
      have h_even : Even (2 * a.toNat) := by exact even_two_mul a.toNat
      have h_odd : Odd (2 * (-b - 1).toNat + 1) := by
        rw[Nat.odd_iff_not_even]
        exact Nat.not_even_two_mul_add_one (-b - 1).toNat
      have h_sum_odd : Odd ((2 * a.toNat) + (2 * (-b - 1).toNat + 1)) := by
        exact Even.add_odd h_even h_odd
      exact Nat.ne_of_odd_add h_sum_odd

  · by_cases hb : 0 ≤ b
```

`a < 0` and `0 ≤ b`. Note that this is the same proof as in the above case.

```lean
· rw[if_neg ha, if_pos hb]
      have h_even : Even (2 * b.toNat) := by exact even_two_mul b.toNat
      have h_odd : Odd (2 * (-a - 1).toNat + 1) := by
        rw[Nat.odd_iff_not_even]
        exact Nat.not_even_two_mul_add_one (-a - 1).toNat
      have h_sum_odd : Odd ((2 * (-a - 1).toNat + 1) + (2 * b.toNat)) := by
        exact Even.odd_add h_even h_odd
      exact Nat.ne_of_odd_add h_sum_odd
```

`a < 0` and `b < 0`

```lean
· rw[if_neg ha, if_neg hb]
      contrapose! h
      simp at h
      simp at ha
      simp at hb
      rw[← Int.neg_inj]
      apply Nat.sub_one_cancel at h

      · apply Int.neg_pos_of_neg at ha
        apply Int.le_of_lt at ha
        apply Int.neg_pos_of_neg at hb
        apply Int.le_of_lt at hb
        rw [← Int.toNat_of_nonneg ha, ← Int.toNat_of_nonneg hb]
        norm_cast

      · simp
        exact ha

      · simp
        exact hb
```

We obtain a bijection from ℕ to ℤ by applying the Schröder Berstein theorem.

```lean
example : ∃ h : ℕ → ℤ, Bijective h := by
  exact schroeder_bernstein fnz_inj fzn_inj
```

# Axioms

```lean
-- Here we will investigate the axioms our theorem depends on.

#print axioms schroeder_bernstein

#check Classical.choice


#check propext

-- propext allows us to use the equivalent propositions freely

theorem thm₁ (a b c d e : Prop) (h : a ↔ b) : (c ∧ a ∧ d → e) ↔ (c ∧ b ∧ d → e) :=
  propext h ▸ Iff.refl _


-- funext can be derived from Classical.choice ∧ propext ∧ Quot

#check funext

-- It says that if two functions agree on each element, they are the same.
-- From a computational point of view, this is not the case as functions are
-- understood as algorithms.



#check Quot.sound

-- This axiom is used to show that if r a b, then in the newly constructed quotiont type,
-- they are represented by the same element. For example, let (a : ℕ) ∼ᵣ (b : ℕ) if a % 2 = b % 2
-- We can create a quotient type, ℕᵣ, which we can think it as {0,1}. This axioms says that a and
-- b are represented by the same element, say 0, in the new quotient type.

-- In ZFC, we can show these properties from the set extensionality and definition of relation.
-- Well-definedness issue?


#check Classical.em

-- "Diaconescu's theorem shows that the law of the excluded middle follows from
-- Classical.choice, propext, and funext.
-- Consequences of excluded middle include double-negation elimination, proof by cases,
-- and proof by contradiction."


#check α
#check Type
#check Type 0
#check Type 1
```
