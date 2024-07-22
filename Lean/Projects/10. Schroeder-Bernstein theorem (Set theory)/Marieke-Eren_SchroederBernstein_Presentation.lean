/-
# The Schröder-Bernstein Theorem

Project by Marieke and Eren
-/

import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Function
import Mathlib.Tactic.Ring


open Classical

variable {α β : Type}


section SchroederBernsteinConstruction



-- Assume `Nonempty β` first.

variable [Nonempty β] (f : α → β) (g : β → α)



-- Define auxiliary function `sbAux`.
-- `sbAux f g n` corresponds to `Sₙ` from the maths part.

def sbAux : ℕ → Set α
  | 0 => Set.univ \ g '' Set.univ
  | n + 1 => g '' (f '' sbAux n)



-- Define the union of `sbAux f g n` for all `n : ℕ`.
-- `sbSet f g` corresponds to `S` from the maths part.

def sbSet : Set α :=
  ⋃ n, sbAux f g n



-- Define our candidate for the bijection `α → β`.
-- `sbFun` corresponds to `h` from the maths part.

noncomputable def sbFun (x : α) : β :=
  if x ∈ sbSet f g then f x else Function.invFun g x



-- Show that `Function.invFun g` is a right-inverse of `g` on the complement of `sbSet f g`.

theorem sb_right_inv {x : α} (hx : x ∉ sbSet f g) : g (Function.invFun g x) = x := by

-- We show that any `x`in the complement of `sbSet f g` is in fact in the image of `g`.
  have : x ∈ g '' Set.univ := by
    contrapose! hx
    rw [sbSet, Set.mem_iUnion]
    use 0
    rw [sbAux, Set.mem_diff]
    constructor
    · simp
    · exact hx

-- Therefore we have a preimage `y` for any such `x`.
  have : ∃ y, g y = x := by
    simp at this
    exact this
  obtain ⟨y, hy⟩ := this

  apply Function.invFun_eq
  use y


-- Show that `sbFun` is injective.

theorem sb_injective (hf : Function.Injective f) : Function.Injective (sbFun f g) := by

-- Remember that we'd like to call `sbSet f g` `S`and `sbFun f g` `h`.
  set S := sbSet f g with S_def
  set h := sbFun f g with h_def

  intro x₁ x₂ (hxeq : h x₁ = h x₂)
  simp only [h_def, sbFun, ← S_def] at hxeq

-- Remember that we defined h on a case by case basis, so it makes sense to use the `by_cases` tactic.
  by_cases xS : x₁ ∈ S ∨ x₂ ∈ S

-- `x₁ ∈ S ∨ x₂ ∈ S`
-- In the following we'd like to assume `x₁ ∈ S`.
  · wlog x₁S : x₁ ∈ S generalizing x₁ x₂ hxeq xS

-- This is the proof of the `wlog` statement.
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

-- `¬ x₁ ∈ S ∨ x₂ ∈ S`
  · simp at xS
    rw[if_neg xS.left, if_neg xS.right] at hxeq
    rw[(sb_right_inv f g xS.left).symm, (sb_right_inv f g xS.right).symm, hxeq]


open Function


-- Show that `sbFun`is surjective.

theorem sb_surjective (hg : Injective g) : Function.Surjective (sbFun f g) := by

-- As in the above proof, we rename `sbSet` and `sbFun`.
  set S := sbSet f g with S_def
  set h := sbFun f g with h_def

  intro y
  by_cases gyS : g y ∈ S

-- `g y ∈ S`
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

-- `g y ∉ S`
  · simp [S_def] at gyS
    use g y
    simp [h_def, sbFun, if_neg gyS]
    rw [leftInverse_invFun]
    exact hg

end SchroederBernsteinConstruction


open Function

-- Prove the Schröder-Bernstein Theorem for non-empty `β`.

theorem schroeder_bernstein_of_nonempty [Nonempty β] {f : α → β} {g : β → α} (hf : Injective f)
    (hg : Injective g) : ∃ h : α → β, Bijective h :=
  ⟨sbFun f g, sb_injective f g hf, sb_surjective f g hg⟩



-- Show that there exists a bijection from an empty type to another empty type.

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



--Prove the Schröder-Berstein Theorem.

theorem schroeder_bernstein {f : α → β} {g : β → α} (hf : Injective f)
    (hg : Injective g) : ∃ h : α → β, Bijective h := by

  by_cases h : Nonempty β

-- `Nonempty β`
  · exact schroeder_bernstein_of_nonempty hf hg

-- `Empty β`
  · have : IsEmpty α := by
      by_contra h1
      simp at h1
      obtain ⟨a⟩ := h1
      apply h
      use f a
    simp at h
    exact empty_to_empty_bijection



/-
# Example
There is a bijection from `ℕ` to `ℤ`.
-/


-- Define `fnz : ℕ → ℤ` as the inclusion of `ℕ` into `ℤ`.

def fnz (n : Nat) : Int :=
  Int.ofNat n



-- Define fzn : ℤ → ℕ as the function that sends nonnegative integers to the even numbers
-- and negative integers to the odd numbers.

def fzn (z : Int) : Nat :=
  if 0 ≤ z then 2 * Int.toNat z
  else 2 * Int.toNat (-z - 1) + 1



-- Show that `fnz`and `fzn` are injective.

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

-- `0 ≤ a` and `0 ≤ b`
    · rw [if_pos ha, if_pos hb, Nat.mul_ne_mul_right h2]
      rw[← Int.toNat_of_nonneg ha, ← Int.toNat_of_nonneg hb] at h
      contrapose! h
      rw[Int.ofNat_inj]
      exact h

-- `0 ≤ a` and `b < 0`
    · rw[if_pos ha, if_neg hb]
      have h_even : Even (2 * a.toNat) := by exact even_two_mul a.toNat
      have h_odd : Odd (2 * (-b - 1).toNat + 1) := by
        rw[Nat.odd_iff_not_even]
        exact Nat.not_even_two_mul_add_one (-b - 1).toNat
      have h_sum_odd : Odd ((2 * a.toNat) + (2 * (-b - 1).toNat + 1)) := by
        exact Even.add_odd h_even h_odd
      exact Nat.ne_of_odd_add h_sum_odd

  · by_cases hb : 0 ≤ b

-- `a < 0` and `0 ≤ b`
-- Note that this is the same proof as in the above case.
    · sorry

-- `a < 0` and `b < 0`
    · sorry



-- Obtain a bijection by Schröder-Berstein theorem.

example : ∃ h : ℕ → ℤ, Bijective h := by
  exact schroeder_bernstein fnz_inj fzn_inj




/-
# Axioms
-/

-- Here we will investigate the axioms our theorem depends on.

#print axioms schroeder_bernstein
#print axioms schroeder_bernstein_of_nonempty

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
