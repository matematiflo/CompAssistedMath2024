/-
# Involutions and commutativity
by Lukas Wrana,

based on a sketch by Judith Ludwig, Christian Merten and Florent Schaffhauser,
Proseminar on computer-assisted mathematics,
Heidelberg, Summer Semester 2024

If a finite group has an involutive automorphism with no non-trivial fixed
points, it is commutative. This is wrong, if the finiteness assumption is
dropped.

This project explores the proof of the result for finite groups and constructs
a counter-example in the non-finite case.
-/

import Mathlib.Tactic.Ring
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card

section

variable {G : Type} [Group G]

/-
Given a group `G`, we say a group automorphism `σ` is an involution, if
`σ (σ x) = x` for all `x : G`.
-/

/-
Every group has a trivial involution, namely the identity.
-/

lemma id_is_involution (x : G) : MulEquiv.refl G (MulEquiv.refl G x) = x := by
  rfl

/-
Note: Since a group homomorphism is simply a monoid homomorphism of the
underlying monoids, mathlib does not have a separate group homomorphism type.

A group isomorphism is called `MulEquiv` and is spelled `≃*`.
-/

/-
Another interesting result regarding involutions is, that the number
of involutions (including the identity involution) over a finite group is given by
the following recurrence relation:
-/

def num_involutions : ℕ → ℕ
| 0 => 0
| 1 => 1
| (n + 2) => num_involutions (n + 1) + n * num_involutions n

/-
Note: I probably won't be able to show this result, due to the lack of time.
-/

/-
Note: In mathlib, additively and multiplicatively written groups are
distinguished: There is `Group` and `AddGroup` (and similarly `CommGroup` and
`AddCommGroup`). The corresponding homomorphisms are denoted by `→*` and `→*`
respectively (for isomorphisms it is `≃*` and `≃+`).
-/

/-
Real negation as an additive group isomorphism.
-/

def realNeg : ℝ ≃+ ℝ where
  toFun x := -x
  invFun x := -x
  left_inv x := by simp
  right_inv x := by simp
  map_add' x y := by ring

/-
We can use the attribute `simps` to automatically generate auxiliary lemmas
for `realNeg`. This allows the simplifier to rewrite `realNeg x` to `- x`.

Hint: Adding a `?` to `simps` yields a trace of the generated lemmas.
-/

attribute [simps] realNeg

/-
The function `realNeg` is indeed an involution of the real numbers.
-/

lemma realNeg_is_involution (x : ℝ) : realNeg (realNeg x) = x := by
  /- Add a `?` to see which lemmas were used. -/
  simp

/-
Since mathematically speaking there is no difference between multiplicatively
and additively written groups, there is a meta program converting proofs for
one version to the other to avoid code duplication.

Therefore, from now on, we only care about multiplicatively written groups.
-/

variable [Finite G]

lemma exists_eq_inv_apply (σ : G ≃* G) (hnofix : ∀ g, σ g = g → g = 1)
    (hinv : ∀ x, σ (σ x) = x) : ∀ g : G, ∃ (x : G), g = x⁻¹ * σ x := by
  intro g
  -- We need to show surjectivity of `x ↦ x⁻¹ * σ x`. For this, we
  -- show injectivity first!
  have hinj : Function.Injective (fun x ↦ x⁻¹ * σ x) := by
    intro x y h
    have: x⁻¹ * σ x = y⁻¹ * σ y := h

    have: x = σ x * σ y⁻¹ * y := by
      calc x = σ (σ x)                 := (hinv x).symm
           _ = σ (x * (x⁻¹ * σ x))     := by rw [← mul_assoc, mul_inv_self, one_mul]
           _ = σ (x * (y⁻¹ * σ y))     := by rw [this]
           _ = σ x * σ (y⁻¹ * σ y)     := by rw [map_mul]
           _ = σ x * (σ y⁻¹ * σ (σ y)) := by rw [map_mul]
           _ = σ x * (σ y⁻¹ * y)       := by rw [hinv]
           _ = σ x * σ y⁻¹ * y         := by rw [mul_assoc]

    have: x * y⁻¹ = σ (x * y⁻¹) := by
      calc x * y⁻¹ = σ x * σ y⁻¹ * y * y⁻¹   := by rw [← this]
                 _ = σ x * σ y⁻¹ * (y * y⁻¹) := by rw [mul_assoc]
                 _ = σ x * σ y⁻¹ * 1         := by rw [mul_inv_self]
                 _ = σ x * σ y⁻¹             := by rw [mul_one]
                 _ = σ (x * y⁻¹)             := by rw [← map_mul]

    have h_eq_one : x * y⁻¹ = 1 := by
      apply hnofix
      exact this.symm
    exact mul_inv_eq_one.mp h_eq_one

  have hbij : Function.Bijective (fun x ↦ x⁻¹ * σ x) :=
    Function.Injective.bijective_of_finite hinj

  obtain ⟨x, hx⟩ := hbij.surjective g
  use x
  exact hx.symm

lemma eq_inv (σ : G ≃* G) (hnofix : ∀ g, σ g = g → g = 1)
    (hinv : ∀ x, σ (σ x) = x) : ∀ g : G, σ g = g⁻¹ := by
  intro g
  -- We represent `g` using the lemma above.
  obtain ⟨x, h⟩ := exists_eq_inv_apply σ hnofix hinv g

  calc σ g = σ (x⁻¹ * σ x)   := by rw [h]
         _ = σ x⁻¹ * σ (σ x) := by rw [map_mul]
         _ = σ x⁻¹ * x       := by rw [hinv]
         _ = (σ x)⁻¹ * x     := by rw [map_inv]
         _ = (x⁻¹  * σ x)⁻¹  := by rw [mul_inv_rev, inv_inv]
         _ = g⁻¹             := by rw [h]

/-
If a finite group has an involutive automorphism with no non-trivial fixed
points, it is commutative.
-/

theorem is_commutative (σ : G ≃* G) (hnofix : ∀ g, σ g = g → g = 1)
    (hinv : ∀ x, σ (σ x) = x) : ∀ a b : G, a * b = b * a := by
  intro a b

  calc a * b = a⁻¹⁻¹ * b⁻¹⁻¹ := by simp
           _ = (b⁻¹ * a⁻¹)⁻¹ := by simp
           _ = σ (b⁻¹ * a⁻¹) := by rw [eq_inv σ hnofix hinv]
           _ = σ b⁻¹ * σ a⁻¹ := by exact MulEquiv.map_mul σ _ _
           _ = b⁻¹⁻¹ * σ a⁻¹ := by rw [eq_inv σ hnofix hinv]
           _ = b * σ a⁻¹     := by simp
           _ = b * a⁻¹⁻¹     := by rw [eq_inv σ hnofix hinv]
           _ = b * a         := by simp

end

/-
We now want to produce a counter-example to `is_commutative` when the
assumption `Finite G` is dropped.

For this we consider the free group on `2` generators: `FreeGroup (Fin 2)`.
Using the universal property of the free group, we can construct group
homomorphisms into an arbitrary group. For example:
-/

example : FreeGroup (Fin 2) →* Multiplicative ℤ :=
  FreeGroup.lift (fun j ↦ (j : ℤ))

/-
The automorphism of `FreeGroup (Fin 2)` swapping the generators.
-/

def swap : FreeGroup (Fin 2) ≃* FreeGroup (Fin 2) :=
  MonoidHom.toMulEquiv
    -- Because `Fin 2` has only two elements `0` and `1`, `1 - i` will
    -- always yield the other element, thus swapping the generators.
    (FreeGroup.lift (fun i ↦ FreeGroup.of (1 - i)))
    (FreeGroup.lift (fun i ↦ FreeGroup.of (1 - i)))
    (by
      ext x
      simp
      match x with
      | 0 => rfl
      | 1 => rfl)
    (by
      ext x
      simp
      match x with
      | 0 => rfl
      | 1 => rfl)

/-
Now we want to prove that `swap` is an involution, has no non-trivial fixed
points but `FreeGroup (Fin 2)` is not-abelian.
-/

lemma swap_is_involution : ∀ x, swap (swap x) = x := by
  intro x
  simp [swap]
  induction x using FreeGroup.induction_on with
  | C1 => simp
  | Cp =>
    sorry

  | Ci =>
    sorry

  | Cm =>
    sorry


lemma swap_no_fixed_points : ∀ g, swap g = g → g = 1 := by
  intro g hg
  by_contra h
  have : g ≠ swap g := by
    intro heq
    rw [heq] at h
    induction g using FreeGroup.induction_on with
    | C1 =>
      simp [swap] at heq
      simp [swap] at h

    | Cp =>
      sorry

    | Ci =>
      sorry

    | Cm =>
      sorry

  have : swap g = g := hg

  sorry


theorem FreeGroup_not_commutative : ¬(∀ a b : FreeGroup (Fin 2), a * b = b * a) := by
  intro h
  let a := FreeGroup.of 0
  let b := FreeGroup.of 1
  have h_comm := h a b
  have h_swap : swap (a * b) ≠ b * a := by
    simp [swap, a, b, FreeGroup.of]
    intro contra

    sorry
  have h_eq : swap (a * b) = b * a := by

    sorry
  contradiction
