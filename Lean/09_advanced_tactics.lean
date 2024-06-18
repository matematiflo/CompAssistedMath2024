/-
# Advanced tactics

By Judith Ludwig and Florent Schaffhauser,
Proseminar on computer-assisted mathematics,
Heidelberg, Summer Semester 2024
-/

import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.BigOperators.Group.Finset

/-
In this file, we explain the `calc` environment and introduce the following tactics:

- `ext`
- `ring`
- `use`
- `simp`

## The `calc` environment

For some proofs in mathematics, the best strategy is to rewrite an expression multiple times and at each step justify the rewriting. We often do this automatically without giving explicit arguments. In Lean, we have to provide them. As you learned in the NNG, you can use the rewrite tactic `rw`.
-/

example (a b : ℝ) : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by
  rw [mul_add, add_mul, add_mul]
  rw [← add_assoc, add_assoc (a * a)]
  rw [mul_comm b a, two_mul]

/-
Using the Lean Infoview one can see the progress in the goal and follow the above proof. From the code alone, this is really hard. For such a situation Lean has the so-called `calc` environment. The syntax is a bit tricky.
-/

example (a b : ℝ) : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
  calc
    (a + b) * (a + b) = a * a + b * a + (a * b + b * b) := by sorry
    _ = a * a + (b * a + a * b) + b * b := by sorry
    _ = a * a + 2 * (a * b) + b * b := by sorry

/-
Try proving the following using a calc proof.
-/

example (a b c d : ℝ): (a + b) * (c + d) = a * c + a * d + b * c + b * d := by sorry

/-
Here is an example from group theory. Let us see how to handle groups in Lean.
-/

variable {G : Type} [Group G]

/-
In mathematics we learn that a group is a set with an associative multiplication, an identity and inverses. So in Lean a group `G` is a term of type `Type` plus the extra structure.

In fact, Lean builds Groups on Monoids. If you hover over `Group`, you'll see the following definition:
"A Group is a Monoid with an operation `⁻¹` satisfying `g⁻¹ * g = 1`."

Note that we only require `g` to have a left inverse.
The theorem `mul_left_inv` says that for any element `g` in the group, `g⁻¹ * g = 1`.

Let us use a calc environment to show from the group axioms, that a left inverse in a group is also a right inverse.

See if you can solve this using only the three theorems `mul_assoc`, `one_mul`and `mul_left_inv`.
-/

#check mul_assoc
#check one_mul
#check mul_left_inv

lemma rightinv (g : G) : g * g⁻¹ = 1 :=
  calc
    g * g⁻¹ = 1 * g * g⁻¹ := by sorry
    _ = (g * g⁻¹)⁻¹ * (g * g⁻¹) * g * g⁻¹ := by rw [mul_left_inv (g * g⁻¹)]
    _ = (g * g⁻¹)⁻¹ * g * (g⁻¹ * g) * g⁻¹:= by rw [← mul_assoc (g * g⁻¹)⁻¹ g]; sorry
    _ = (g * g⁻¹)⁻¹ * g * 1 * g⁻¹ := by sorry
    _ = (g * g⁻¹)⁻¹ * (g * g⁻¹) := by sorry
    _ = 1 := by sorry

/-

## The `ext` tactic

If we want to prove an equality of two sets, we can do this by showing they contain the same sets of elements.
If we want to prove an equality of two functions, we can do this by showing their values agree on each argument.

This principle is known as *extensionality* and Lean has a tactic, called `ext`, that can deal with this. This tactic applies so called "extensionality lemmas" and replaces an "equality goal" by a "show it for an arbitrary input" goal. Let us see some examples.
-/

variable {α : Type*}
variable (s t : Set α)
open Set

example : s ∩ t = t ∩ s := by
  ext x
  constructor
  · rintro ⟨xs, xt⟩
    exact ⟨xt, xs⟩
  . sorry

example : (fun a b : ℝ ↦ (a + b) ^ 2) = fun a b : ℝ ↦ a ^ 2 + 2 * a * b + a ^ 2 := by
  ext a b
  sorry -- easier to fill this sorry only after learning about the ring tactic

example (G H : Type) [Group G] [Group H] (φ ψ : G →* H)
    (h : ∀ g, φ g = ψ g) : φ = ψ := by
  ext g
  apply h

#check MonoidHom.ext

/-
## The `ring` tactic

The `ring` tactic proves algebraic identities in commutative rings that follow purely from the ring axioms. The commutative ring can be an abstract commutative ring `R` or a concrete instance like the reals `ℝ`. The `ring` tactic will not take into account local assumptions.
-/

example (a b : ℝ) : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by
  sorry

/-
It even works on some results in semiring such as `ℕ`. Try replacing `ℝ` by `ℕ` in the above example.
-/

example (a b : ℝ) : (a + b) * (a - b) = a * a - b * b := by
  sorry

/-
## The `use` tactic

If our goal is of the form `∃ ...` then the `use` tactic helps us make progress. For example, if our goal is to show that there exists a real number `x` with `x ≥ 0`, writing `use 1` will replace `x` with `1`
-/

example : ∃ (x : ℝ), x ≥ 0 := by
  use 1
  sorry

variable {G : Type} [Group G]

example (g : G) : ∃ h, g * h = 1 := by
  use g⁻¹
  exact rightinv g

/-
## The `simp` tactic

The `simp` tactic is Lean's simplifier. It tries to apply lemmas that have a `simp` attribute. (A simp attribute is added by putting a tag @[simp]).

Theorems tagged with the simp attribute are used by the simplifier (i.e., the simp tactic, and its variants) to simplify expressions occurring in your goals. Theorems tagged with the simp attribute are called "simp theorems" or "simp lemmas". Here is an example.
-/

@[simp] theorem ne_eq' (a b : α) : (a ≠ b) = ¬ (a = b) := rfl

/-
This simp theorem instructs the simplifier to replace instances of the term `a ≠ b` with `Not (a = b)`.
-/

example (a : ℝ) : a + 0 = a  := by
  simp

/-
We can use simp at a local hypothesis `h`, by typing `simp at h`.
-/

example (a b : ℝ) (h: a = b + 0) : a = b := by
   simp at h
   exact h

/-
We can add rules to the simplifier using `simp [h₁, h₂, ..., hₙ]`. This simplifies the goal using the lemmas tagged with the attribute [simp] and the given expressions hᵢ's.
-/

example (a b : G) (h: a * b = 1 ) : a * b * 1 = 1 := by
   simp [h]

/-
The variant `simp only [h₁, h₂, ..., hₙ]` simplifies the goal using only the given expressions `hᵢ`'s and not using the lemmas tagged with the attribute [simp].

Let's see an example. For that take a commutative group.
-/

variable {G : Type} [CommGroup G]

example (a b c d : G) (h: a * b = 1 ) :  b * a * c * d = d * c := by
   simp only [mul_comm b a]
   sorry

/-
## The `congr` tactic

In mathematics, we constantly use the following facts:

- If `x₁ = x₂` (as terms of type `X`) and `f : X → Y`, then `f x₁ = f x₂`.
- If `x : X` and `f = g` (as terms of type `X → Y`), then `f x = g x`.
- If `x₁ = x₂` and `f = g`, then `f x₁ = g x₂`.

In Lean, we can use the `congr` tactic (short for *congruence*) to reduce the goal equalities above to the assumptions of those lemmas. By the way, can you formalize and prove those lemmas? Here is the first statement formalized for you.
-/

example {X Y : Type} {f : X → Y} {x₁ x₂ : X} (h : x₁ = x₂) : f x₁ = f x₂ := by
  sorry

/-
In the following example, the `congr` tactic is capable of reducing the equality `g (f x) = g (f x')` to `x = x'`. Note that there is no term `h : x = x'` in our local context, so we cannot close the goal after that.
-/

variable {X Y Z : Type} {f : X → Y} {g : Y → Z} {x x' : X}

example : g (f x) = g (f x') := by
  congr
  sorry

/-
If we add the term `h : x = x'`, then the `congr` tactic closes the goal automatically.
-/

example {h : x = x'} : g (f x) = g (f x') := by
  congr

/-
Note that we can choose how many times we use the `congr` tactic. For instance, in the previous example, we can use it just once, to reduce the goal to `f x = f x'`.
-/

example : g (f x) = g (f x') := by
  congr 1
  sorry

/-
If we add the term `h : f x = f x'`, then either `congr 1` or `congr` closes the goal automatically.
-/

example {h : f x = f x'} : g (f x) = g (f x') := by
  congr 1

/-
Note that if we write `(g ∘ f) x = (g ∘ f) x'` instead of `g (f x) = g (f x')`, then `congr 1` already reduces the goal to `x = x'`. If we want to reduce it to `f x = f x'` instead, we need to rewrite `g ∘ f` first.
-/

example : (g ∘ f) x = (g ∘ f) x' := by
  -- simp only [Function.comp_apply]
  congr 1
  sorry

/-
There are many more tactics that make formalizing mathematics in Lean easier. For an overview of the most important ones see for example [this blog post](
https://www.ma.imperial.ac.uk/~buzzard/xena/formalising-mathematics-2024/Part_C/Part_C.html).

Here is an exercise to practice some of the tactics encountered in this file and more (like `induction`, for instance). We recommend to do it on paper first!
-/

variable (u v : ℕ → ℝ) (h : ∀ k : ℕ, v k = u (k + 1) - u k)

theorem telescopic_sum_and_average : ∀ n : ℕ, ((∑ i : Fin (n + 1), v i) + u 0) / (n + 1)= u (n + 1) / (n + 1) := by
  sorry
