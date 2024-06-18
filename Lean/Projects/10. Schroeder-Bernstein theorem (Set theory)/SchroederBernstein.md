# The Schröder-Bernstein Theorem

By Judith Ludwig, Christian Merten and Florent Schaffhauser,
Proseminar on computer-assisted mathematics,
Heidelberg, Summer Semester 2024

In this project, we prove the Schröder-Bernstein Theorem: If two sets `X` and `Y` have injections `X → Y` and `Y → X`, there exists a bijection `X → Y`.

Since Lean is based on type theory (as opposed to set theory in the sense of ZFC), we show the analogous statement where `X` and `Y` are types.

The idea and the setup is taken from the book Mathematics in Lean by Jeremy Avigad and Patrick Massot (https://leanprover-community.github.io/mathematics_in_lean/C04_Sets_and_Functions.html). You can find more explanations and even pictures at the previous link.

```lean
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Function
```

We want to do proofs by contradition and use the axiom of choice. To make the code lighter we open the classical namespace.

```lean
open Classical

variable {α β : Type}

section WarmUp
```

To get used to working with sets and functions in Lean, here are some warm-up exercises.

```lean
variable (f : α → β) (s t : Set α)

example : s \ (t ∪ u) ⊆ (s \ t) \ u := by
  intro a ⟨ha1, ha2⟩
  -- Found using `simp?`
  simp only [Set.mem_union, not_or] at ha2
  -- This line is optional, but it lets you understand what to show.
  simp only [Set.mem_diff]
  constructor
  · constructor
    · exact ha1
    · exact ha2.left
  · exact ha2.right
```

Given s of type Set α, the image of s under f is denoted by f '' s. For the preimage we use f ⁻¹' where the exponent -1 can be typed by `\-` or `\-1`.

```lean
example (hf : Function.Injective f) : f ⁻¹' (f '' s) ⊆ s := by
  intro a ha
  simp at ha
  obtain ⟨x, hxins, hfx⟩ := ha
  -- The library search tactic `exact?` can be used not only to search lemma names in the library, but also how to apply local hypothesis to simple goals.
  have hxa : x = a := by exact?
  -- See `#help tactic subst` if you want to learn about a tactic.
  subst hxa
  exact hxins

example : f '' (f ⁻¹' u) ⊆ u := by
  sorry

example (h : Function.Surjective f) : u ⊆ f '' (f ⁻¹' u) := by
  sorry

example (h : s ⊆ t) : f '' s ⊆ f '' t := by
  sorry

end WarmUp

section SchroederBernsteinConstruction
```

We assume `Nonempty β` first. If `β` is empty, the proof is easy (see `schroeder_bernstein` below).

```lean
variable [Nonempty β] (f : α → β) (g : β → α)
```

The natural numbers `ℕ` are defined inductively. Hence to define a function from `ℕ`, we may define it for `0` (base case) and for every natural number of the form `n + 1`, where we may use the definition for `n` (induction step).

An example is the following function, which is an auxiliary function to define `sbSet`.

```lean
def sbAux : ℕ → Set α
  | 0 => Set.univ \ g '' Set.univ
  | n + 1 => g '' (f '' sbAux n)
```

The union of `sbAux f g n` for all `n : ℕ`.

```lean
def sbSet : Set α :=
  ⋃ n, sbAux f g n
```

To define our candidate bijection, we need `Function.invFun `g`.

`Function.invFun g` is a function `α → β` that chooses (an arbitrary) pre-image of `x : α` under `g`, whenever such a pre-image exists and any element of `β` if it does not (here we use that `β` is non-empty).

(This uses the axiom of choice! Why?)

```lean
#check Function.invFun
```

Our candidate for the bijection `α → β`.

```lean
noncomputable def sbFun (x : α) : β :=
  if x ∈ sbSet f g then f x else Function.invFun g x
```

In general, `Function.invFun` is not a right-inverse of `g` (because `g` is in general not surjective). But outside of our auxiliary set `sbSet f g`, it is a right-inverse, as the next theorem shows.

```lean
theorem sb_right_inv {x : α} (hx : x ∉ sbSet f g) : g (Function.invFun g x) = x := by
  have : x ∈ g '' Set.univ := by
    contrapose! hx
    rw [sbSet, Set.mem_iUnion]
    use 0
    rw [sbAux, Set.mem_diff]
    sorry
  have : ∃ y, g y = x := by
    sorry
  sorry
```

If a proof is symmetric with respect to two variables, in informal maths we write "without loss of generality ...". A similar thing can be done in Lean using the `wlog` tactic.

```lean
#help tactic wlog
```

Hint: you need to use `sb_right_inv` in the proof.

```lean
theorem sb_injective (hf : Function.Injective f) : Function.Injective (sbFun f g) := by
  set A := sbSet f g with A_def
  set h := sbFun f g with h_def
  intro x₁ x₂ (hxeq : h x₁ = h x₂)
  simp only [h_def, sbFun, ← A_def] at hxeq
  by_cases xA : x₁ ∈ A ∨ x₂ ∈ A
  · wlog x₁A : x₁ ∈ A generalizing x₁ x₂ hxeq xA
    · symm
      apply this hxeq.symm xA.symm (xA.resolve_left x₁A)
    have x₂A : x₂ ∈ A := by
      /- Try to omit the `_root_` here, to understand why it is needed. -/
      apply _root_.not_imp_self.mp
      intro (x₂nA : x₂ ∉ A)
      rw [if_pos x₁A, if_neg x₂nA] at hxeq
      rw [A_def, sbSet, Set.mem_iUnion] at x₁A
      have x₂eq : x₂ = g (f x₁) := by
        sorry
      rcases x₁A with ⟨n, hn⟩
      rw [A_def, sbSet, Set.mem_iUnion]
      use n + 1
      simp [sbAux]
      exact ⟨x₁, hn, x₂eq.symm⟩
    sorry
  · simp at xA
    sorry
```

The definition `Function.Injective` is in the `Function` namespace, as indicated by the prefix `Function.`. If we want to save some characters, we can drop the `Function.` by opening the `Function` namespace:

```lean
open Function

theorem sb_surjective (hf : Injective f) (hg : Injective g) : Function.Surjective (sbFun f g) := by
  -- We introduce auxiliary variables using `set`. `A_def` contains the defining equality.
  set A := sbSet f g with A_def
  set h := sbFun f g with h_def
  intro y
  by_cases gyA : g y ∈ A
  · rw [A_def, sbSet, Set.mem_iUnion] at gyA
    rcases gyA with ⟨n, hn⟩
    rcases n with _ | n
    · simp [sbAux] at hn
    simp [sbAux] at hn
    rcases hn with ⟨x, xmem, hx⟩
    use x
    have : x ∈ A := by
      rw [A_def, sbSet, Set.mem_iUnion]
      exact ⟨n, xmem⟩
    simp only [h_def, sbFun, if_pos this]
    exact hg hx
  · sorry

end SchroederBernsteinConstruction

open Function
```

The Schröder-Bernstein Theorem for non-empty `β`.

```lean
theorem schroeder_bernstein_of_nonempty [Nonempty β] {f : α → β} {g : β → α} (hf : Injective f)
    (hg : Injective g) : ∃ h : α → β, Bijective h :=
  ⟨sbFun f g, sb_injective f g hf, sb_surjective f g hf hg⟩
```

The Schröder-Bernstein Theorem: If we have an injection from `α` to `β` and an injection from `β` to `α`, there exists a bijection from `α` to `β`.

```lean
theorem schroeder_bernstein {f : α → β} {g : β → α} (hf : Injective f)
    (hg : Injective g) : ∃ h : α → β, Bijective h := by
  by_cases h : Nonempty β
  · exact schroeder_bernstein_of_nonempty hf hg
  · simp at h
    use f
    sorry
```
