# Involutions and commutativity

By Judith Ludwig, Christian Merten and Florent Schaffhauser,
Proseminar on computer-assisted mathematics,
Heidelberg, Summer Semester 2024

If a finite group has an involutive automorphism with no non-trivial fixed points, it is commutative. This is wrong, if the finiteness assumption is dropped.

This project sketch explores the proof of the result for finite groups
and constructs a counter-example in the non-finite case.

```lean
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.Data.Real.Basic

section

variable {G : Type} [Group G]
```

Given a group `G`, we say a group automorphism `σ` is an involution, if
`σ (σ x) = x` for all `x : G`.

Every group has a trivial involution, namely the identity.

```lean
lemma id_is_involution (x : G) : MulEquiv.refl G (MulEquiv.refl G x) = x := by
  rfl
```

Note: Since a group homomorphism is simply a monoid homomorphism of the underlying monoids, mathlib does not have a separate group homomorphism type.

A group isomorphism is called `MulEquiv` and is spelled `≃*`.

Note: In mathlib, additively and multiplicatively written groups are distinguished: There is `Group` and `AddGroup` (and similarly `CommGroup` and `AddCommGroup`). The corresponding homomorphisms are denoted by `→*` and `→*` respectively (for isomorphisms it is `≃*` and `≃+`).

Real negation as an additive group isomorphism.

```lean
def realNeg : ℝ ≃+ ℝ where
  toFun x := -x
  invFun x := -x
  left_inv x := by simp
  right_inv x := by simp
  map_add' x y := by ring
```

We can use the attribute `simps` to automatically generate auxiliary lemmas for `realNeg`. This allows the simplifier to rewrite `realNeg x` to `- x`.

Hint: Adding a `?` to `simps` yields a trace of the generated lemmas.

```lean
attribute [simps?] realNeg
```

The function `realNeg` is indeed an involution of the real numbers.

```lean
lemma realNeg_is_involution (x : ℝ) : realNeg (realNeg x) = x := by
  /- Add a `?` to see which lemmas were used. -/
  simp
```

Since mathematically speaking there is no difference between multiplicatively and additively written groups, there is a meta program converting proofs for one version to the other to avoid code duplication.

Therefore, from now on, we only care about multiplicatively written groups.

```lean
variable [Finite G]

lemma exists_eq_inv_apply (σ : G ≃* G) (hnofix : ∀ g, σ g = g → g = 1)
    (hinv : ∀ x, σ (σ x) = x) : ∀ g : G,
    ∃ (x : G), g = x⁻¹ * σ x := by
  intro g
  -- Hint: we need to show surjectivity of `x ↦ x⁻¹ * σ x`. For this, show injectivity first!
  have hinj : Function.Injective (fun x ↦ x⁻¹ * σ x) := by
    sorry
  sorry

lemma eq_inv (σ : G ≃* G) (hnofix : ∀ g, σ g = g → g = 1)
    (hinv : ∀ x, σ (σ x) = x) : ∀ g : G, σ g = g⁻¹ := by
  intro g
  -- We represent `g` using the lemma above.
  obtain ⟨x, h⟩ := exists_eq_inv_apply σ hnofix hinv g
  sorry
```

If a finite group has an involutive automorphism with no non-trivial fixed points, it is commutative.

```lean
theorem isCommutative (σ : G ≃* G) (hnofix : ∀ g, σ g = g → g = 1)
    (hinv : ∀ x, σ (σ x) = x) : ∀ a b : G, a * b = b * a := by
  intro a b
  calc a * b = a⁻¹⁻¹ * b⁻¹⁻¹ := by simp
           _ = (b⁻¹ * a⁻¹)⁻¹ := by simp
  /- continue calc block -/
  sorry

end
```

We now want to produce a counter-example to `isCommutative` when the assumption `Finite G` is dropped.

For this we consider the free group on `2` generators: `FreeGroup (Fin 2)`. Using the universal property of the free group, we can construct group homomorphisms into an arbitrary group. For example:

```lean
example : FreeGroup (Fin 2) →* Multiplicative ℤ :=
  FreeGroup.lift (fun j ↦ (j : ℤ))
```

The automorphism of `FreeGroup (Fin 2)` swapping the generators.

```lean
def swap : FreeGroup (Fin 2) ≃* FreeGroup (Fin 2) :=
  MonoidHom.toMulEquiv
    sorry
    sorry
    sorry
    sorry
```

Now state and prove that `swap` is an involution, has no non-trivial fixed points but `FreeGroup (Fin 2)` is not-abelian.
