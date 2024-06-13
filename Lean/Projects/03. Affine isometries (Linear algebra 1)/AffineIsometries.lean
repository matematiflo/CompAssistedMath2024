/-
# Affine isometries

By Judith Ludwig, Christian Merten and Florent Schaffhauser,
Proseminar on computer-assisted mathematics,
Heidelberg, Summer Semester 2024

In this project sketch we define affine isometries and show that they are always of the form `x ↦ g *ᵥ x + y` for some orthogonal matrix `g`.
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.UnitaryGroup

variable {n : ℕ}

open Matrix

/-
We can search the standard library with the library search tactic `exact?`
-/

example (x y : EuclideanSpace ℝ (Fin n)) :
    ‖x - y‖ ^ 2 = ‖x‖ ^ 2 - 2 * ⟪x, y⟫_ℝ + ‖y‖ ^ 2 := by
  exact?

section WarmUp

/-
This section is for making our life a bit easier.

The first lemma gives (the formula, or better) the function for multiplying a matrix g with a vector of the form (0,..,a,...,0), where a is in position i. This function is a function (Fin n) → ℝ, i.e. a vector in ℝ^n.

The second lemma shows that giving a linear endomorphism of ℝ^n means giving a matrix.
-/

@[simp]
lemma Matrix.mulVec_euclideanSpace_single (g : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) (a : ℝ) :
    g *ᵥ EuclideanSpace.single i a = fun j ↦ g j i * a := by
  show g *ᵥ Pi.single i a = fun j ↦ g j i * a
  simp

variable (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))

lemma eq_matrix (hf : IsLinearMap ℝ f) :
    ∃ g : Matrix (Fin n) (Fin n) ℝ, ∀ (x : EuclideanSpace ℝ (Fin n)), f x = g *ᵥ x := by
  /- First reflex when proving something on vector spaces: pick a basis! -/
  let b : Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)) := PiLp.basisFun 2 ℝ (Fin n)
  /- Try to understand what this means. -/
  let g : Matrix (Fin n) (Fin n) ℝ := fun i j ↦ f (b j) i
  use g
  intro x
  have hx : x ∈ Submodule.span ℝ (Set.range b) := by simp
  -- To show something on every element of `EuclideanSpace ℝ (Fin n)` it suffices to check that the property is stable under addition, scalar multiplication, holds for zero and finally to check it on generators of `EuclideanSpace ℝ (Fin n)`. In this case we choose the standard basis.
  -- Now try to fill in the gaps.
  refine Submodule.span_induction hx ?_ ?_ ?_ ?_
  · rintro z ⟨i, rfl⟩
    simp [g, b]
  · simp [hf.map_zero]
  · intro x y hx hy
    rw [hf.map_add, mulVec_add]
    sorry
  · sorry
end WarmUp

/-
An affine isometry of the `n`-dimensional Euclidean space is defined as a distance preserving function.
-/

def IsAffineIsometry (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) : Prop :=
  ∀ (x y : EuclideanSpace ℝ (Fin n)), ‖f x - f y‖ = ‖x - y‖

namespace IsAffineIsometry

variable (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))

/-
Subtracting a constant value from an affine isometry yields an affine isometry.
-/
lemma of_sub_const (hf : IsAffineIsometry f) (a : EuclideanSpace ℝ (Fin n)) :
    IsAffineIsometry (fun x ↦ f x - a) := by
  intro x y
  simp only [sub_sub_sub_cancel_right]
  exact hf x y

section PreservesOrigin

/-
We first restrict to the case of origin preserving affine isometries, i.e. we additionally require `f 0 = 0`.

If an affine isometry preserves the origin, it preserves the norm.
-/

theorem preserves_norm_of_preserves_origin (hf : IsAffineIsometry f) (hforigin : f 0 = 0)
    (x : EuclideanSpace ℝ (Fin n)) : ‖f x‖ = ‖x‖ := by
  calc
    ‖f x‖ = ‖f x - 0‖   := by simp
        _ = ‖f x - f 0‖ := by sorry
        _ = ‖x - 0‖     := by sorry
        _ = ‖x‖         := by sorry

/-
This is a helper lemma, towards `preserves_innerProduct_of_preserves_origin`.
-/

lemma preserves_innerProduct_of_preserves_origin_aux (hf : IsAffineIsometry f) (hforigin : f 0 = 0)
    (x y : EuclideanSpace ℝ (Fin n)) : - 2 * ⟪f x, f y⟫_ℝ = - 2 * ⟪x, y⟫_ℝ := by
  calc
    - 2 * ⟪f x, f y⟫_ℝ = ‖f x - f y‖ ^ 2 - ‖f x‖ ^ 2 - ‖f y‖ ^ 2 := by
                          simp [norm_sub_pow_two_real]; abel
                     _ = ‖f x - f y‖ ^ 2 - ‖x‖ ^ 2 - ‖y‖ ^ 2 := by
                          simp [preserves_norm_of_preserves_origin f hf hforigin]
                     _ = ‖x - y‖ ^ 2 - ‖x‖ ^ 2 - ‖y‖ ^ 2 := by sorry
                     _ = - 2 * ⟪x, y⟫_ℝ := by sorry

/-
If an affine isometry preserves the origin, it preserves the inner product.
-/

theorem preserves_innerProduct_of_preserves_origin (hf : IsAffineIsometry f) (hforigin : f 0 = 0)
    (x y : EuclideanSpace ℝ (Fin n)) :
    ⟪f x, f y⟫_ℝ = ⟪x, y⟫_ℝ :=
  sorry

/-
An origin preserving affine isometry is a linear map.
-/

theorem linear_of_preserves_origin (hf : IsAffineIsometry f) (hforigin : f 0 = 0) :
    IsLinearMap ℝ f where
  map_add := sorry
  map_smul := sorry

/-
We now want to show that any affine isometry preserving the origin is given by an orthogonal matrix. To
check the definition of something in the standard library, go to the docs or use:
-/

#print orthogonalGroup

/-
The defining property of the orthogonal group is the equation `star g * g = 1`. In our situation `star g` is simply `g` transposed.

An origin preserving affine isometry is given by an orthogonal matrix. *Hint:* Use `eq_matrix` from above to get started.
-/

theorem eq_orthogonalMatrix_of_preserves_origin (hf : IsAffineIsometry f) (hforigin : f 0 = 0) :
    ∃ g : orthogonalGroup (Fin n) ℝ, ∀ (x : EuclideanSpace ℝ (Fin n)), f x = g *ᵥ x :=
  sorry

end PreservesOrigin

variable (g : orthogonalGroup (Fin n) ℝ) (x y : EuclideanSpace ℝ (Fin n))

/-
Any affine isometry is of the form `x ↦ g *ᵥ x + y` for some orthogonal matrix `g`.
Hint: Reduce to the `f 0 = 0` case.
-/

theorem eq_orthogonalMatrix_add_const (hf : IsAffineIsometry f) :
    ∃ (g : orthogonalGroup (Fin n) ℝ) (y : EuclideanSpace ℝ (Fin n)),
    ∀ (x : EuclideanSpace ℝ (Fin n)),
    f x = g *ᵥ x + (EuclideanSpace.equiv _ _ y) := by
  let f' : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) := fun x ↦ f x - f 0
  have hf' : IsAffineIsometry f' := sorry
  have hf'zero : f' 0 = 0 := sorry
  obtain ⟨g, hg⟩ := eq_orthogonalMatrix_of_preserves_origin f' hf' hf'zero
  sorry

end IsAffineIsometry
