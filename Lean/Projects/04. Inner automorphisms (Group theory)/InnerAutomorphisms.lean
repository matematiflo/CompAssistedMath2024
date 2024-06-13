/-
# Inner automorphisms

By Judith Ludwig, Christian Merten and Florent Schaffhauser,
Proseminar on computer-assisted mathematics,
Heidelberg, Summer Semester 2024

In this project sketch we define the group of inner automorphisms of a group and
show that the group `GL (Fin n) ℝ` has an automorphism that is not inner.
-/

import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.Data.Complex.Basic

section

variable {G : Type} [Group G]

/-
A group homomorphism is a `MonoidHom` and is denoted by `→+` and a group isomorphism
is a `MulEquiv` and is denoted by `≃*`.

A `MulEquiv` is defined as a `structure`. To see the fields of `MulEquiv`, you can use `#print`:
-/

#print MulEquiv

/-
Note that in this case, `MulEquiv` has two fields: `toEquiv` and `map_mul'`. Since `toEquiv` is an
`Equiv`, it is again a structure, whose fields you can check with
-/

#print Equiv

/-
Note that this also unfolds the `toEquiv` field.

To define a term of a type defined by `structure`, use the `def foo : bar where` syntax.
-/

/-
Every element `g : G` defines an automorphism of `G` by conjugation.
-/

def conjugate (g : G) : G ≃* G where
  toFun x := g * x * g⁻¹
  invFun x := g⁻¹ * x * g
  left_inv x := by group
  right_inv x := by group
  map_mul' x y := by group

/-
For more details on structures, see
https://lean-lang.org/theorem_proving_in_lean4/structures_and_records.html
-/

@[simp]
lemma conjugate_apply (g x : G) : conjugate g x = g * x * g⁻¹ :=
  rfl

/-
`conjugate` commutes with multiplication.
-/

lemma conjugate_mul (a b : G) : conjugate (a * b) = conjugate a * conjugate b := by
  ext x
  sorry

variable (G)

/-
`conjugate` as a group homomorphism.
-/

@[simps!]
def conjugateHom : G →* (G ≃* G) :=
  MonoidHom.mk' conjugate sorry

/-
As an example we show that the kernel of the conjugation is the center of the group.
-/

theorem conjugateHom_ker : (conjugateHom G).ker = Subgroup.center G := by
  ext x
  constructor
  · intro h
    rw [Subgroup.mem_center_iff]
    intro y
    have : y = x * y * x⁻¹ := by
      rw [← conjugateHom_apply_apply, h]
      simp
    /- `rw` at first occurence -/
    nth_rw 1 [this]
    /- finish of with `group` -/
    group
  · intro h
    rw [Subgroup.mem_center_iff] at h
    ext y
    /- found with `simp?` -/
    simp only [conjugateHom_apply_apply, MulAut.one_apply]
    rw [← h]
    group

/-
The group of inner automorphisms of `G` is the subgroup of automorphisms, which are given by conjugation with an element of `G`.
-/

def InnerAut : Subgroup (G ≃* G) where
  carrier := { σ : G ≃* G | ∃ (g : G), conjugate g = σ }
  mul_mem' := sorry
  one_mem' := sorry
  inv_mem' := sorry

end

/-
If `φ` is an inner automorphism of `GL (Fin n) ℝ` and `A : GL (Fin n) ℝ`, the characteristic polynomials of `A` and `φ A` agree.
-/

theorem charpoly_eq_of_inner (A : GL (Fin n) ℝ) (φ : InnerAut (GL (Fin n) ℝ)) :
    Matrix.charpoly A.val = Matrix.charpoly (φ.val A).val :=
  sorry

/-
The transpose of an element of `GL (Fin n) ℝ`.

*Hint:* Alternatively you can use `Matrix.GeneralLinearGroup.mkOfDetNeZero`.
-/

def Matrix.GeneralLinearGroup.transpose (A : GL (Fin n) ℝ) : GL (Fin n) ℝ where
  val := A.val.transpose
  inv := A.inv.transpose
  val_inv := sorry
  inv_val := sorry

/-
The automorphism of `GL (Fin n) ℝ` sending `A` to the transpose of `A⁻¹`.
-/

def transposeInv : GL (Fin n) ℝ ≃* GL (Fin n) ℝ where
  toFun g := g⁻¹.transpose
  invFun g := g⁻¹.transpose
  left_inv := sorry
  right_inv := sorry
  map_mul' := sorry

/-
State and prove that `transposeInv` is not an inner-automorphism of `GL (Fin n) ℝ`.

*Hint:* For the proof use `charpoly_eq_of_inner`.
-/
