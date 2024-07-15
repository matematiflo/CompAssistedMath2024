import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Group.Aut
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic

variable {G : Type} [Group G]

-- We will now define the conjugation map h ↦ ghg⁻¹;
-- We provide the proofs that this map is indeed an automorphism
-- at the same time, because automorphisms form a "structure"
-- in Lean 4 with multiple components.

def conjugation (g : G) : G ≃* G where

  -- The actual map itself.
  toFun (h : G) := g * h * g⁻¹

  -- The inverse map.
  invFun (h : G) := g⁻¹ * h * g

  -- Proof that the inverse map is a left inverse.
  left_inv (h : G) := show g⁻¹ * (g * h * g⁻¹) * g = h by
    group

  -- Proof that the inverse map is a right inverse.
  right_inv (h : G) := show g * (g⁻¹ * h * g) * g⁻¹ = h by
    group

  -- Proof that the map is indeed a group homomorphism.
  map_mul' (h₁ h₂ : G) := show g * (h₁ * h₂) * g⁻¹ = (g * h₁ * g⁻¹) * (g * h₂ * g⁻¹) by
    group

@[simp] lemma conjugation_apply (g h : G) : conjugation g h = g * h * g⁻¹ := rfl

-- Now we can define our map c;
-- As with automorphims, group homomorphims are also defined
-- as structures. Note that while the proof, that c maps the
-- neutral element to the neutral element, is actually not needed
-- (as this always holds for group homomorphims), we give it
-- nonetheless, because Lean 4 defines them under the hood as
-- monoid homomorphims.

def c : G →* (G ≃* G) where

  -- The actual map itself.
  toFun (g : G) := conjugation g

  -- Proof that c maps the neutral element to the neutral element.
  map_one' := show conjugation 1 = 1 by
    ext h
    simp

  -- Proof that c is a group homomorphism.
  map_mul' (g₁ g₂ : G) := show conjugation (g₁ * g₂) = conjugation g₁ * conjugation g₂ by
    ext h
    simp
    group

@[simp] lemma c_apply (g : G) : c g = conjugation g := rfl

-- Now we cam define Inn(G) as the subgroup defined by the image
-- of c. We make use of the fact the image of a group homomorphism
-- always forms a subgroup.

def Inn (G : Type) [Group G] : Subgroup (G ≃* G) := c.range

-- Now we show that the diagonal matrix with only 2 on the diagonal
-- is an element of GLₙ(ℝ), i.e. it has an inverse matrix, namely the
-- matrix with only 1/2 in the diagonal.

noncomputable def diag_mat_with_two (n : ℕ) : GL (Fin n) ℝ where

  -- The matrix itself
  val := Matrix.scalar (Fin n) 2

  -- The inverse matrix
  inv := Matrix.scalar (Fin n) 2⁻¹

  -- Proof the proposed inverse is a right inverse.
  val_inv := by
    dsimp
    simp

  -- Proof the proposed inverse is a left inverse.
  inv_val := by
    dsimp
    simp

@[simp] lemma diag_mat_with_two_apply (n : ℕ) : diag_mat_with_two n = Matrix.scalar (Fin n) (2 : ℝ) := rfl
@[simp] lemma diag_mat_with_two_inverse_apply (n : ℕ) : (diag_mat_with_two n)⁻¹ = Matrix.scalar (Fin n) (2⁻¹ : ℝ) := rfl

-- We show that if A ∈ GLₙ(ℝ), we also have Aᵗ ∈ GLₙ(ℝ).

def Matrix.GeneralLinearGroup.transpose (A : GL (Fin n) ℝ) : GL (Fin n) ℝ where

  -- Definition of Aᵗ
  val := A.val.transpose

  -- Definition of (Aᵗ)⁻¹ (= (A⁻¹)ᵗ)
  inv := A.inv.transpose

  -- Proof that Aᵗ * (A⁻¹)ᵗ = 1ₙ
  val_inv := show A.val.transpose * A.inv.transpose = 1 by
    rw [← Matrix.transpose_mul]
    dsimp
    rw_mod_cast [mul_left_inv]
    rw_mod_cast [Matrix.transpose_one]

  -- Proof that (A⁻¹)ᵗ * Aᵗ = 1ₙ
  inv_val := show A.inv.transpose * A.val.transpose = 1 by
    rw [← Matrix.transpose_mul]
    dsimp
    rw_mod_cast [mul_right_inv]
    rw_mod_cast [Matrix.transpose_one]

@[simp] lemma transpose_apply (A : GL (Fin n) ℝ) : A.transpose = A.val.transpose := rfl
@[simp] lemma transpose_inverse_apply (A : GL (Fin n) ℝ) : (A.transpose)⁻¹ = A.inv.transpose := rfl

-- We will now define and prove that the map α: GLₙ(ℝ) → GLₙ(ℝ), A ↦ (A⁻¹)ᵗ
-- is a group automorphism, as wished.

def α : GL (Fin n) ℝ ≃* GL (Fin n) ℝ where

  -- The actual map itself.
  toFun (A : GL (Fin n) ℝ) := A⁻¹.transpose

  -- The inverse map. (Same map as above.)
  invFun (A : GL (Fin n) ℝ) := A⁻¹.transpose

  -- Proof that the inverse map is a left inverse.
  left_inv (A : GL (Fin n) ℝ) := by norm_cast

  -- Proof that the inverse map is a right inverse. (Same proof as above.)
  right_inv (A : GL (Fin n) ℝ) := by norm_cast

  -- Proof that the map is indeed a group homomorphism.
  map_mul' (A₁ A₂ : GL (Fin n) ℝ) := by
    dsimp [Matrix.GeneralLinearGroup.transpose]
    simp
    norm_cast

@[simp] lemma α_apply (A : GL (Fin n) ℝ) : α A = A⁻¹.transpose := rfl
lemma simplify_inv (A : GL (Fin n) ℝ) : (A.val)⁻¹ = A.inv := by norm_cast

-- To help us prove our statement, we will first prove that inner auto-
-- morphisms preserve characteristic polynomials.

open Matrix.GeneralLinearGroup in
theorem inn_preserve_charpoly (ϕ : GL (Fin n) ℝ ≃* GL (Fin n) ℝ) (A : GL (Fin n) ℝ) :
ϕ ∈ Inn (GL (Fin n) ℝ) → (A.val).charpoly = ((ϕ A).val).charpoly := by
  intro ⟨B, image_of_B⟩ -- Initial assumption.
  rw [← image_of_B]
  simp
  rw [simplify_inv]
  -- Standard basis for endomorphism general linear group:
  let b : Basis (Fin n) ℝ (Fin n → ℝ) := Pi.basisFun ℝ (Fin n)
  -- eB is B equal to B, but interpreted as a group automorphism:
  let eB : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ) := (toLinear B).toLinearEquiv
  have h₁ : eB = (Matrix.toLin b b) B.val := rfl
  have h₂ : eB.symm = (Matrix.toLin b b) B.inv := rfl
  -- Rewrite matrices as automorphisms
  rw [← LinearMap.toMatrix_toLin b b A]
  rw [← LinearMap.toMatrix_toLin b b B]
  rw [← LinearMap.toMatrix_toLin b b B.inv]
  repeat rw [← LinearMap.toMatrix_comp]
  repeat rw [LinearMap.charpoly_toMatrix]
  -- We use the fact that this proof was already done for the endomorphism general linear group.
  rw [← h₁, ← h₂, ← LinearEquiv.conj_apply, eB.charpoly_conj]

-- This lemma will help us show that two polynomials are not equal.

lemma inn_preserve_charpoly_all_elements (ϕ : GL (Fin n) ℝ ≃* GL (Fin n) ℝ) (A : GL (Fin n) ℝ) :
ϕ ∈ Inn (GL (Fin n) ℝ) → ∀x : ℝ, Polynomial.eval x (A.val).charpoly = Polynomial.eval x ((ϕ A).val).charpoly := by
  intro hyp x
  rw [inn_preserve_charpoly]
  exact hyp

-- We will now show that α does not preserve the characteristic polynomial of
-- the diagoal matrix with 2 on the diagonal.

-- 0ⁿ = 0, if we interpret 0 as the real number.

lemma zero_pow_nat (n : ℕ) (not_zero : n ≠ 0) : (0 : ℝ) ^ n = (0 : ℝ) := by
  simp
  exact not_zero

-- We evaluate our counterexample at 2.

lemma eval_at_two (not_zero : n ≠ 0) : Polynomial.eval 2 ((diag_mat_with_two n).val).charpoly ≠ Polynomial.eval 2 ((α (diag_mat_with_two n)).val).charpoly := by
  simp [-map_ofNat, -Matrix.coe_units_inv]
  dsimp [Matrix.charpoly, Matrix.charmatrix]
  simp
  ring_nf
  intro hyp
  symm at hyp
  rw [zero_pow_nat n not_zero] at hyp
  have t : 3 / 2 ≠ (0 : ℝ) := by simp
  exact pow_ne_zero n t hyp

-- As such, we can show that α does not preserve the characteristic polynomial of our matrix.

theorem α_not_preserving (not_zero : n ≠ 0) : ∃x : ℝ, Polynomial.eval x ((diag_mat_with_two n).val).charpoly ≠ Polynomial.eval x ((α (diag_mat_with_two n)).val).charpoly := by
  use 2
  exact eval_at_two not_zero

-- Now we are finally ready to show α is not an inner automorphism.

theorem α_not_in_inn (not_zero : n ≠ 0) : α ∉ Inn (GL (Fin n) ℝ) := by
  dsimp [Not]
  intro α_in_Inn
  apply inn_preserve_charpoly_all_elements α (diag_mat_with_two n) at α_in_Inn
  have hyp : ∃x : ℝ, Polynomial.eval x ((diag_mat_with_two n).val).charpoly ≠ Polynomial.eval x ((α (diag_mat_with_two n)).val).charpoly := α_not_preserving not_zero
  rw [← not_forall] at hyp
  exact hyp α_in_Inn
