import Mathlib.Analysis.SpecialFunctions.Pow.Real

example {R : Type} [CommRing R] [IsDomain R] (x y : R) (hx : x ≠ 0) (h : x * y = x) : y = 1 := by
  exact (mul_eq_left₀ hx).mp h

variable {R : Type} [CommRing R]

/-
We put the following definitions in a namespace, to avoid naming clashes with the library.
-/

namespace Algebra'

/-
We say that `x` divides `y` if and only if `y` is a multiple of `x`.
-/

def Divides (x y : R) : Prop :=
  ∃ a, y = a * x

/-
We introduce the notation `x | y` for `Divides x y`.
-/

notation x " | " y => Divides x y

/-
If zero divides `x`, then `x` is zero.
-/

lemma zero_of_zero_divides (x : R) (hx : 0 | x) : x = 0 := by
  obtain ⟨a, ha⟩ := hx
  simpa using ha

lemma everything_divides_zero (x : R) : x | 0 := by
  use 0
  simp
/-
Hint: If you want to know what a specific tactic does, use the `#help tactic` command. For example:
-/


/-
If `x` divides a non-zero element `y`, `x` is non-zero.
-/

lemma ne_zero_of_divides_of_ne_zero (x y : R) (hy : y ≠ 0) (hxy : x | y) : x ≠ 0 := by
  intro hx
  subst hx
  exact hy (zero_of_zero_divides y hxy)

/-
We say that `x` and `y` are associated if and only if `x` and `y` agree up to a unit.
-/

def IsAssociated (x y : R) : Prop :=
  ∃ (a : Rˣ), y = a * x

/-
Every element is associated to itself.
-/

lemma isAssociated_of_eq (x : R) : IsAssociated x x := by
  use 1
  simp

/-
If two elements are associated, they divide each other.
-/

lemma divides_divides_of_isAssociated (x y : R) (h : IsAssociated x y) :
    (x | y) ∧ (y | x) := by
  obtain ⟨a, ha⟩ := h
  constructor
  · use a
  · use a.inv
    rw [ha]
    simp

/-
In a domain, two elements are associated if they divide each other.
-/

lemma isAssociated_of_divides_divides_of_domain [IsDomain R] (x y : R) (hxy : x | y) (hyx : y | x) :
    IsAssociated x y := by
  by_cases hx : x = 0
  · subst hx
    have h1 : y = 0 := zero_of_zero_divides y hxy
    subst h1
    apply isAssociated_of_eq
  · simp at hx
    obtain ⟨a, ha⟩ := hxy
    obtain ⟨b, hb⟩ := hyx
    have hba : b * a = 1 := by
      rw [ha, ← mul_assoc] at hb
      exact (mul_eq_right₀ hx).mp (id (Eq.symm hb))
    have hab : a * b = 1 := by
      rw [mul_comm a b]
      exact hba
    let a' : Rˣ := {
      val := a,
      inv := b,
      val_inv := hab,
      inv_val := hba
    }
    use a'


lemma isAssociated_is_symmetric (x y: R) (h : IsAssociated x y) : IsAssociated y x := by
  obtain ⟨a, rfl⟩ := h
  use a⁻¹
  exact (Units.eq_inv_mul_iff_mul_eq a).mpr rfl

/-
In a domain, two elements are associated if and only if they divide each other.
-/

lemma isAssociated_iff_divides_divides_of_domain [IsDomain R] (x y : R) :
    IsAssociated x y ↔ (x | y) ∧ (y | x) := by
  constructor
  · exact divides_divides_of_isAssociated x y
  · intro ⟨hxy, hyx⟩
    exact isAssociated_of_divides_divides_of_domain x y hxy hyx

/-
We say an element `x : R` is non-trivial, if it is neither zero nor a unit.
-/

def IsNontrivial (x : R) : Prop := x ≠ 0 ∧ ¬ (IsUnit x)

/-
An irreducible element `x : R` is a non-trivial element such that whenever `x = a * b`, either `a` is a unit or `b` is a unit.
-/

def IsIrreducible (x : R) : Prop :=
  IsNontrivial x ∧ ∀ a b, x = a * b → IsUnit a ∨ IsUnit b


/-
An element `x` of a ring is prime, if it is non-trivial and whenever `x` divides a product, it divides one of the factors.
-/

def IsPrime (x : R) : Prop :=
  IsNontrivial x ∧ ∀ a b, (x | a * b) → (x | a) ∨ (x | b)

/-
In an integral domain, every prime element is irreducible.
-/

lemma ca_equals_ba [IsDomain R] {a b c: R} (h: a = b) : c*a = c*b := by
  apply mul_eq_mul_left_iff.mpr
  apply Or.inl
  exact h

lemma ac_equals_bc [IsDomain R] {a b c: R} (h: a = b) : a*c = b*c := by
  apply mul_eq_mul_right_iff.mpr
  apply Or.inl
  exact h
/-
lemma non_trivial_prod_is_non_trivial [IsDomain R] (a b: R) (hnontr_a: IsNontrivial a) (hnontr_b: IsNontrivial b): IsNontrivial (a * b) := by
  obtain ⟨ hnonzero_a, hunit_a⟩ := hnontr_a
  obtain ⟨ hnonzero_b, hunit_b⟩ := hnontr_b
 -/


lemma  is_unit_of_mul_eq_one [IsDomain R] {a b x: R} (h_mul : x = a * b) (hnontrivial: IsNontrivial x) (hxa: Divides x a) : IsUnit b := by
  obtain ⟨c, hxa⟩ := hxa -- a = c * x
  rw [hxa, mul_comm, ←mul_assoc] at h_mul -- rewrite to x = a * b = b * a = b * c * x
  have hbc1 : b * c = 1 := by -- proof that b * c = 1
        apply (mul_eq_right₀ hnontrivial.left).mp
        rw[←h_mul]
  exact isUnit_of_mul_eq_one b c hbc1

theorem isIrreducible_of_isPrime [IsDomain R] (x : R) (h : IsPrime x) : IsIrreducible x := by
  obtain ⟨hnontrivial, hdiv⟩ := h
  constructor
  · exact hnontrivial
  · intros a b h_mul
    have hx_divides_ab : x | a*b := by
      use 1
      rw[h_mul]
      simp
    have hxa_or_xb := hdiv a b hx_divides_ab
    -- x divides either a or b because it's prime
    rcases hxa_or_xb with hxa | hxb
    · exact Or.inr (is_unit_of_mul_eq_one h_mul hnontrivial hxa)
    · have h_mul1 : x = b * a := by
        rw[mul_comm]
        exact h_mul
      exact Or.inl (is_unit_of_mul_eq_one h_mul1 hnontrivial hxb)







/-
Now define factorial rings (also called unique factorization domains) and show that in any factorial ring,
also the converse of `isIrreducible_of_isPrime` holds, i.e. every irreducible element is prime.
-/
noncomputable instance (D: Type) [CommRing D] : Inhabited D := by
  exact Classical.inhabited_of_nonempty'



def IsFactorialRing (D: Type) [CommRing D] [IsDomain D]: Prop := -- Ring has a 0 by default, Inhabited R only done for Lean to stop complaining
  -- It's based on a ring R
  -- And every non-zero and non-unit element is factorable into irreducibles
  (∀ (x : D), x ≠ 0 → ¬IsUnit x → ∃ (factors :List D), ((∀ y ∈ factors, IsIrreducible y) ∧ x=List.prod factors)) ∧
  -- And such factorisation is unique up to associates and permutation:
  (
  ∀ (x : D) (factors1 factors2 : List D), -- there exist 2 lists
  x ≠ 0 → (¬IsUnit x) → -- for any x in R that is non-zero and non-unit
  (x = List.prod factors1) → (x = List.prod factors2) → -- such that x is the product of the factors in each list
  (∀ y ∈ factors1, IsIrreducible y) → (∀ y ∈ factors2, IsIrreducible y) → -- and those lists are made up of irreducibles
  ((factors1.length=factors2.length) ∧ -- then they are of equal length
  ∃ σ ∈ factors1.permutations, -- and there exists a permutation of one of them, here called sigma
  (∀ i : Fin σ.length,  (IsAssociated (σ.get i) (factors2.get! i )))) -- such that sigma_i is associated to factors2_i
  )


variable {D : Type} [CommRing D] [IsDomain D]

theorem isPrime_of_isIrreducible (p : D) (h : IsIrreducible p) (hUFD: IsFactorialRing D): IsPrime p := by
  obtain ⟨hnontrivial, hirr⟩ := h
  constructor
  · exact hnontrivial
  -- Step 2: a and b non-unit, non-zero
  · intros a b hdiv

    by_cases ha : a = 0
    · left
      rw [ha]
      exact everything_divides_zero p


    by_cases hb : b = 0
    · right
      rw [hb]
      exact everything_divides_zero p
    obtain ⟨ c, hdiv ⟩ := hdiv -- pc= a * b


    by_cases hunit_a : IsUnit a
    · right
      obtain ⟨u, hu⟩ := hunit_a
      have hmul :   b = ↑u⁻¹ * (c * p) := by
        subst hu
        refine (Units.eq_inv_mul_iff_mul_eq u).mpr ?_ -- rewrite goal
        exact hdiv
      simp[<-mul_assoc] at hmul
      use c * ↑u⁻¹
      subst hmul
      ring


    by_cases hunit_b : IsUnit b
    · left
      obtain ⟨u, hu⟩ := hunit_b
      rw[mul_comm] at hdiv
      have hmul : a = u⁻¹ * (c * p) := by
        subst hu
        exact (Units.eq_inv_mul_iff_mul_eq u).mpr hdiv
      rw[<-mul_assoc, mul_comm] at hmul
      use (u⁻¹ * c)
      subst hmul
      ring
    -- Step 3.1: c is non-zer0


    by_cases hzero_c : c = 0
    · subst hzero_c
      simp at hdiv
      rcases hdiv with ⟨u, hu⟩
      · contradiction
      · contradiction


    -- Step 3.2: c is non-unit
    by_cases hunit_c : IsUnit c -- first use c⁻¹ to get p = ...
    obtain ⟨u, hu⟩ := hunit_c
    have hdiv' : u⁻¹ * (a * b) = u⁻¹ * (c * p) := by
      subst hu
      exact ca_equals_ba hdiv
    subst hu
    rw[<-mul_assoc, <-mul_assoc] at hdiv'
    simp at hdiv'
    rw[mul_comm ↑u⁻¹ a, mul_assoc] at hdiv'
    have hdiv': p = a * (↑u⁻¹*b) := by subst hdiv'; rfl
    have hunits: IsUnit a ∨ IsUnit (↑u⁻¹*b)  := by
      apply hirr a (↑u⁻¹*b) hdiv'
    -- now either a is a unit or u⁻¹*b is a unit
    rcases hunits with hunit_a | hunit_ub
    · contradiction

    · have hunit_b: IsUnit b := by -- if u⁻¹*b is a unit, then b is a unit
        obtain ⟨v, hv⟩ := hunit_ub
        have huv: u * v = b := by
          exact (Units.eq_inv_mul_iff_mul_eq u).mp hv
        have hunit_v: IsUnit v.val := by
          use v
        have hunit_u: IsUnit u.val := by
          use u
        have hunit_uv: IsUnit (u * v.val) := by
          exact IsUnit.mul hunit_u hunit_v
        rw[<-huv]
        exact hunit_uv
      contradiction


    -- Step 4: Because we're in a UFD,factor a*b and p*c into irreducibles,
    -- and show that the factorisations are the same
    obtain ⟨ hfactorisable, hunique ⟩ := hUFD
    obtain ⟨factors_a, hfactor_a_irreducible, hprodfactors_a⟩ := hfactorisable a ha hunit_a
    obtain ⟨factors_b, hfactor_b_irreducible, hprodfactors_b⟩ := hfactorisable b hb hunit_b
    obtain ⟨factors_c, hfactor_c_irreducible, hprodfactors_c⟩ := hfactorisable c hzero_c hunit_c
    -- we factorised a, b, c into irreducibles
    have habneq0 : a*b ≠ 0 := by simp[ha, hb]
    have habnotunit: ¬ IsUnit (a*b) := by
        intro hunit -- proof by contradiction
        have hunit_b': IsUnit b := by -- more precisely, we show that b is a unit
          obtain ⟨u, hu⟩ := hunit -- u * 1 = a * b
          have humul' : b * (u⁻¹ * a) = 1  := by -- rewrite it
            have hu': u * 1 = (a * b) := by simp[hu]
            have humul : 1 = u⁻¹ * (a * b) := by
              apply (Units.eq_inv_mul_iff_mul_eq u).mpr hu'
            simp[humul]
            ring
          -- and use theorem that if b * x = 1, then b is a unit
          exact isUnit_of_mul_eq_one b (u⁻¹ * a) humul'
        contradiction
    -- here we factors non-trivial a*b in 2 different ways:
    -- a*b = prod (a_i) * prod (b_i)
    let factors_ab := factors_a ++ factors_b
    have hfactor_ab_irreducible : ∀ y ∈ factors_ab, IsIrreducible y := by
      intros y hy
      simp[factors_ab] at hy
      rcases hy with hya | hyb
      · exact hfactor_a_irreducible y hya
      · exact hfactor_b_irreducible y hyb
    have hprodfactors_ab : a*b = List.prod factors_ab := by
      simp[factors_ab, hprodfactors_a, hprodfactors_b]
    -- a * b = c * p=prod (c_i) * p
    let factors_pc := [p] ++ factors_c  -- note that p is irreducible itself, so every element in [p] is irreducible
    have hprodfactors_pc : a*b = List.prod factors_pc := by
      simp[factors_pc, hprodfactors_c, hdiv]
      ring
    have hfactor_pc_irreducible : ∀ y ∈ factors_pc, IsIrreducible y := by
      intros y hy
      simp[factors_pc] at hy
      rcases hy with rfl | hy
      · exact ⟨hnontrivial, hirr⟩ -- we split IsIrreducible p into those 2 before
      · exact hfactor_c_irreducible y hy
    -- now we use the uniqueness of factorisation in UFD
    -- namely, the 2 factorisations of a*b must be associate up to reordering:
    -- they are the same length:
    obtain hlength := (hunique (a*b) factors_ab factors_pc habneq0 habnotunit hprodfactors_ab hprodfactors_pc hfactor_ab_irreducible hfactor_pc_irreducible).1
    -- (trust is we just wrote up every part of the definition of this property)
    -- and there exists a permutation of factors_pc that makes it associate to factors_ab:
    obtain ⟨σ, hσ, hσassoc⟩ := (hunique (a*b) factors_ab factors_pc habneq0 habnotunit hprodfactors_ab hprodfactors_pc hfactor_ab_irreducible hfactor_pc_irreducible).2
    -- we now show that p is associate to one of the factors in factors_ab
    -- have hσlen : factors_pc.length = factors_ab.length := by
    --   rw [hlength]
    -- we need to show that p is associated to one of the factors in factors_ab
    -- but since in the definition we have only indexes of elements, we need to find the index of p in factors_pc
    have hpassociatedwithab_i: (∃ i : Fin σ.length, IsAssociated p (σ.get i) ) := by
      -- because in the definition we have only indexes of elements, we need to find the index of p in factors_pc
      have hphasnumberj : ∃ j : Fin σ.length, p = factors_pc.get! j := by
        -- we actually know the index is 0
        have hpfactor : p = factors_pc.get! 0 := by
          simp[factors_pc]
        -- but we need to prove σ.length>0 to be able to translate 0 from ℕ to Fin σ.length
        have hσlengthgr0 : σ.length > 0 := by
          -- so we prove that factors_pc.length > 0
          have hpclengthgr0 : factors_pc.length > 0 := by
            have hfactors_pc_isnotnull : ¬factors_pc = [] := by
              intro hf
              simp[factors_pc] at hf -- by using a lemma that says that non-empty list has length > 0
            exact (List.length_pos_iff_ne_nil.mpr hfactors_pc_isnotnull)
           -- now we use the fact,  hlength says that f_pc.length=f_ab.length, obviously = σ.length, as a permutation of factors_ab
          have hequallength : σ.length = factors_pc.length  := by
            rw[<-hlength]
            apply List.Perm.length_eq
            exact List.mem_permutations.mp hσ
          rw[hequallength]
          exact hpclengthgr0

         -- now that σ.length>0, we can just translate 0 to Fin σ.length,
        use @Fin.ofNat' σ.length 0 hσlengthgr0
        exact hpfactor -- and substitute 0
      -- now we know p's index, and we can simply substitute it into hσassoc
      obtain ⟨j, hfactorspc_j_equals_p⟩ := hphasnumberj
      use j
      rw[hfactorspc_j_equals_p]
      exact isAssociated_is_symmetric (σ.get j) (factors_pc.get! ↑j) (hσassoc j)
    have hσ_perm_of_ab: σ.Perm factors_ab := by
      exact List.mem_permutations.mp hσ
    have a_in_σ_a_in_ab: ∀ a ∈ σ, a∈ factors_ab := by
      intros a ha
      exact (List.Perm.mem_iff hσ_perm_of_ab).mp ha
    -- we know p is associated to one of elements of σ
    -- which means p is associated to one of factors in factors_a or factors_b
    have hp_assoc_a_or_b:
      (∃ a ∈ factors_a, IsAssociated a p) ∨
      (∃ b ∈ factors_b, IsAssociated b p) := by
      -- we need to prove that p is associated to one of the elements in factors_ab first
      obtain ⟨i, hpi⟩ := hpassociatedwithab_i

      -- σ.get i is also in factors_ab:
      have hσiinσ : σ.get i ∈ σ := by
        refine List.mem_iff_get.mpr ?_
        use i

        -- refine List.mem_append.mp ?_ -- this one: a ∈ s ++ t ↔ a ∈ s ∨ a ∈ t
      have hσiinab' : σ.get i ∈ factors_ab := by
        exact a_in_σ_a_in_ab (σ.get i) (hσiinσ)
        --refine List.mem_of_elem_eq_true ?_
        -- exact List.get_mem σ i
      -- and p is associated to σ.get i

      have hp_associated_to_ab : ∃ a ∈ factors_ab, IsAssociated p a := by
        use σ.get i
      have hσ_i_in_a_or_b: (σ.get i) ∈ factors_a ∨ (σ.get i) ∈ factors_b := by
        exact (List.mem_append.mp hσiinab')
      -- we know that σ get i is in factors_a or factors_b
      -- and naturally we split into 2 cases:
      rcases hσ_i_in_a_or_b with hσ_i_in_a | hσ_i_in_b
      · left
        use (σ.get i)
        constructor
        · exact hσ_i_in_a
        · exact (isAssociated_is_symmetric p (σ.get i) hpi)
      · right
        use (σ.get i)
        constructor
        · exact hσ_i_in_b
        · exact (isAssociated_is_symmetric p (σ.get i) hpi)

    -- Step 5: p is associated to a or b
    rcases hp_assoc_a_or_b with hpa | hpb
    · left
      obtain ⟨a_i, ha_i, hp_assoc_a_i⟩ := hpa
      obtain ⟨u, hu⟩ := (isAssociated_is_symmetric a_i p hp_assoc_a_i)

      -- we can use fucking factors_a \ {a_i} ? hard




















end Algebra'

-- this has been at the beginning of step 4, may be we shall need it
/-
  have habneq0 : a*b ≠ 0 := by simp[ha, hb]
  have hpcneq0 : p*c ≠ 0 := by simp[hzero_c, hnontrivial.left]
  have abnotunit: ¬ IsUnit (a*b) := by -- why the fuck did I need it?
      intro hunit
      obtain ⟨u, hu⟩ := hunit
      have hu': u * 1 = (a * b) := by simp[hu]
      have humul : 1 = u⁻¹ * (a * b) := by
        apply (Units.eq_inv_mul_iff_mul_eq u).mpr hu'
      have humul' : b * (u⁻¹ * a) = 1  := by
        simp[humul]
        ring
      have hunit_b': IsUnit b := by
        exact isUnit_of_mul_eq_one b (u⁻¹ * a) humul'
      contradiction  -/
