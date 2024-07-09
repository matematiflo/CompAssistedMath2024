import Mathlib.Analysis.SpecialFunctions.Pow.Real

-- Example usage of a lemma about commutative rings and domains
example {R : Type} [CommRing R] [IsDomain R] (x y : R) (hx : x ≠ 0) (h : x * y = x) : y = 1 := by
  exact (mul_eq_left₀ hx).mp h

-- Define the type R and require it to be a commutative ring
variable {R : Type} [CommRing R]

/-
We put the following definitions in a namespace, to avoid naming clashes with the library.
-/
namespace Algebra'

/- Definitions -/

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
We say that `x` and `y` are associated if and only if `x` and `y` agree up to a unit.
-/
def IsAssociated (x y : R) : Prop :=
  ∃ (a : Rˣ), y = a * x

/-
An element `x : R` is non-trivial if it is neither zero nor a unit.
-/
def IsNontrivial (x : R) : Prop := x ≠ 0 ∧ ¬IsUnit x

/-
An irreducible element `x : R` is a non-trivial element such that whenever `x = a * b`, either `a` is a unit or `b` is a unit.
-/
def IsIrreducible (x : R) : Prop :=
  IsNontrivial x ∧ ∀ a b, x = a * b → IsUnit a ∨ IsUnit b

/-
An element `x` of a ring is prime if it is non-trivial and whenever `x` divides a product, it divides one of the factors.
-/
def IsPrime (x : R) : Prop :=
  IsNontrivial x ∧ ∀ a b, (x | a * b) → (x | a) ∨ (x | b)

/-
Define factorial rings (also called unique factorization domains).
-/
def IsFactorialRing (R : Type) [CommRing R] [IsDomain R] [Inhabited R] : Prop :=
  -- First part: Every non-zero and non-unit element is factorizable into irreducibles.
  (∀ (x : R), x ≠ 0 → ¬IsUnit x →
    -- For every non-zero, non-unit element x, there exists a list of elements (factors)
    ∃ (factors : List R),
      -- All elements in the factors list are irreducible
      (∀ y ∈ factors, IsIrreducible y) ∧
      -- The product of all elements in the factors list equals x
      x = List.prod factors) ∧
  -- Second part: Such factorization is unique up to associates and permutation.
  (∀ (x : R) (factors1 factors2 : List R),
    -- For every non-zero, non-unit element x
    x ≠ 0 → ¬IsUnit x →
    -- If x can be written as the product of factors1
    x = List.prod factors1 →
    -- and also as the product of factors2
    x = List.prod factors2 →
    -- and all elements in factors1 are irreducible
    (∀ y ∈ factors1, IsIrreducible y) →
    -- and all elements in factors2 are irreducible
    (∀ y ∈ factors2, IsIrreducible y) →
    -- Then, the lengths of the two factor lists are the same
    (factors1.length = factors2.length ∧
    -- and there exists a permutation σ of factors1 such that
    ∃ σ ∈ factors1.permutations,
      -- each element in σ is associated with the corresponding element in factors2
      (∀ i : Fin σ.length, IsAssociated (σ.get i) (factors2.get! i))))



/- Lemmas -/

/-
If zero divides `x`, then `x` is zero.
-/
lemma zero_of_zero_divides (x : R) (hx : 0 | x) : x = 0 := by
  obtain ⟨a, ha⟩ := hx
  simpa using ha

/-
Everything divides zero.
-/
lemma everything_divides_zero (x : R) : x | 0 := by
  use 0
  simp

/-
If `x` divides a non-zero element `y`, `x` is non-zero.
-/
lemma ne_zero_of_divides_of_ne_zero (x y : R) (hy : y ≠ 0) (hxy : x | y) : x ≠ 0 := by
  intro hx
  subst hx
  exact hy (zero_of_zero_divides y hxy)

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
  -- Obtain a unit 'a' such that y = a * x from the association h
  obtain ⟨a, ha⟩ := h
  -- Split the goal into two parts: (x | y) and (y | x)
  constructor
  -- Proof that x divides y
  · use a  -- y = a * x implies x | y
  -- Proof that y divides x
  · use a.inv  -- Since a is a unit, a.inv is its inverse
    -- Substitute y = a * x into the goal and simplify
    rw [ha]
    simp  -- Simplifies using the properties of units and their inverses


/-
In a domain, two elements are associated if they divide each other.
-/
lemma isAssociated_of_divides_divides_of_domain [IsDomain R] (x y : R) (hxy : x | y) (hyx : y | x) :
    IsAssociated x y := by
  -- Case analysis on whether x is zero
  by_cases hx : x = 0
  -- Case when x is zero
  · subst hx
    -- If x divides y and x is zero, then y must be zero
    have h1 : y = 0 := zero_of_zero_divides y hxy
    -- Substitute y with zero
    subst h1
    -- Zero is associated with zero
    apply isAssociated_of_eq
  -- Case when x is not zero
  · simp at hx
    -- Obtain the existence of an element a such that y = a * x
    obtain ⟨a, ha⟩ := hxy
    -- Obtain the existence of an element b such that x = b * y
    obtain ⟨b, hb⟩ := hyx
    -- Prove that b * a = 1
    have hba : b * a = 1 := by
      rw [ha, ← mul_assoc] at hb  -- Rewrite using the fact y = a * x
      exact (mul_eq_right₀ hx).mp (id (Eq.symm hb))  -- Use the non-zero property of x and associativity
    -- Prove that a * b = 1 by commutativity
    have hab : a * b = 1 := by
      rw [mul_comm a b]  -- Rewrite using commutativity of multiplication
      exact hba
    -- Define a unit a' with value a and inverse b
    let a' : Rˣ := {
      val := a,
      inv := b,
      val_inv := hab,  -- a * b = 1
      inv_val := hba   -- b * a = 1
    }
    -- x and y are associated via the unit a'
    use a'

/-
In a domain, two elements are associated if and only if they divide each other.
-/
lemma isAssociated_iff_divides_divides_of_domain [IsDomain R] (x y : R) :
    IsAssociated x y ↔ (x | y) ∧ (y | x) := by
  -- Split the proof into two directions:
  constructor
  -- First direction: If x is associated with y, then x divides y and y divides x
  · exact divides_divides_of_isAssociated x y
  -- Second direction: If x divides y and y divides x, then x is associated with y
  · intro ⟨hxy, hyx⟩
    exact isAssociated_of_divides_divides_of_domain x y hxy hyx


/-
Helper lemmas for proving properties of units.
-/
lemma ca_equals_ba [IsDomain R] {a b c : R} (h : a = b) : c * a = c * b := by
  apply mul_eq_mul_left_iff.mpr
  apply Or.inl
  exact h

lemma ac_equals_bc [IsDomain R] {a b c : R} (h : a = b) : a * c = b * c := by
  apply mul_eq_mul_right_iff.mpr
  apply Or.inl
  exact h

lemma is_unit_of_mul_eq_one [IsDomain R] {a b x : R} (h_mul : x = a * b)
    (hnontrivial : IsNontrivial x) (hxa : Divides x a) : IsUnit b := by
  -- Obtain an element c such that a = c * x from the divisibility condition
  obtain ⟨c, hxa⟩ := hxa
  -- Rewrite x = a * b using a = c * x to get x = b * c * x
  rw [hxa, mul_comm, ← mul_assoc] at h_mul
  -- Prove that b * c = 1
  have hbc1 : b * c = 1 := by
    -- Use the non-triviality of x to show that x = b * c * x implies b * c = 1
    apply (mul_eq_right₀ hnontrivial.left).mp
    -- Simplify the equation using the hypothesis h_mul
    rw [← h_mul]
  -- Conclude that b is a unit because b * c = 1
  exact isUnit_of_mul_eq_one b c hbc1


/-
In an integral domain, every prime element is irreducible.
-/
theorem isIrreducible_of_isPrime [IsDomain R] (x : R) (h : IsPrime x) : IsIrreducible x := by
  -- Obtain the non-triviality and divisibility properties from the prime condition
  obtain ⟨hnontrivial, hdiv⟩ := h
  -- Construct the IsIrreducible structure
  constructor
  -- Prove that x is non-trivial (not a unit and not zero)
  · exact hnontrivial
  -- Prove that if x = a * b, then a or b must be a unit
  · intros a b h_mul
    -- Since x is prime, x must divide a * b
    have hx_divides_ab : x | a * b := by
      use 1  -- Since x = x * 1
      rw [h_mul]
      simp  -- Simplify the equation
    -- Use the prime property to conclude that x divides either a or b
    have hxa_or_xb := hdiv a b hx_divides_ab
    -- Case analysis: either x divides a or x divides b
    rcases hxa_or_xb with hxa | hxb
    -- Case 1: x divides a
    · exact Or.inr (is_unit_of_mul_eq_one h_mul hnontrivial hxa)
      -- If x divides a, then a is a unit
    -- Case 2: x divides b
    · have h_mul1 : x = b * a := by
        rw [mul_comm]  -- Rewrite x = a * b as x = b * a
        exact h_mul
      exact Or.inl (is_unit_of_mul_eq_one h_mul1 hnontrivial hxb)
      -- If x divides b, then b is a unit


/-
Every irreducible element is prime in a factorial ring.
-/
theorem isPrime_of_isIrreducible [IsDomain R] [Inhabited R] (p : R) (h : IsIrreducible p) (hUFD : IsFactorialRing R) : IsPrime p := by
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
    obtain ⟨c, hdiv⟩ := hdiv -- pc = a * b
    by_cases hunit_a : IsUnit a
    · right
      obtain ⟨u, hu⟩ := hunit_a
      have hmul : b = ↑u⁻¹ * (c * p) := by
        subst hu
        refine (Units.eq_inv_mul_iff_mul_eq u).mpr ?_ -- rewrite goal
        exact hdiv
      simp [<- mul_assoc] at hmul
      use c * ↑u⁻¹
      subst hmul
      ring
    by_cases hunit_b : IsUnit b
    · left
      obtain ⟨u, hu⟩ := hunit_b
      rw [mul_comm] at hdiv
      have hmul : a = u⁻¹ * (c * p) := by
        subst hu
        exact (Units.eq_inv_mul_iff_mul_eq u).mpr hdiv
      rw [<- mul_assoc, mul_comm] at hmul
      use (u⁻¹ * c)
      subst hmul
      ring
    -- Step 3.1: c is non-zero
    by_cases hzero_c : c = 0
    · subst hzero_c
      simp at hdiv
      rcases hdiv with ⟨u, hu⟩
      · contradiction
      · contradiction
    -- Step 3.2: c is non-unit
    by_cases hunit_c : IsUnit c
    obtain ⟨u, hu⟩ := hunit_c
    have hdiv' : u⁻¹ * (a * b) = u⁻¹ * (c * p) := by
      subst hu
      exact ca_equals_ba hdiv
    subst hu
    rw [<- mul_assoc, <- mul_assoc] at hdiv'
    simp at hdiv'
    rw [mul_comm ↑u⁻¹ a, mul_assoc] at hdiv'
    have hdiv' : p = a * (↑u⁻¹ * b) := by subst hdiv'; rfl
    have hunits : IsUnit a ∨ IsUnit (↑u⁻¹ * b) := by
      apply hirr a (↑u⁻¹ * b) hdiv'
    rcases hunits with hunit_a | hunit_ub
    · contradiction
    · have hunit_b : IsUnit b := by
        obtain ⟨v, hv⟩ := hunit_ub
        have huv : u * v = b := by
          exact (Units.eq_inv_mul_iff_mul_eq u).mp hv
        have hunit_v : IsUnit v.val := by
          use v
        have hunit_u : IsUnit u.val := by
          use u
        have hunit_uv : IsUnit (u * v.val) := by
          exact IsUnit.mul hunit_u hunit_v
        rw [<- huv]
        exact hunit_uv
      contradiction
    -- Step 4: Because we're in a UFD, factor a*b and p*c into irreducibles,
    -- and show that the factorizations are the same

end Algebra'
