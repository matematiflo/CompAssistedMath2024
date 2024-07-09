import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option pp.all true

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
  -- Every non-zero and non-unit element is factorizable into irreducibles.
  (∀ (x : R), x ≠ 0 → ¬IsUnit x → ∃ (factors : List R),
    (∀ y ∈ factors, IsIrreducible y) ∧ x = List.prod factors) ∧
  -- Such factorization is unique up to associates and permutation.
  (∀ (x : R) (factors1 factors2 : List R),
    x ≠ 0 → ¬IsUnit x →
    x = List.prod factors1 → x = List.prod factors2 →
    (∀ y ∈ factors1, IsIrreducible y) → (∀ y ∈ factors2, IsIrreducible y) →
    (factors1.length = factors2.length ∧
    ∃ σ ∈ factors1.permutations,
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

lemma is_unit_of_mul_eq_one [IsDomain R] {a b x : R} (h_mul : x = a * b) (hnontrivial : IsNontrivial x) (hxa : Divides x a) : IsUnit b := by
  obtain ⟨c, hxa⟩ := hxa -- a = c * x
  rw [hxa, mul_comm, ← mul_assoc] at h_mul -- rewrite to x = a * b = b * a = b * c * x
  have hbc1 : b * c = 1 := by -- proof that b * c = 1
    apply (mul_eq_right₀ hnontrivial.left).mp
    rw [← h_mul]
  exact isUnit_of_mul_eq_one b c hbc1

/-
In an integral domain, every prime element is irreducible.
-/
theorem isIrreducible_of_isPrime [IsDomain R] (x : R) (h : IsPrime x) : IsIrreducible x := by
  obtain ⟨hnontrivial, hdiv⟩ := h
  constructor
  · exact hnontrivial
  · intros a b h_mul
    have hx_divides_ab : x | a * b := by
      use 1
      rw [h_mul]
      simp
    have hxa_or_xb := hdiv a b hx_divides_ab
    -- x divides either a or b because it's prime
    rcases hxa_or_xb with hxa | hxb
    · exact Or.inr (is_unit_of_mul_eq_one h_mul hnontrivial hxa)
    · have h_mul1 : x = b * a := by
        rw [mul_comm]
        exact h_mul
      exact Or.inl (is_unit_of_mul_eq_one h_mul1 hnontrivial hxb)

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
