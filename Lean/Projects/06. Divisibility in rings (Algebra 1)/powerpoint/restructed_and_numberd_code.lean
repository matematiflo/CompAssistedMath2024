PLS DONT CHANGE IF NOT NECESSARY THIS IS FOR SCREENSHOTS IT DOENST NEED TO WORK



namespace Algebra'

def Divides (x y : R) : Prop :=
  ∃ a, y = a * x

notation x " | " y => Divides x y

def IsAssociated (x y : R) : Prop :=
  ∃ (a : R), y = a * x

def IsNontrivial (x : R) : Prop := x ≠ 0 ∧ ¬ (IsUnit x)

def IsIrreducible (x : R) : Prop :=
  IsNontrivial x ∧ ∀ a b, x = a * b → IsUnit a ∨ IsUnit b

def IsPrime (x : R) : Prop :=
  IsNontrivial x ∧ ∀ a b, (x | a * b) → (x | a) ∨ (x | b)

def IsFactorialRing (R: Type) [CommRing R] [IsDomain R] [Inhabited R]: Prop := -- Ring has a 0 by default, Inhabited R only done for Lean to stop complaining
  (∀ (x : R), x ≠ 0 → ¬IsUnit x → ∃ (factors :List R), ((∀ y ∈ factors, IsIrreducible y) ∧ x=List.prod factors)) ∧
  (
  ∀ (x : R) (factors1 factors2 : List R), -- there exist 2 lists
  x ≠ 0 → (¬IsUnit x) → -- for any x in R that is non-zero and non-unit
  (x = List.prod factors1) → (x = List.prod factors2) → -- such that x is the product of the factors in each list
  (∀ y ∈ factors1, IsIrreducible y) → (∀ y ∈ factors2, IsIrreducible y) → -- and those lists are made up of irreducibles
  ((factors1.length=factors2.length) ∧ -- then they are of equal length
  ∃ σ ∈ factors1.permutations, -- and there exists a permutation of one of them, here called sigma
  (∀ i : Fin σ.length,  (IsAssociated (σ.get i) (factors2.get! i )))) -- such that sigma_i is associated to factors2_i
  )

def IsFactorialRing (R: Type) [CommRing R] [IsDomain R] [Inhabited R]: Prop :=
  (∀ (x : R), x ≠ 0 → ¬IsUnit x → ∃ (factors : List R),
  (∀ y ∈ factors, IsIrreducible y) ∧ x = List.prod factors) ∧
  (∀ (x : R) (factors1 factors2 : List R),
    x ≠ 0 → ¬IsUnit x →
    (x = List.prod factors1) → (x = List.prod factors2) →
    (∀ y ∈ factors1, IsIrreducible y) → (∀ y ∈ factors2, IsIrreducible y) →
    ((factors1.length = factors2.length) ∧
    ∃ σ ∈ factors1.permutations,
    (∀ i : Fin σ.length, IsAssociated (σ.get i) (factors2.get! i))))




lemma zero_of_zero_divides (x : R) (hx : 0 | x) : x = 0 := by
  obtain ⟨a, ha⟩ := hx
  simpa using ha

lemma everything_divides_zero (x : R) : x | 0 := by
  use 0
  simp

lemma ne_zero_of_divides_of_ne_zero (x y : R) (hy : y ≠ 0) (hxy : x | y) : x ≠ 0 := by
  intro hx
  subst hx
  exact hy (zero_of_zero_divides y hxy)



lemma isAssociated_of_eq (x : R) : IsAssociated x x := by
  use 1
  simp



lemma divides_divides_of_isAssociated (x y : R) (h : IsAssociated x y) :
    (x | y) ∧ (y | x) := by
  obtain ⟨a, ha⟩ := h
  constructor
  · use a
  · use a.inv
    rw [ha]
    simp

lemma isAssociated_of_divides_divides_of_domain /- Define a lemma named `isAssociated_of_divides_divides_of_domain` -/
  [IsDomain R] /- Assume `R` is a domain (i.e., a commutative ring with no zero divisors) -/
  (x y : R) /- Introduce elements `x` and `y` in `R` -/
  (hxy : x | y) /- Assume `x` divides `y` -/
  (hyx : y | x) /- Assume `y` divides `x` -/ :
  IsAssociated x y := by /- We aim to prove `x` is associated with `y` -/
  by_cases hx : x = 0 /- Consider the case whether `x = 0` -/
  · subst hx /- If `x = 0`, substitute `x` with `0` in the goal -/
    have h1 : y = 0 := zero_of_zero_divides y hxy /- Since `x = 0` divides `y`, `y` must be `0` by Lemma 1 -/
    subst h1 /- Substitute `y` with `0` in the goal -/
    apply isAssociated_of_eq /- Apply the lemma stating that zero is associated with zero -/
  · simp at hx /- Simplify the negation `hx : x ≠ 0` -/
    obtain ⟨a, ha⟩ := hxy /- Obtain an element `a` such that `y = a * x` from `x | y` -/
    obtain ⟨b, hb⟩ := hyx /- Obtain an element `b` such that `x = b * y` from `y | x` -/
    have hba : b * a = 1 := by /- Prove that `b * a = 1` -/
      rw [ha, ← mul_assoc] at hb /- Rewrite `hb` using `ha` and associativity of multiplication -/
      exact (mul_eq_right₀ hx).mp (id (Eq.symm hb)) /- Show `b * a = 1` using the property of no zero divisors -/
    have hab : a * b = 1 := by /- Prove that `a * b = 1` -/
      rw [mul_comm a b] /- Use commutativity of multiplication to rewrite `a * b` as `b * a` -/
      exact hba /- Conclude that `a * b = 1` from `b * a = 1` -/
    let a' : Rˣ := { /- Define `a'` as a unit in `R` -/
      val := a, /- The value of `a'` is `a` -/
      inv := b, /- The inverse of `a'` is `b` -/
      val_inv := hab, /- The property that `val * inv = 1` -/
      inv_val := hba /- The property that `inv * val = 1` -/
    }
    use a' /- Use `a'` to show that `x` is associated with `y` -/


lemma isAssociated_iff_divides_divides_of_domain [IsDomain R] (x y : R) :
    IsAssociated x y ↔ (x | y) ∧ (y | x) := by
  constructor
  · exact divides_divides_of_isAssociated x y
  · intro ⟨hxy, hyx⟩
    exact isAssociated_of_divides_divides_of_domain x y hxy hyx


lemma ca_equals_ba [IsDomain R] {a b c: R} (h: a = b) : c*a = c*b := by
  apply mul_eq_mul_left_iff.mpr
  apply Or.inl
  exact h

lemma ac_equals_bc [IsDomain R] {a b c: R} (h: a = b) : a*c = b*c := by
  apply mul_eq_mul_right_iff.mpr
  apply Or.inl
  exact h

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

variable {R : Type} [CommRing R] [IsDomain R] [Inhabited R]

theorem isPrime_of_isIrreducible (p : R) (h : IsIrreducible p) (hUFD: IsFactorialRing R): IsPrime p := by
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
    by_cases hunit_c : IsUnit c
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
    rcases hunits with hunit_a | hunit_ub
    · contradiction
    · have hunit_b: IsUnit b := by
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

end Algebra'
