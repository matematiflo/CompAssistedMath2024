import Mathlib.Analysis.SpecialFunctions.Pow.Real

/- In this project sketch we define and prove some basic properties of divisibility in commutative rings.
Such as:
- Definition of divisibility
- Definition of associated elements and some basic properties
- Definition of irreducible elements
- Definition of prime elements
- Definition of unique factorization domains
- Theorem 1: In an integral domain, every prime element is irreducible.
- Theorem 2: In unique factorization domains, every irreducible element is prime.
 -/


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


-- it's reflective:
lemma isAssociated_of_eq (x : R) : IsAssociated x x := by
  use 1
  simp

-- it's symmetric:
lemma isAssociated_is_symmetric (x y: R) (h : IsAssociated x y) : IsAssociated y x := by
  obtain ⟨a, rfl⟩ := h
  use a⁻¹
  exact (Units.eq_inv_mul_iff_mul_eq a).mpr rfl

-- and transitive:
lemma isAssociated_is_transitive (x y z: R) (hxy : IsAssociated x y) (hyz : IsAssociated y z) : IsAssociated x z := by
  obtain ⟨a, ha⟩ := hxy
  obtain ⟨b, hb⟩ := hyz
  subst ha
  rw[<-mul_assoc] at hb
  subst hb
  let ba' : Rˣ := {
      val := b * a,
      inv := a⁻¹ * b⁻¹,
      val_inv := by
        ring_nf
        simp
      inv_val := by
        ring_nf
        simp
    }
  use ba'


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
  -- has not been annotated yet
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
We say an element `x : R` is non-trivial, if it is neither zero nor a unit.
-/

def IsNontrivial (x : R) : Prop := x ≠ 0 ∧ ¬ (IsUnit x)

/-
An irreducible element `x : R` is a non-trivial element such that whenever `x = a * b`,
either `a` is a unit or `b` is a unit.
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



/- lemma for the last step of Theorem 1:
x = ab, x|a, x non-trivial → b is a unit
-/

lemma  is_unit_of_mul_eq_one [IsDomain R] {a b x: R} (h_mul : x = a * b) (hnontrivial: IsNontrivial x) (hxa: Divides x a) : IsUnit b := by
  obtain ⟨c, hxa⟩ := hxa -- a = c * x
  rw [hxa, mul_comm, ←mul_assoc] at h_mul -- rewrite to a * b = x = b * c * x
  have hbc1 : b * c = 1 := by -- we use a property of 1 in domains to get b * c = 1
        apply (mul_eq_right₀ hnontrivial.left).mp
        rw[←h_mul]
  exact isUnit_of_mul_eq_one b c hbc1 -- in-built lemma: b * c = 1 → b is unit

/- Theorem 1: In an integral domain, every prime element is irreducible. -/
theorem isIrreducible_of_isPrime [IsDomain R] (x : R) (h : IsPrime x) : IsIrreducible x := by
  obtain ⟨hnontrivial, hdiv⟩ := h
  constructor
  · exact hnontrivial
  · intros a b h_mul
    -- x divides a * b, as x = a * b
    have hx_divides_ab : x | a*b := by
      use 1
      simp[h_mul]
    -- so x divides either a or b because it's prime
    have hxa_or_xb := hdiv a b hx_divides_ab
    rcases hxa_or_xb with hxa | hxb
    · -- if x | a, substitute a = c * x, to get x = x * (c * b)
      -- x≠0, so c * b = 1, thus b is a unit
      exact Or.inr (is_unit_of_mul_eq_one h_mul hnontrivial hxa)
    · -- same here
      have h_mul1 : x = b * a := by
        simp[mul_comm, h_mul]
      exact Or.inl (is_unit_of_mul_eq_one h_mul1 hnontrivial hxb)


-- Here we switch from R to D to more easily distinguish between the integral domain and UFD properties.

/-
We now define factorial rings (also called unique factorization domains) and show that in any UFD,
the converse of `isIrreducible_of_isPrime` holds, i.e. every irreducible element is prime.
-/
noncomputable instance (D: Type) [CommRing D] : Inhabited D := by
  exact Classical.inhabited_of_nonempty'
/-
In the next definition, we have to access element of factors2 list by using i ∈ Fin σ.length,
instead of i ∈ Fin factors2.length. It is no problem, because they are the same length, so we use get!,
which ignores the lengths, but requires existence of some element in D. Which, again, is obvious,
rings are bound to have a 0, but Lean doesn't know that.
Thus, we include these 2 lines above, which for some reason help Lean to realise inhabitedness of D.
-/

def IsUFD (D: Type) [CommRing D] [IsDomain D]: Prop :=
  -- It's based on an integral domain D
  -- every non-trivial element is factorable into irreducibles
  (∀ (x : D), x ≠ 0 → ¬IsUnit x → ∃ (factors :List D), -- for any non-zero, non-unit x in D there's a list
  ((∀ y ∈ factors, IsIrreducible y) ∧ x=List.prod factors)) ∧ -- of irreducibles that multiply to x
  -- And such factorisation is unique up to associates and permutation:
  (
  ∀ (x : D) (factors1 factors2 : List D), -- for any x in D, if there exist 2 lists
  x ≠ 0 → (¬IsUnit x) → -- such that x is non-zero and non-unit
  (x = List.prod factors1) → (x = List.prod factors2) → -- that x is the product of the factors in each list
  (∀ y ∈ factors1, IsIrreducible y) → (∀ y ∈ factors2, IsIrreducible y) → -- and those lists are made up of irreducibles
  ((factors1.length=factors2.length) ∧ -- then they are of equal length
  ∃ σ ∈ factors1.permutations, -- and there exists a permutation of one of them, here called sigma
  (∀ i : Fin σ.length,  (IsAssociated (σ.get i) (factors2.get! i )))) -- such that sigma[i] is associated to factors2[i]
  )

/- in the definition we could have used IsNontrivial x instead of a ≠ 0 and ¬IsUnit,
but we decided not to, to not need to fold and unfold the 2 properties of nontriviality all the time
-/


variable {D : Type} [CommRing D] [IsDomain D]


/- now a ** a few ** lemmas for the inverse theorem to make the body of the theorem more readable.
Annotated by the step they are used in.
-/

/-
From Step 2:
If ab=pc and a is a unit, then p|b.
-/
lemma units_dont_break_divisibility [IsDomain R] {a b c p : R}
  (hunit_a : IsUnit a) (hdiv : a * b = c * p) : (p | b) := by
  obtain ⟨u, hu⟩ := hunit_a
  -- Just multiply both sides by a⁻¹.
  have hmul :   b = ↑u⁻¹ * (c * p) := by
    subst hu
    refine (Units.eq_inv_mul_iff_mul_eq u).mpr ?_
    exact hdiv
  simp[<-mul_assoc] at hmul
  use c * ↑u⁻¹
  subst hmul
  ring


-- from Step 3.2: ab=pc, a and b non trivial, p prime → c non-unit

lemma c_is_non_unit {a b c p : D} (hdiv : a * b = c * p) (hirr : ∀ (a b : D), p = a * b → IsUnit a ∨ IsUnit b)
  (hunit_a : ¬IsUnit a) (hunit_b : ¬IsUnit b) : ¬IsUnit c := by
  -- proof by contradiction
  intro hunit_c
  obtain ⟨u, hu⟩ := hunit_c

  -- first use c⁻¹ to split p into to factors:
  -- p = ↑u⁻¹ * (a * b), ↑u=c
  have hdiv : p = ↑u⁻¹ * (a * b) := by
    subst hu
    apply (Units.eq_inv_mul_iff_mul_eq u).mpr
    simp[hdiv]
  rw[mul_comm, mul_assoc] at hdiv

  -- now use the fact that p is irreducible to show that one of 2 factors is unit
  have hunits: IsUnit a ∨ IsUnit (b*↑u⁻¹)  := by
    apply hirr a (b*↑u⁻¹) hdiv


  rcases hunits with hunit_a | hunit_ub
  ·  -- case "a is a unit" is a direct contradiction, a is non-unit
    contradiction
  · -- case u⁻¹*b is a unit
    -- We prove that b is a unit, again a contradiction
    have hunit_b: IsUnit b := by
      obtain ⟨v, hv⟩ := hunit_ub

      -- rewrite b to b = u * (↑u⁻¹ * b) := u * v
      have huv: u * v = b := by
        rw[mul_comm] at hv
        exact (Units.eq_inv_mul_iff_mul_eq u).mp hv

      -- a little problem along the way:
      -- when we obtain, we have v∈Rˣ, but we need v IsUnit, same with u
      have hunit_v: IsUnit v.val := by
        use v
      have hunit_u: IsUnit u.val := by
        use u

      -- and use the fact that multiplication of 2 units is a unit itself
      have hunit_uv: IsUnit (u.val * v.val) := by -- u.val here because it's in D, not in Dˣ
        exact IsUnit.mul hunit_u hunit_v

      -- substitute u * v = b
      rw[<-huv]
      exact hunit_uv

    contradiction -- to ¬IsUnit b

-- from Step 4.2: product of 2 units is not a unit, to show that ab is not a unit

lemma product_of_non_units_is_non_unit {a b: D} (hunit_b : ¬IsUnit b) : ¬IsUnit (a * b) := by
  intro hunit -- proof by contradiction

  -- more precisely, we show that b is a unit, if ab is a unit
  have hunit_b': IsUnit b := by
    obtain ⟨u, hu⟩ := hunit -- u * 1 = a * b

    -- many clumsy rewrites
    have humul' : b * (u⁻¹ * a) = 1  := by
      have hu': u * 1 = (a * b) := by simp[hu]
      have humul : 1 = u⁻¹ * (a * b) := by
        apply (Units.eq_inv_mul_iff_mul_eq u).mpr hu'
      simp[humul]
      ring

    -- now we have b * (↑u⁻¹ * a) = 1
    -- and use theorem that if x * y = 1, then x is a unit
    exact isUnit_of_mul_eq_one b (u⁻¹ * a) humul'
  contradiction


/- from Step 4.6: sub-lemma

The definition of a factorization and a permutation being associates was:
(∀ i : Fin σ.length,  (IsAssociated (σ.get i) (factors2.get! i )))
Thus, we need to find the index of p in factors_pc.
It's 0, because factors_pc := p ++ factors_c, BUT
in the definition, i : Fin σ.length, not i : Fin factors_pc.length or i : ℕ.

The following lemma converts 0 from ℕ to Fin σ.length.
-/
lemma fin_σ_has_index_for_p {factors_pc factors_c factors_ab σ : List D} {p: D} (h: factors_pc = [p]++factors_c)
 (hlength : factors_ab.length = factors_pc.length) (hσ : σ ∈ factors_ab.permutations) :
 (∃ j : Fin σ.length, p = factors_pc.get! j) := by

  have hpfactor : p = factors_pc.get! 0 := by
    simp[h]
  -- in short: σ.length=ab.length=pc.length>0, because p∈ factors_pc→ factors_pc≠[]
  have hpclengthgr0 : factors_pc.length > 0 := by
    have hfactors_pc_isnotnull : ¬factors_pc = [] := by
      intro hf
      simp[h] at hf
    exact (List.length_pos_iff_ne_nil.mpr hfactors_pc_isnotnull)

  have hσlengthgr0 : σ.length > 0 := by
    have hequallength : σ.length = factors_pc.length  := by
      rw[<-hlength]
      apply List.Perm.length_eq
      exact List.mem_permutations.mp hσ
    rw[hequallength]
    exact hpclengthgr0

  -- now that σ.length>0, we can just translate 0 from ℕ to Fin σ.length,
  -- and substitute the 0 of the corect type
  use @Fin.ofNat' σ.length 0 hσlengthgr0
  exact hpfactor

/- actual lemma used in theorem body:
just substitute 0 from previous sub-lemma into
(hσassoc : ∀ i : Fin σ.length, IsAssociated (σ.get i) (factors_pc.get! i))
-/
lemma p_has_an_associate_in_ab {factors_pc factors_c factors_ab σ : List D} {p: D} (h: factors_pc = [p]++factors_c)
 (hlength : factors_ab.length = factors_pc.length) (hσ : σ ∈ factors_ab.permutations)
 (hσassoc : ∀ i : Fin σ.length, IsAssociated (σ.get i) (factors_pc.get! i)) :
 (∃ i : Fin σ.length, IsAssociated (σ.get i) p) := by
  -- because in the definition we have only indexes of elements, we need to find the index of p in factors_pc
  obtain ⟨j, hfactorspc_j_equals_p⟩ := (fin_σ_has_index_for_p h hlength hσ)
  use j
  rw[hfactorspc_j_equals_p]
  exact hσassoc j


/- from Step 4.7:
 p is associated to one of factors in factors_ab →
 p is associated to one of factors in factors_a or factors_b
-/
lemma p_associate_of_a_or_b {factors_a factors_b factors_ab σ : List D} (h: factors_ab = factors_a ++ factors_b)
  (hσ : σ ∈ factors_ab.permutations)
  (hpassociatedwithab_i: (∃ i : Fin σ.length, IsAssociated (σ.get i) p)) :
  (∃ a ∈ factors_a, IsAssociated a p) ∨ (∃ b ∈ factors_b, IsAssociated b p) := by

  -- first we get out the index of p in σ to get σ[i]
  obtain ⟨i, hpi⟩ := hpassociatedwithab_i

  -- σ.get i ∈ σ:
  have hσiinσ : σ.get i ∈ σ := by
    refine List.mem_iff_get.mpr ?_
    use i
  -- any element from σ is element of factors_ab:
  have a_in_σ_a_in_ab: ∀ a ∈ σ, a∈ factors_ab := by
    intros a ha
    exact (List.Perm.mem_iff (List.mem_permutations.mp hσ)).mp ha

  -- and therefore σ.get i ∈ factors_ab = factors_a ++ factors_b
  have hσ_i_in_ab : σ.get i ∈ (factors_a ++ factors_b) := by
    subst h
    exact a_in_σ_a_in_ab (σ.get i) (hσiinσ)

  -- which we can split into 2 cases
  have hσ_i_in_a_or_b: (σ.get i) ∈ factors_a ∨ (σ.get i) ∈ factors_b := by
    exact (List.mem_append.mp hσ_i_in_ab)
  -- and resolve each one trivially
  rcases hσ_i_in_a_or_b with hσ_i_in_a | hσ_i_in_b
  · left
    use (σ.get i)
  · right
    use (σ.get i)

-- from Step 5
-- sub-lemma: if a_i ∈ factors_a, such that factors_a.prod = a, then a_i | a
lemma factor_divides_prod [IsDomain R] {a a_i : R} {factors_a : List R} (hfactors: a=factors_a.prod) (ha_i: a_i ∈ factors_a) : a_i | a := by
  obtain ⟨s, t, hsplit⟩ := (List.append_of_mem ha_i)
  simp[List.prod_cons, hsplit] at hfactors
  use s.prod * t.prod
  simp[hfactors]
  ring

-- actual lemma in the theorem body:
-- if a_i from factors_a is associated to p, then p|a,
lemma factor_associate_divides_prod [IsDomain R] {a p : R} {factors_a : List R}
 (hprodfactors_a : a = factors_a.prod) (hpa: ∃ a ∈ factors_a, IsAssociated a p):
  (p | a) := by
  -- name a_i the factor of a that is associated to p
  obtain ⟨a_i, ha_i, hp_assoc_a_i⟩ := hpa
  -- p * u = a_i by lemma
  obtain ⟨u, hu⟩ := (divides_divides_of_isAssociated a_i p hp_assoc_a_i).right
  -- a_i * a_rest = a by another lemma and the fact that a_i is in factors_a
  obtain ⟨a_rest, a_rest_div⟩  := factor_divides_prod hprodfactors_a ha_i
  -- so a = p * u * a_rest, thus p|a
  subst hu
  use a_rest * u
  simp[a_rest_div]
  ring


/-
Theorem 2: In unique factorization domains, every irreducible element is prime.
-/

theorem isPrime_of_isIrreducible (p : D) (h : IsIrreducible p) (hUFD: IsUFD D): IsPrime p := by
  obtain ⟨hnontrivial, hirr⟩ := h
  constructor
  · exact hnontrivial
  -- Step 2: a and b non-unit, non-zero, so nontrivial
  · intros a b hdiv
    obtain ⟨ c, hdiv ⟩ := hdiv -- a * b = c * p

    by_cases ha : a = 0
    · left
      rw [ha]
      exact everything_divides_zero p

    by_cases hb : b = 0
    · right
      rw [hb]
      exact everything_divides_zero p

    by_cases hunit_a : IsUnit a
    · right
      exact units_dont_break_divisibility hunit_a hdiv
      -- this multiplies by a⁻¹ and uses (a⁻¹ * c) * p = b

    by_cases hunit_b : IsUnit b
    · left; rw[mul_comm] at hdiv
      exact units_dont_break_divisibility hunit_b hdiv
      -- see previous case


    -- Step 3: c is nontrivial

    -- 3.1: c is non-zero
    by_cases hzero_c : c = 0
    · subst hzero_c -- if c were 0
      simp at hdiv --  then pc=0 and either a or b is 0
      rcases hdiv with ⟨u, hu⟩ -- but we've already handled that case
      · contradiction
      · contradiction

    -- Step 3.2: c is non-unit
    have hunit_c: ¬IsUnit c := by
      exact c_is_non_unit hdiv hirr hunit_a hunit_b


    -- Step 4: p is associated to one of the factors of a*b

    -- Step 4.1: Factorisation of a, b, c, ab, pc
    obtain ⟨hfactorisable, hunique⟩ := hUFD
    obtain ⟨factors_a, hfactor_a_irreducible, hprodfactors_a⟩ := hfactorisable a ha hunit_a
    obtain ⟨factors_b, hfactor_b_irreducible, hprodfactors_b⟩ := hfactorisable b hb hunit_b
    obtain ⟨factors_c, hfactor_c_irreducible, hprodfactors_c⟩ := hfactorisable c hzero_c hunit_c

    let factors_ab := factors_a ++ factors_b
    let factors_pc := [p] ++ factors_c  -- note that p is irreducible itself, so every element in [p] is irreducible

    -- Step 4.2: proof that a*b≠0 and a*b non-unit, to be able to use the UFD properties on it
    have habneq0 : a*b ≠ 0 := by simp[ha, hb]
    have habnotunit: ¬ IsUnit (a*b) := by
        exact product_of_non_units_is_non_unit hunit_b

    -- Step 4.3': factors_ab must be a factorisation of ab
    have hprodfactors_ab : a*b = List.prod factors_ab := by
      simp[factors_ab, hprodfactors_a, hprodfactors_b]

    -- Step 4.3: a factorisation of ab must be non-trivial to be unique up to association
    -- proof: as simple as split into a factor is in factors_a or factors_b
    have hfactor_ab_irreducible : ∀ y ∈ factors_ab, IsIrreducible y := by
      intros y hy
      simp[factors_ab] at hy
      rcases hy with hya | hyb
      · exact hfactor_a_irreducible y hya
      · exact hfactor_b_irreducible y hyb

    -- -- Step 4.4: same for p*c and factors_pc
    have hprodfactors_pc : a*b = List.prod factors_pc := by
      simp[factors_pc, hprodfactors_c, hdiv]
      ring

    have hfactor_pc_irreducible : ∀ y ∈ factors_pc, IsIrreducible y := by
      intros y hy
      simp[factors_pc] at hy
      rcases hy with rfl | hy
      · exact ⟨hnontrivial, hirr⟩ -- p itself is irreducible
      · exact hfactor_c_irreducible y hy

    -- Step 4.5: use the uniqueness of factorisation in UFD
    -- namely, for factors_ab and factors_pc is true:

    -- they are the same length:
    obtain hlength := (hunique (a*b) factors_ab factors_pc habneq0 habnotunit hprodfactors_ab hprodfactors_pc hfactor_ab_irreducible hfactor_pc_irreducible).1

    -- and there exists a permutation of factors_ab that makes it associate to factors_pc on per-element basis:
    obtain ⟨σ, hσ, hσassoc⟩ := (hunique (a*b) factors_ab factors_pc habneq0 habnotunit hprodfactors_ab hprodfactors_pc hfactor_ab_irreducible hfactor_pc_irreducible).2


    -- Step 4.6: p is associate to one of the factors in factors_ab
    -- very funny
    have hpassociatedwithab_i: (∃ i : Fin σ.length, IsAssociated (σ.get i) p) := by
      have hfactors_pc : factors_pc = [p] ++ factors_c := by
        rfl
      exact p_has_an_associate_in_ab hfactors_pc hlength hσ hσassoc

    /- Step 4.7:
     We know p is associated to one of elements of σ → one of factors_ab →
     one of factors in factors_a or factors_b
     -/
    have hp_assoc_a_or_b:
      (∃ a ∈ factors_a, IsAssociated a p) ∨ (∃ b ∈ factors_b, IsAssociated b p) := by
      have hfactors_ab : factors_ab = factors_a ++ factors_b := by
        rfl
      exact p_associate_of_a_or_b hfactors_ab hσ hpassociatedwithab_i


    /- Step 5: p is divides a or b.
    Rewrite a_i = p*u and a=a₁⬝a₂...a_{i-1}⬝p⬝u⬝a_{i+1}... in case hpa,
    or same with b in hpb

    -/
    rcases hp_assoc_a_or_b with hpa | hpb
    · left
      exact factor_associate_divides_prod hprodfactors_a hpa
    · right
      exact factor_associate_divides_prod hprodfactors_b hpb



end Algebra'
