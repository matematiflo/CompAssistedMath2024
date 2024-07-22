/-
# Continuity of real functions

Initial version by Judith Ludwig, Christian Merten and Florent Schaffhauser,
Proseminar on computer-assisted mathematics,
Heidelberg, Summer Semester 2024

Edited by Felix Lentze and Dominic Plein.

In this project, we show basic properties of continuous functions, give some
examples and prove basic properties. We also show that continuity is equivalent
to left- and right-continuity combined.
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-- We can find lemma names by using the library search tactic `exact?`. -/
example (x y : ℝ) : |x + y| ≤ |x| + |y| := by
  exact abs_add x y


--------------------------------------------------------------------------------
-- # Definition of continuity
--------------------------------------------------------------------------------

/-- Definition of a continuous function `f : D → ℝ` at a point `a ∈ D`. -/
def IsContinuousAt (D : Set ℝ) (f : D → ℝ) (a : D) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x : D,
  (|x.val - a.val| < δ  →  |f x - f a| < ε)

/-- Definition of a continuous function on a set `D`. -/
def IsContinuous (D : Set ℝ) (f : D → ℝ) : Prop :=
  ∀ a : D, IsContinuousAt D f a


--------------------------------------------------------------------------------
-- # Constant function `x ↦ c` with `c ∈ ℝ`
--------------------------------------------------------------------------------

/-- The constant function is continuous (at a given point `a ∈ D ⊆ ℝ`). -/
theorem constant_function_is_continuous_at_a_point
    (D : Set ℝ) (c : ℝ) (a : D)
    : IsContinuousAt D (fun _ ↦ c) a := by

  dsimp [IsContinuousAt]
  intro ε hεbigger0
  exists 1
  simp only [one_pos, true_and]

  intro x _h_xδ_criterion
  simp only [sub_self, abs_zero]
  exact hεbigger0

/-- The constant function is continuous. -/
theorem constant_function_is_continuous
    (D : Set ℝ) (c : ℝ)
    : IsContinuous D (fun _ ↦ c) := by

  intro a
  exact constant_function_is_continuous_at_a_point D c a


--------------------------------------------------------------------------------
-- # Function `x ↦ m * x + y₀` with `m, y₀ ∈ ℝ`
--------------------------------------------------------------------------------

/-- The function `x ↦ m * x + y₀` is continuous (at a given point `a ∈ D ⊆ ℝ`). -/
theorem lines_are_continuous_at_a_point
    (D : Set ℝ) (m y₀ : ℝ) (a : D)
    : IsContinuousAt D (fun x ↦ m * x + y₀) a := by

  by_cases m_cases : m = 0

  -- m = 0
  · subst m
    simp only [zero_mul, zero_add]
    exact constant_function_is_continuous_at_a_point D y₀ a

  -- m ≠ 0
  . push_neg at m_cases
    dsimp [IsContinuousAt]
    intro ε h_εbigger0

    let δ := ε / |m|
    use δ
    have h_δbigger0 : δ > 0 := by positivity
    simp only [h_δbigger0, true_and]

    intro x h_xδ_criterion
    simp

    let x' := x.val; let a' := a.val
    calc |m * x' - m * a'|

      _ = |m * (x' - a')|
        := by ring_nf

      _ = |m| * |x' - a'|
        := abs_mul m (x' - a')

      _ < |m| * δ
        := (mul_lt_mul_left (by positivity)).mpr h_xδ_criterion

      _ = |m| * (ε / |m|)
        := by rfl

      _ = ε
        := by field_simp

/-- The function `x ↦ m * x + y₀` is continuous. -/
theorem lines_are_continuous
    (D : Set ℝ) (m y₀ : ℝ)
    : IsContinuous D (fun x ↦ m * x + y₀) := by

  intro a
  exact lines_are_continuous_at_a_point D m y₀ a


--------------------------------------------------------------------------------
-- # Parabola `x ↦ x^2`
--------------------------------------------------------------------------------

/-- The function `x ↦ x^2` is continuous (at a given point `a ∈ D ⊆ ℝ`). -/
theorem parabola_is_continuous_at_a_point
    (D : Set ℝ) (a : D)
    : IsContinuousAt D (fun x ↦ x^2) a := by

  let a' := a.val
  dsimp [IsContinuousAt]
  intro ε h_εbigger0

  -- `δ` and its upper bounds
  let δ := ε / (2 * |a'| + 1) ⊓ 1
  use δ
  have h_δbigger0 : δ > 0 := by simp [δ]; positivity
  have h_δsmaller1 : δ ≤ 1 := inf_le_right
  have h_δsmallerε : δ ≤ ε / (2 * |a'| + 1) := inf_le_left
  simp only [h_δbigger0, true_and]

  -- `∀ x ∈ D`
  intro x h_xδ_criterion
  let x' := x.val

  -- Some inequalities for the calculation
  have h_triangle_inequality : |x' + a'| ≤ |x'| + |a'| := abs_add x' a'
  have h_x_smaller : |x'| < (|a'| + δ) := by calc
    |x'| = |a' + (x' - a')|  := by ring_nf
      _ <= |a'| + |x' - a'|  := abs_add a' (x' - a')
      _ < |a'| + δ           := by linarith [h_xδ_criterion]
  have h_x_smaller_with_added_term : |x'| + |a'| < (|a'| + δ) + |a'|
    := by linarith [h_x_smaller]

  calc |x'^2 - a'^2|

    _ = |(x' + a') * (x' - a')|
      := by ring_nf

    _ = |x' + a'| * |x' - a'|
      := abs_mul (x' + a') (x' - a')

    _ ≤ (|x'| + |a'|) * |x' - a'|
      := mul_le_mul_of_nonneg_right h_triangle_inequality (abs_nonneg (x' - a'))

    _ ≤ (|x'| + |a'|) * δ
      := mul_le_mul_of_nonneg_left (le_of_lt h_xδ_criterion) (by positivity)

    _ < ((|a'| + δ) + |a'| ) * δ
      := (mul_lt_mul_iff_of_pos_right h_δbigger0).mpr h_x_smaller_with_added_term

    _ = (2 * |a'| + δ) * δ
      := by ring_nf

    _ ≤ (2 * |a'| + 1) * δ
      := (mul_le_mul_iff_of_pos_right h_δbigger0).mpr (by linarith [h_δsmaller1])

    _ ≤ (2 * |a'| + 1) * (ε / (2 * |a'| + 1))
      := mul_le_mul_of_nonneg_left h_δsmallerε (by positivity)

    _ = ε
      := by field_simp

/-- The function `x ↦ x^2` is continuous. -/
theorem parabola_is_continuous
    (D : Set ℝ)
    : IsContinuous D (fun x ↦ x^2) := by

  intro a
  exact parabola_is_continuous_at_a_point D a


--------------------------------------------------------------------------------
-- # Hyperbola `x ↦ 1/x`
--------------------------------------------------------------------------------

/-- `a ∈ D` implies `a ≠ 0` since `D = { a | a ≠ 0 }` -/
lemma element_not_zero_if_set_has_no_zero
    (D : Set ℝ) (h_0notinD : 0 ∉ D) (a : D)
    : a.val ≠ 0 := by
  apply ne_of_mem_of_not_mem a.property
  exact h_0notinD

/-- For `a, b ∈ ℝ`, we have `|a| - |b| ≤ |a + b|`. -/
lemma reverse_triangle_inequality (a b : ℝ) : |a| - |b| ≤ |a + b| := by
  let m : ℝ := a + b
  let n : ℝ := -b
  have h_mn : m + n = a := by ring_nf
  calc |a| - |b| = |m + n| - |n| := by rw [h_mn, abs_neg]
               _ ≤ |m| := by linarith [abs_add m n]
               _ = |a + b| := by rfl


/-- The function `x ↦ 1/x` is continuous
(at a given point `a ∈ D ⊆ ℝ` with `0 ≠ D`) -/
theorem hyperbola_is_continuous_at_a_point
    (D : Set ℝ) (h_0notinD : 0 ∉ D) (a : D)
    : IsContinuousAt D (fun x ↦ 1/x) a := by

  let a' := a.val
  have h_a_not_0 : a' ≠ 0 := element_not_zero_if_set_has_no_zero D h_0notinD a
  dsimp [IsContinuousAt]
  intro ε h_εbigger0

  -- `δ` and its upper bounds
  let δ := ε * |a'|^2 / 2 ⊓ |a'| / 2
  use δ
  have h_δbigger0 : δ > 0 := by
    simp [δ]
    constructor
    . exact mul_pos h_εbigger0 (sq_pos_of_ne_zero h_a_not_0)
    . exact h_a_not_0
  have h_δsmallerfirst : δ ≤ ε * |a'|^2 / 2 := inf_le_left
  have h_δsmallersecond : δ ≤ |a'| / 2 := inf_le_right
  simp only [h_δbigger0, true_and]

  -- `∀ x ∈ D`
  intro x h_xδ_criterion
  let x' := x.val
  have h_x_not_0 : x' ≠ 0 := element_not_zero_if_set_has_no_zero D h_0notinD x

  -- Some inequalities for the calculation
  have h_x_bigger_a : |x'| > |a'| / 2 := by
    calc |x'|   = |a' + (x' - a')|  := by ring_nf
      _ ≥ |a'| - |x' - a'|  := by linarith [reverse_triangle_inequality a' (x' - a')]
      _ > |a'| - δ          := by linarith [h_xδ_criterion]
      _ ≥ |a'| / 2          := by linarith [h_δsmallersecond]
  have h_x_bigger_a_with_factor : |a'| * |x'| > |a'| * (|a'| / 2) := by
    apply mul_lt_mul_of_pos_left h_x_bigger_a
    simp [h_a_not_0]

  calc |1/x' - 1/a'|

    _ = |(a' - x') / (a' * x')|
      := by rw [div_sub_div 1 1 h_x_not_0 h_a_not_0]; ring_nf

    _ = |x' - a'| / (|a'| * |x'|)
      := by rw [abs_div, abs_mul, abs_sub_comm]

    _ < δ / (|a'| * |x'|)
      := (div_lt_div_right (by positivity)).mpr h_xδ_criterion

    _ < δ / (|a'| * (|a'| / 2))
      := (div_lt_div_left h_δbigger0 (by positivity) (by positivity)).mpr
        h_x_bigger_a_with_factor

    _ ≤ (ε * |a'|^2 / 2) / (|a'| * (|a'| / 2))
      := (div_le_div_right (by positivity)).mpr h_δsmallerfirst

    _ = (ε * |a'|^2 / 2) / (|a'|^2 / 2)
      := by ring_nf

    _ = ε
      := by field_simp

/-
  You might ask yourself whether `fun x ↦ 1/x` is continuous at `a=0`.
  From a mathematical point of view, we cannot give an answer as we've only
  defined continuity at points `a ∈ D`, i.e. points in the domain of the function.
  For `1/x`, we don't consider `ℝ` as the domain, but `ℝ \ {0}` since 1/0 is
  not defined.

  However, things are different in Lean4. Here, 1/0 is defined as 0 (see
  the theorem `div_zero`). Therefore, it's possible to prove that `fun x ↦ 1/x`
  is not continuous at `a=0` in Lean4. E.g. consider the sequence `1/n`, which
  converges to `0` for `n → ∞`, but `1/(1/n) = n`, which diverges and in particular
  is not equal to `1/0 = 0`.

  We haven't gotten to this part yet, as we didn't understand the question
  in the beginning. We will try to file in another PR in the (near) future
  with a proof.

  example : ¬IsContinuousAt Set.univ (fun x ↦ 1/x) ⟨0, trivial⟩
-/


--------------------------------------------------------------------------------
-- # Sum of two continuous functions `f` and `g`
--------------------------------------------------------------------------------

/-- The sum of two continuous functions is continuous. -/
theorem sum_of_two_continuous_functions_is_continuous
    (D : Set ℝ) (f: D → ℝ) (g: D → ℝ)
    (h_f_continuous: IsContinuous D f) (h_g_continuous: IsContinuous D g)
    : IsContinuous D (f + g) := by

  intro a
  dsimp [IsContinuousAt]
  intro ε h_εbigger0

  -- Individual continuity of f and g
  have h_f_continuous_short : ∃ δ₁ > 0, ∀ x : D,
      |x.val - a| < δ₁ → |f x - f a| < ε/2 := by
    apply h_f_continuous
    simp
    exact h_εbigger0

  have h_g_continuous_short : ∃ δ₂ > 0, ∀ x : D,
      |x.val - a| < δ₂ → |g x - g a| < ε/2 := by
    apply h_g_continuous
    simp
    exact h_εbigger0

  -- Choice of `δ`
  obtain ⟨δ₁, δ₁_positive, hδ₁⟩ := h_f_continuous_short
  obtain ⟨δ₂, δ₂_positive, hδ₂⟩ := h_g_continuous_short
  use min δ₁ δ₂

  constructor
  -- min δ₁ δ₂ > 0
  · apply lt_min δ₁_positive δ₂_positive

  -- Continuity of f + g
  · intro x h_δ_criterion

    have h_f_estimate : |f x - f a| < ε/2 := by
      apply hδ₁ x (lt_of_lt_of_le h_δ_criterion (min_le_left δ₁ δ₂))
    have h_g_estimate : |g x - g a| < ε/2 := by
      apply hδ₂ x (lt_of_lt_of_le h_δ_criterion (min_le_right δ₁ δ₂))

    simp
    calc |f x + g x - (f a + g a)|

      _ = |(f x - f a) + (g x - g a)|
        := by ring_nf

      _ ≤ |f x - f a| + |g x - g a|
        := by exact abs_add (f x - f a) (g x - g a)

      _ < ε/2 + ε/2
        := add_lt_add h_f_estimate h_g_estimate

      _ = ε
        := by linarith


--------------------------------------------------------------------------------
-- # Product of two continuous functions `f` and `g`
--------------------------------------------------------------------------------

/-- The product of two continuous functions is continuous -/
theorem product_of_two_continuous_functions_is_continuous
    (D : Set ℝ) (f: D → ℝ) (g: D → ℝ)
    (h_f_continuous: IsContinuous D f) (h_g_continuous: IsContinuous D g)
    : IsContinuous D (f * g) := by

  intro a
  dsimp [IsContinuousAt]
  intro ε h_εbigger0

  -- Individual continuity of f and g
  have h_f_continuous_short : ∃ δ₁ > 0, ∀ x : D,
      |x.val - a| < δ₁ → |f x - f a| < ε / (2 * |g a| + 1) := by
    apply h_f_continuous
    apply div_pos h_εbigger0
    apply add_pos_of_nonneg_of_pos
    simp [abs_nonneg]
    exact by field_simp

  have h_g_continuous_short : ∃ δ₂ > 0, ∀ x : D,
      |x.val - a| < δ₂ → |g x - g a| < ε / (2 * (ε + |f a|)) := by
    apply h_g_continuous
    apply div_pos h_εbigger0
    simp
    apply add_pos_of_pos_of_nonneg h_εbigger0
    simp [abs_nonneg]

  -- Choice of `δ`
  obtain ⟨δ₁, δ₁_positive, hδ₁⟩ := h_f_continuous_short
  obtain ⟨δ₂, δ₂_positive, hδ₂⟩ := h_g_continuous_short
  use min δ₁ δ₂

  constructor
  -- min δ₁ δ₂ > 0
  · apply lt_min δ₁_positive δ₂_positive

  -- Continuity of f * g
  · intro x h_δ_criterion

    have h_f_estimate : |f x - f a| < (ε / (2 * |g a| + 1)) := by
      apply hδ₁ x
      exact lt_of_lt_of_le h_δ_criterion (min_le_left δ₁ δ₂)

    have h_g_estimate : |g x - g a| < ε / (2 * (ε + |f a|)) := by
      apply hδ₂ x
      exact lt_of_lt_of_le h_δ_criterion (min_le_right δ₁ δ₂)

    have h_f_smaller_epsilon : |f x| - |f a| < ε := by
      calc |f x| - |f a|
        _ ≤ |f x - f a| := by exact abs_sub_abs_le_abs_sub (f x) (f a)
        _ < ε / (2 * |g a| + 1) := h_f_estimate
        _ ≤ ε := by
          apply div_le_self
          · exact (le_of_lt h_εbigger0) -- ε > 0
          · simp

    have h_frac_smaller_one : |g a| / (|g a| + 1/2) ≤ 1 := by
      rw [div_le_one]
      . exact by linarith
      . exact by field_simp

    have h_ε_for_g : ε / (2 * |g a| + 1) * |g a| ≤ ε/2 := by
      calc ε / (2 * |g a| + 1) * |g a|
        _ = ε / 2 * (|g a| / (|g a| + 1/2)) := by field_simp; linarith
        _ ≤ ε / 2 * 1 := by
          apply mul_le_mul_of_nonneg_left
          exact h_frac_smaller_one
          apply le_of_lt
          simp; exact h_εbigger0
        _ = ε / 2 := by linarith

    calc |(f * g) x - (f * g) a|

      _ = |f x * g x - f a * g a|
        := by simp [mul_sub]

      _ = |f x * g x - f x * g a + f x * g a - f a * g a|
        := by ring_nf

      _ = |f x * (g x - g a)  +  (f x - f a) * g a|
        := by ring_nf

      _ ≤ |f x * (g x - g a)| + |(f x - f a) * g a|
        := abs_add _ _

      _ = |f x| * |g x - g a| + |f x - f a| * |g a|
        := by simp [abs_mul]

      _ ≤ |f x| * (ε / (2 * (ε + |f a|))) + |f x - f a| * |g a|
        := by
          simp only [add_le_add_iff_right]
          apply mul_le_mul_of_nonneg_left
          apply le_of_lt
          apply h_g_estimate
          apply abs_nonneg

      _ ≤ |f x| * (ε / (2 * (ε + |f a|))) + ε / (2 * |g a| + 1) * |g a|
        := by
          simp only [add_le_add_iff_left]
          apply mul_le_mul_of_nonneg_right
          apply le_of_lt
          apply h_f_estimate
          apply abs_nonneg

      _ < (ε + |f a|) * (ε / (2 * (ε + |f a|))) + ε / (2 * |g a| + 1) * |g a|
        := by
          simp only [add_lt_add_iff_right]
          apply mul_lt_mul_of_pos_right
          exact by linarith [h_f_smaller_epsilon]
          apply div_pos h_εbigger0
          simp
          apply add_pos_of_pos_of_nonneg h_εbigger0
          simp [abs_nonneg]

      _ = ε / 2 + ε / (2 * |g a| + 1) * |g a|
        := by field_simp; linarith

      _ ≤ ε / 2 + ε / 2
        := by
          simp only [add_le_add_iff_left]
          exact h_ε_for_g

      _ = ε
        := by linarith


--------------------------------------------------------------------------------
-- # Definition of left- and right-continuity
--------------------------------------------------------------------------------

/-- Definition of a left-continuous function `f: D → ℝ`. -/
def IsLeftContinuousAt (D : Set ℝ) (f : D → ℝ) (a : D) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x : D,
  x < a → (|x.val - a.val| < δ  →  |f x - f a| < ε)

/-- Definition of a right-continuous function `f: D → ℝ`. -/
def IsRightContinuousAt (D : Set ℝ) (f : D → ℝ) (a : D) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x : D,
  x > a → (|x.val - a.val| < δ  →  |f x - f a| < ε)


--------------------------------------------------------------------------------
-- # Heaviside function as example
--------------------------------------------------------------------------------

/--
  Definition of the Heaviside function, often denoted `Θ` in literature.

  By the keyword `noncomputable`, we signal Lean4 that this function does not have
  a constructive computational method within the confines of Lean's type theory
  and logic. You may want to look up "decidability in computer science" for more
  information on this topic, e.g. the halting problem and deterministic finite
  automata.

  The `@[simp]` attribute tells Lean to use this definition as a simplification rule
  when simplifying expressions via the `simp` tactic.
-/
@[simp]
noncomputable def Heaviside (x : ℝ) : ℝ := if x < 0 then 0 else 1

/-- The Heaviside function is right-continuous. -/
example : IsRightContinuousAt Set.univ (fun x ↦ Heaviside x) ⟨0, trivial⟩ := by
  intro ε hεbigger0
  use 1
  simp
  intro x h_x_gt_zero _h_xδ_criterion

  -- Variant 1: via `split_ifs`
  split_ifs with h_xvalue
  · linarith
  · simp only [sub_self, abs_zero]
    exact hεbigger0

  -- Variant 2: via `if_neg`
  -- rw [if_neg]
  -- · simp only [sub_self, abs_zero]
  --   exact hεbigger0
  -- · simp only [not_lt]
  --   exact le_of_lt h_x_gt_zero

/-- The Heaviside function is not continuous (at `a = 0`). -/
example : ¬IsContinuousAt Set.univ (fun x ↦ Heaviside x) ⟨0, trivial⟩ := by
  -- We proof by contradiction, so we assume that the function is continuous
  -- and show that this leads to a `False` truth-value.
  intro h_is_continuous

  let ε := (1:ℝ)/2
  choose δ δ_pos hδ using h_is_continuous ε (by positivity)

  let x := -δ/2
  have h_x_smaller_zero : x < 0 := by dsimp [x]; linarith
  have _h_x_smaller_delta : x < δ := by dsimp [x]; linarith
  have h_x_smaller_delta' : |x| < δ := by
    dsimp [x]
    simp only [abs_lt]
    constructor
    · linarith
    · linarith

  -- Construct contradiction
  have h_heaviside : |Heaviside x  - Heaviside 0| = 1 := by
    simp [Heaviside, h_x_smaller_zero]

  have h_heaviside_ε : |Heaviside x - Heaviside 0| < ε := by
    simp [Heaviside] at hδ
    simp
    exact hδ x h_x_smaller_delta'

  have h_blow_up_math : ε > 1 := by
    calc ε > |Heaviside x - Heaviside 0| := h_heaviside_ε
      _ = 1 := h_heaviside

  exact absurd h_blow_up_math (by norm_num)


--------------------------------------------------------------------------------
-- # Equivalence of continuity and left- and right-continuity
--------------------------------------------------------------------------------

theorem LeftRightContinuousIffIsContinuous
    (D : Set ℝ) (f: D → ℝ) (a : D)
    : (IsContinuousAt D f a)
      ↔ (IsLeftContinuousAt D f a ∧ IsRightContinuousAt D f a) := by

  constructor

  -- Left side implies right side,
  -- i.e. (continuity) → (left- and right-continuity)
  · intro h_continuous
    constructor

    -- Left-continuity
    · dsimp [IsLeftContinuousAt]
      intro ε h_εbigger0
      obtain ⟨δ, h_δbigger0, h_δ⟩ := h_continuous ε (by linarith)
      use δ
      use h_δbigger0
      intro x _h_x_smaller_a h_x_δ_criterion
      exact h_δ x h_x_δ_criterion

    -- Right-continuity
    · dsimp [IsLeftContinuousAt]
      intro ε h_εbigger0
      obtain ⟨δ, h_δbigger0, h_δ⟩ := h_continuous ε (by linarith)
      use δ
      use h_δbigger0
      intro x _h_x_bigger_a h_x_δ_criterion
      exact h_δ x h_x_δ_criterion

  -- Right side implies left side,
  -- i.e. (left- and right-continuity) → (continuity)
  · intro h_left_and_right_continuous
    rcases h_left_and_right_continuous with ⟨left_continuous, right_continuous⟩
    intro ε h_εbigger0

    -- `δ₁` and `δ₂` obtained from left- and right-continuity
    obtain ⟨δ₁, hδ₁, hδ₁_prop⟩ := left_continuous ε (by linarith)
    obtain ⟨δ₂, hδ₂, hδ₂_prop⟩ := right_continuous (ε) (by linarith)
    use min δ₁ δ₂
    use lt_min hδ₁ hδ₂

    intro x h_x_δ_criterion

    by_cases h_a_value : x < a
    -- x < a (use left-continuity)
    · apply hδ₁_prop x h_a_value
      apply lt_of_lt_of_le h_x_δ_criterion
      apply min_le_left

    -- x ≥ a
    · push_neg at h_a_value
      by_cases h_a_value' : x = a
      -- x = a
      · rewrite [h_a_value']
        simp [abs_zero, h_εbigger0]
      -- x > a (use right-continuity)
      · have h_x_bigger_a : x > a := by
          push_neg at h_a_value'
          exact lt_of_le_of_ne h_a_value (id (Ne.symm h_a_value'))
        apply hδ₂_prop x h_x_bigger_a
        apply lt_of_lt_of_le h_x_δ_criterion
        apply min_le_right
