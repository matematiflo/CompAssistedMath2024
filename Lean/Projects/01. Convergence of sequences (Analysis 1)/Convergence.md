# Convergence of sequences

By Judith Ludwig, Christian Merten and Florent Schaffhauser,
Proseminar on computer-assisted mathematics,
Heidelberg, Summer Semester 2024

In this project, we show basic properties of convergent sequences. The goal is to show that the sequence of the `n`-th root of `n` converges to one.

```lean
import Mathlib.Analysis.SpecialFunctions.Pow.Real
```

We can find lemma names by using the library search tactic `exact?`.

```lean
example (x y : ℝ) : |x + y| ≤ |x| + |y| := by
  exact abs_add x y
```

Definition of a convergent sequence `a : ℕ → ℝ`.

```lean
def ConvergesTo (a : ℕ → ℝ) (x : ℝ) : Prop :=
  ∀ ε > 0, ∃ (n : ℕ), ∀ m ≥ n, |a m - x| < ε

namespace ConvergesTo
```

The definition of `ConvergesTo` unwrapped.

```lean
lemma iff (a : ℕ → ℝ) (x : ℝ) :
    ConvergesTo a x ↔ ∀ ε > 0, ∃ (n : ℕ), ∀ m ≥ n, |a m - x| < ε := by
  rfl
```

In the definition of `ConvergesTo`, we may replace the condition `< ε` by `≤ ε`.

```lean
lemma iff' (a : ℕ → ℝ) (x : ℝ) :
    ConvergesTo a x ↔ ∀ ε > 0, ∃ (n : ℕ), ∀ m ≥ n, |a m - x| ≤ ε := by
  constructor
  · intro h ε hε
    obtain ⟨n, hn⟩ := h ε hε
    use n
    intro m hmn
    exact le_of_lt (hn m hmn)
  · intro h ε hε
    obtain ⟨n, hn⟩ := h (ε / 2) (by simpa)
    use n
    intro m hmn
    have : |a m - x| ≤ ε / 2 := hn m hmn
    have : ε / 2 < ε := by simpa
    linarith
```

Constant sequences converge to the constant value.

```lean
theorem of_constant (x : ℝ) : ConvergesTo (fun _ ↦ x)  x := by
  dsimp [ConvergesTo]
  intro ε hε
  use 0
  intro m _
  simp only [sub_self, abs_zero]
  assumption
```

The sequence `1 / n` converges to zero. Here is a proof, with only two 'sorry's left to fill.

```lean
example : ConvergesTo (fun n ↦ 1 / n) 0 := by
  rw [iff']
  intro ε hε
  use ⌈1/ε⌉₊
  intro m hm
  have hle₁ : (1 / m : ℝ) ≤ (1 / ⌈1 / ε⌉₊ : ℝ) := by
    apply one_div_le_one_div_of_le
    · simpa
    · simpa using hm
  have hle₂ : (1 / ⌈1 / ε⌉₊ : ℝ) ≤ 1 / (1 / ε) := by
    apply one_div_le_one_div_of_le
    · simpa
    · exact Nat.le_ceil (1 / ε)
  calc
    |(1 / m : ℝ) - 0| = (1 / m : ℝ) := by simp
                    _ ≤ (1 / ⌈1 / ε⌉₊ : ℝ) := hle₁
                    _ ≤ 1 / (1 / ε) := hle₂
                    _ = ε := one_div_one_div ε
```

The sum of two convergent sequences is convergent and the limit is the sum of the limits. There is one `sorry` left to fill, though!

```lean
theorem add (a₁ a₂ : ℕ → ℝ) (x₁ x₂ : ℝ) (h₁ : ConvergesTo a₁ x₁)
    (h₂ : ConvergesTo a₂ x₂) : ConvergesTo (a₁ + a₂) (x₁ + x₂) := by
  intro ε hε
  obtain ⟨n₁, hn₁⟩ := h₁ (ε / 2) (by simpa)
  obtain ⟨n₂, hn₂⟩ := h₂ (ε / 2) (by simpa)
  use (max n₁ n₂)
  intro m hmn
  have hlt₁ : |a₁ m - x₁| < ε / 2 := by
    apply hn₁
    exact le_of_max_le_left hmn
  have hlt₂ : |a₂ m - x₂| < ε / 2 := by
    apply hn₂
    exact le_of_max_le_right hmn
  calc
    |a₁ m + a₂ m - (x₁ + x₂)| = |(a₁ m - x₁) + (a₂ m - x₂)| := by abel_nf
                            _ ≤ |a₁ m - x₁| + |a₂ m - x₂| := abs_add _ _
                            _ < ε / 2 + ε / 2 := add_lt_add hlt₁ hlt₂
                            _ = ε := by ring

end ConvergesTo
```

Definition of a bounded sequence.

```lean
def IsBounded (a : ℕ → ℝ) : Prop :=
  ∃ (C : ℝ), ∀ (n : ℕ), |a n| ≤ C

namespace IsBounded
```

The definition of `IsBounded` unwrapped.

```lean
theorem iff (a : ℕ → ℝ) : IsBounded a ↔ ∃ (C : ℝ), ∀ (n : ℕ), |a n| ≤ C := by
  rfl
```

To show that a sequence is bounded, it suffices to show it is bounded starting
from some `n`.

```lean
theorem iff' (a : ℕ → ℝ) : IsBounded a ↔
    ∃ (C : ℝ), ∃ (n : ℕ), ∀ m ≥ n, |a m| ≤ C := by
  constructor
  · intro ⟨C, hC⟩
    use C
    use 0
    intro m _
    exact hC m
  · intro ⟨C, n, hn⟩
    rw [iff]
    let s : Finset ℕ := Finset.range (n + 1)
    use C + s.sup' ⟨0, by simp [s]⟩ (fun k ↦ |a k|)
    intro m
    by_cases h : n ≤ m
    · trans
      · exact hn m h
      · simp only [le_add_iff_nonneg_right, Finset.le_sup'_iff]
        use 0
        simp [s]
    · have hmem : m ∈ s := by simp [s]; omega
      trans
      · exact Finset.le_sup' (fun k ↦ |a k|) hmem
      · have : 0 ≤ C := (abs_nonneg (a n)).trans (hn n (Nat.le_refl n))
        simpa

theorem of_convergesTo (a : ℕ → ℝ) (x : ℝ) (h : ConvergesTo a x) :
    IsBounded a := by
  rw [iff']
  obtain ⟨n, hn⟩ := h 1 Real.zero_lt_one
  use 1 + |x|
  use n
  intro m nm
  calc
    |a m| = |a m - x + x| := by ring_nf
        _ ≤ |a m - x| + |x| := abs_add (a m - x) x
        _ ≤ 1 + |x| := add_le_add_right (le_of_lt (hn m nm)) |x|

end IsBounded

namespace ConvergesTo
```

The product of converging sequences converges to the product of the limits.

Hint for the proof: use that convergent sequences are bounded!

```lean
theorem mul (a₁ a₂ : ℕ → ℝ) (x₁ x₂ : ℝ) (h₁ : ConvergesTo a₁ x₁)
    (h₂ : ConvergesTo a₂ x₂) : ConvergesTo (a₁ * a₂) (x₁ * x₂) := by
```

The sandwich lemma: Given three sequences `a`, `b` and `c` such that
`a n ≤ b n ≤ c n` for all `n : ℕ` and both `a` and `c` converge to `x : ℝ`. Then also
`b` converges to `x`.

```lean
theorem sandwich (a b c : ℕ → ℝ) (h : ∀ n, a n ≤ b n ∧ b n ≤ c n) (x : ℝ)
    (ha : ConvergesTo a x) (hb : ConvergesTo c x) : ConvergesTo b x := by
  intro ε hε
  obtain ⟨n₁, hn₁⟩ := ha ε hε
  obtain ⟨n₂, hn₂⟩ := hb ε hε
  let N := max n₁ n₂
  use N
  intro m hmn
  have hn₁n : n₁ ≤ N := le_max_left n₁ n₂
  have hn₂n : n₂ ≤ N := le_max_right n₁ n₂

  have hmn₁ : n₁ ≤ m := le_trans hn₁n hmn
  have hmn₂ : n₂ ≤ m := le_trans hn₂n hmn

  have h₁ : |a m - x| < ε := hn₁ m hmn₁
  have h₂ : |c m - x| < ε := hn₂ m hmn₂

  have h₃ : a m ≤ b m := (h m).left
  have h₄ : b m ≤ c m := (h m).right

  rw [abs_sub_lt_iff] at h₁ h₂
  rw [abs_sub_lt_iff]
  rcases h₁ with ⟨_, h₁r⟩
  rcases h₂ with ⟨h₂l, _⟩
  constructor
  · linarith
  · linarith


end ConvergesTo
```

To reference the sandwich lemma, use the term `ConvergesTo.sandwich`, which is a function.

```lean
#check @ConvergesTo.sandwich
```

For convenience, we define the `n`-th root of `x : ℝ`.

```lean
noncomputable def Nat.root (n : ℕ) (x : ℝ) : ℝ := Real.rpow x (1 / n)
```

The `n`-th root of `n` to the power of `n` is `n`.

```lean
lemma nthRoot_pow (n : ℕ) (h : n ≥ 1) : (n.root n) ^ n = n := by
  simp [Nat.root]
  convert_to Real.rpow (Real.rpow n (1 / n)) n = n
  · simp
  · simp only [Real.rpow_eq_pow]
    rw [← Real.rpow_mul (Nat.cast_nonneg n)]
    field_simp
```

The sequence of the `n`-th root of `n` converges to `1`.

```lean
example : ConvergesTo (fun n ↦ n.root n) 1 := sorry
```
