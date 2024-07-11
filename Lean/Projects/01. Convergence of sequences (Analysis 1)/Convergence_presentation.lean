/-
# Convergence of sequences

By Judith Ludwig, Christian Merten and Florent Schaffhauser,
Proseminar on computer-assisted mathematics,
Heidelberg, Summer Semester 2024

In this project, we show basic properties of convergent sequences. The goal is to show that the sequence of the `n`-th root of `n` converges to one.
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-
Definition of a convergent sequence `a : ℕ → ℝ`.
-/

def ConvergesTo (a : ℕ → ℝ) (x : ℝ) : Prop :=
  ∀ ε > 0, ∃ (n : ℕ), ∀ m ≥ n, |a m - x| < ε

namespace ConvergesTo

/-
The definition of `ConvergesTo` unwrapped.
-/

lemma iff (a : ℕ → ℝ) (x : ℝ) :
    ConvergesTo a x ↔ ∀ ε > 0, ∃ (n : ℕ), ∀ m ≥ n, |a m - x| < ε := by
  rfl

/-
In the definition of `ConvergesTo`, we may replace the condition `< ε` by `≤ ε`.
-/

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

/-
Constant sequences converge to the constant value.
-/

theorem of_constant (x : ℝ) : ConvergesTo (fun _ ↦ x) x := by sorry

/-
The sandwich lemma: Given three sequences `a`, `b` and `c` such that
`a n ≤ b n ≤ c n` for all `n : ℕ` and both `a` and `c` converge to `x : ℝ`. Then also
`b` converges to `x`.
-/

theorem sandwich (a b c : ℕ → ℝ) (h : ∃ (n : ℕ), ∀ m ≥ n , a m ≤ b m ∧ b m ≤ c m) (x : ℝ)
    (ha : ConvergesTo a x) (hb : ConvergesTo c x) : ConvergesTo b x := by sorry

end ConvergesTo

/-
To reference the sandwich lemma, use the term `ConvergesTo.sandwich`, which is a function.
-/

#check @ConvergesTo.sandwich

/-
For convenience, we define the `n`-th root of `x : ℝ`.
-/

noncomputable def Nat.root (n : ℕ) (x : ℝ) : ℝ := Real.rpow x (1 / n)

-------------------------------------------------------------------

/-
The sequence of the `n`-th root of `n` converges to `1`.
-/

-------------------------------------------------------------------

/-
Here we show necessary properties involving type casting
-/

lemma Nat_eq_Real (n : ℕ) (h : 1 ≤ n) : ((n * (n - 1)) / 2 : ℕ) = (n * (n - 1 : ℝ)) / 2 := by
      rw [Nat.cast_div]
      · simp
        rw [Nat.cast_sub]
        simp
        exact h
      · have := Nat.even_mul_pred_self n
        rw [even_iff_exists_two_nsmul] at this
        simp at this
        obtain ⟨c, hc⟩ := this
        use c
      · simp

/-
Here we show necessary properties involving the `n`-th root of `n`
-/

-------------------------------------------------------------------

/-
The `n`-th root of `n` to the power of `n` is `n`.
-/

lemma nthRoot_pow (n : ℕ) (h : n ≥ 1) : (n.root n) ^ n = n := by sorry

/-
One is less or equal to the `n`-th root of `n`
-/

lemma one_le_nrootn (n : ℕ) (h : 1 ≤ n) : 1 ≤ n.root n := by sorry

-------------------------------------------------------------------

/-
We define the auxilliary sequence `d n := n.root n - 1` and
show necessary properties
-/

noncomputable def d (n : ℕ) : ℝ := n.root n - 1

/-
Using the binomial theorem we can show the following inwquality
-/

lemma dn_ge_binomial (n : ℕ) (hn : n ≥ 2) : (d n + 1) ^ n ≥ (n * (n - 1 : ℝ)) / 2 * (d n) ^ 2 := by
      rw [add_pow]
      simp
      calc
        _ ≥ d n ^ 2 * Nat.choose n 2 := by
            show _ ≤ _
            apply Finset.single_le_sum (f := fun k ↦ d n ^ k * n.choose k)
            · intro i _
              have h1 : 0 ≤ d n ^ i := by
                apply pow_nonneg
                simp[d]
                apply one_le_nrootn
                linarith
              have h2 : 0 ≤ (n.choose i : ℝ) := by
                simp
              exact Left.mul_nonneg h1 h2
            · simp
              exact Nat.succ_lt_succ hn
        _ = (n * (n - 1 : ℝ)) / 2 * (d n) ^ 2 := by
          rw [Nat.choose_two_right]
          rw [mul_comm]
          rw [Nat_eq_Real n]
          exact Nat.one_le_of_lt hn

/-
Following from the previously shown, we can derive the inequality for `n`
-/

lemma n_ge_binomial (n : ℕ) (hn : n ≥ 2) : n ≥ (n * (n - 1 : ℝ)) / 2 * (d n) ^ 2 := by sorry

/-
Finally this leads to the following inequality for the sequence `d n`
-/

lemma dn_le_sqrt (n : ℕ) (h : n ≥ 2) : (d n) ≤ Real.sqrt (2 / (n - 1 : ℝ)) := by sorry

-------------------------------------------------------------------

/-
Start of the Proof
-/

example : ConvergesTo (fun n ↦ n.root n) 1 := by

  have prop_an (n : ℕ) (h : 1 ≤ n) : 1 ≤ n.root n := by apply one_le_nrootn n h

  have prop_cn (n : ℕ) (h : n ≥ 2) : n.root n ≤ 1 + Real.sqrt (2 / (n - 1)) := by
    calc
      n.root n = d n + 1 := by simp [d]
             _ ≤ 1 + Real.sqrt (2 / (n-1)) := by
                rw[add_comm]
                rw[add_le_add_iff_left]
                exact dn_le_sqrt n h

  have prop_sandwich : ∃ (n : ℕ), ∀ m ≥ n, 1 ≤ m.root m ∧ m.root m ≤ 1 + Real.sqrt (2 / (m - 1)) := by
    use 2
    intro m hm
    constructor
    · apply prop_an m; linarith
    · apply prop_cn m; linarith

  have conv_an : ConvergesTo (fun _ ↦ 1) 1 := by apply ConvergesTo.of_constant

  have conv_cn : ConvergesTo (fun n ↦ 1 + Real.sqrt (2 / (n - 1))) 1 := by sorry

  exact ConvergesTo.sandwich (fun _ ↦ 1) (fun n ↦ n.root n) (fun n ↦ 1 + Real.sqrt (2 / (n - 1))) prop_sandwich 1 conv_an conv_cn
