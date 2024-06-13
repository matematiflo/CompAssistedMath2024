/-
# Constructive and classical logic in Lean

By Judith Ludwig and Florent Schaffhauser,
Proseminar on computer-assisted mathematics,
Heidelberg, Summer Semester 2024

In this assignement, you are asked to complete as many exercises as possible by filling in the `sorries` that we have left here and there. Submit your work via GitHub Classroom **before Friday 14.06 at 23:59 PM**.

The assignment will be graded as handed-in/not-handed-in only (no numerical grade). It is here mainly to help you make progress in your understanding of how Lean works, and in order for you to get some feedback. In case you have some sorries left, please submit the assignement nevertheless.
-/

variable {P Q R : Prop}

/-
## Basic tautologies in constructive logic

A tautology is a proposition with parameters that has a proof regardless of whether its paramters have a proof. For instance, the proposition `P → P` is a tautology, because the identity function `fun p => p`  is a proof of `P → P`. In tactic mode, you can prove this using `by {intro p; exact p}`.

We prove below a few basic tautologies, using only *constructive logic* (no law of excluded middle (LEM), which also rules out the axiom of choice, by [Diaconescu's theorem](https://en.wikipedia.org/wiki/Diaconescu%27s_theorem)). Note that we are not saying that the LEM is not true, we are just not using it.

### Exercise 1

Let `P` and `Q` be propositions. Prove that the propositions `P ∧ Q` and `Q and P` are equivalent.
-/

theorem symmAnd (P Q : Prop) : P ∧ Q ↔ Q ∧ P := by
  sorry

/-
### Exercise 2

Let `P`, `Q` and `R` be propositions. The goal of this exercise is to understand how a proposition of the form `P ∨ Q` can imply a proposition `R`. In other words, we want to determine all functions *out* of the inductive type `P ∨ Q`.

1. Show that, to a function `u : (P ∨ Q) → R`, one can associate functions `v : P → R` and `w : Q → R` (see below for the formal version of that statement).
2. Conversely, show that, given functions `v : P → R` and `w : Q → R`, we can define a function `u : (P ∨ Q) → R`.
3. Conclude from the previous two points that `((P ∨ Q) → R) ↔ ((P → R) ∧ (Q → R))`.
-/

theorem Exercise2_1 : ((P ∨ Q) → R) → ((P → R) ∧ (Q → R)) := by
  intro u
  sorry

theorem Exercise2_2 : ((P → R) ∧ (Q → R)) → ((P ∨ Q) → R) := by
  sorry

theorem Exercise2_3 : ((P ∨ Q) → R) ↔ ((P → R) ∧ (Q → R)) := by
  constructor
  · exact Exercise2_1
  · sorry

/-
### Exercise 3

Prove that `∧` distributes over `∨`, in the sense that `P ∧ (Q ∨ R)` is equivalent to `(P ∧ Q) ∨ (P ∧ R)`.
-/

theorem distribAndOr : P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) := by
  constructor
  · intro t
    rcases t with ⟨p, s⟩
    rcases s with q | r
    · left;  exact ⟨p, q⟩
    · sorry
  · intro t
    -- try it first with `rcases` (3 sorries left)
    rcases t with hpq | hpr
    · constructor
      · exact hpq.1
      · left; sorry
    · constructor
      · sorry
      · sorry
    -- alternately, you can comment what you have just done and uncomment what follows to fill the sorries
    -- constructor
    -- · rcases t with hpq | hqr
    --   · exact hpq.1
    --   · sorry
    -- · rcases t with hpq | hqr
    --   · right; sorry
    --   · sorry

/-
## Falsity and negation

The proposition `False` is defined inductively as a proposition with no constructor. So, by definition, it does not admit any proof (we cannot introduce terms of type `False`). This proposition is then used to define a `Not` or `Negation` operator on propositions. More precisely, the proposition `¬P` (read `Not P` and obtained by typing `\not` to get the symbol `¬`) is *defined* as the implication `P → False`.

The next few exercises are destined to develop your intuition on `¬`.

### Exercise 4

Prove that if `P → Q`, then `¬Q → ¬P`. In the formal statement below, follow the proof state step by step. Once you have understood what is going one, close the goal.
-/

theorem contrapose : (P → Q) → (¬Q → ¬P) := by
  intro f
  intro g
  dsimp [Not] at g -- this will unfold the definition of `¬` for the term `g`
  dsimp [Not]      -- this will unfold the definition of `¬` in the goal
  -- Since the goal is an implication `P → False`, the following tactic makes sense
  intro p
  -- now you should treat `False` just like any other proposition and close the goal by constructing a term of type `False`
  sorry

/-
### Exercise 5

1. State and prove the fact that `P → ¬¬P`.
2. In general, it is not constructively true that `¬¬P → P`. However, if `P` is itself a negation, say `P ↔ ¬Q`, then this is true. Show this as an application of Point 1.

-/

example : ¬¬(¬Q) → (¬Q) := by
  intro f
  dsimp [Not] at f
  dsimp [Not]
  intro q
  -- the next result should have been proven in Point 1, otherwise you can accept it
  have t : Q → ¬¬Q := by
    sorry
  dsimp [Not] at t
  sorry

/-
### Exercise 6

As you may know, from `False`, anything follows... but how can we prove this?
-/

theorem exFalsoQuodLibet : False → P := by
  intro h
  -- To conclude, recall that `False` is an inductive type, and that in order to define a function out of an inductive type, we should proceed by case analysis. Which tactic can you use?
  sorry

/-
### Exercise 7

In this exercise, we show that if we can prove `P ∧ ¬P`, then we can prove anything.

1. Prove that there is a function `(¬P ∧ P) → False`.
2. Deduce from the above and theorem `exFalsoQuodLibet` that `(¬P ∧ P) → Q`.
-/

theorem weakContra : (¬P ∧ P) → False := by
  sorry

theorem strongContra : (¬P ∧ P) → Q := by
  sorry

/-
### Exercise 8

We prove the first [De Morgan's law](https://en.wikipedia.org/wiki/De_Morgan%27s_laws#Negation_of_a_disjunction): `¬(P ∨ Q)` is equivalent to `¬P ∧ ¬Q`.
-/

theorem DeMorgan1 : ¬(P ∨ Q) ↔ ¬P ∧ ¬Q := by
  constructor
  · intro f
    -- dsimp [Not] at f
    constructor
    · dsimp[Not]; sorry
    · sorry
  · intro ⟨g, h⟩
    -- dsimp [Not]
    intro t
    -- dsimp [Not] at g h
    rcases t with p | q
    · sorry
    · sorry

/-
## Classical logic

### Exercise 9

If we want to prove results such as `¬¬P → P` or `(¬Q → ¬P) → (P → Q)`, we need to use the [law of excluded middle](https://en.wikipedia.org/wiki/Law_of_excluded_middle), which is the assertion that, for all proposition `P`, the proposition `P ∨ ¬P` has a proof. The LEM can either be taken as an axiom or obtained as a consequence of the axiom of choice (this is [Diaconescu's theorem](https://en.wikipedia.org/wiki/Diaconescu%27s_theorem)).

In Lean, the LEM is a theorem and it is declared as `Classical.em`, where `em` stands for excluded middle. To apply it, we can use the `by_cases` tactic. The precise syntax for the tactic is `by_cases p : P`, which then creates two sub-cases for the proof of a given goal, one with a term `p : P` in the local context, and the other one with a term `p : ¬P` in the local context. Equivalently, we can use ` rcases Classical.em P with p | p`.

As an application, prove the following results:

1. `¬¬P → P`
2. `(¬Q → ¬P) → (P → Q)`
3. `(P → Q) ↔ (¬P ∨ Q)`.

In 3, which of the two implications does *not* use the LEM?
-/

#check Classical.em  -- Classical.em (p : Prop) : p ∨ ¬p

theorem doubleNegation : ¬(¬P) → P := by
  intro f
  dsimp [Not] at f
  -- rcases Classical.em P with p | p
  by_cases p : P
  · exact p
  · exfalso; exact f p

example : ¬¬P → P := by
  intro f
  by_cases p : P
  · sorry
  · sorry

example : (¬Q → ¬P) → (P → Q) := by
  intro f p
  by_cases q : Q
  · sorry
  · sorry

example : (P → Q) ↔ (¬P ∨ Q) := by
  sorry

/-
### Exercise 10

As a final exercise, prove [De Morgan's second law](https://en.m.wikipedia.org/wiki/De_Morgan%27s_laws#Negation_of_a_conjunction): `¬(P ∧ Q) ↔ ¬P ∨ ¬Q`.
-/

theorem DeMorgan2 (P Q : Prop) : ¬(P ∧ Q) ↔ ¬P ∨ ¬Q := by
  sorry
