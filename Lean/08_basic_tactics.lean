/-
# Basic tactics

By Judith Ludwig and Florent Schaffhauser,
Proseminar on computer-assisted mathematics,
Heidelberg, Summer Semester 2024

In order to write a proof, we can use Lean's tactic mode to assist us. To do so, we enter tactic mode using the keyword `by`. It is recommended to go to the next line after a `by` command, and to indent that line.

You can also use curly brackets `{ }` right after a `by` command. If you go to the next line after opening brackets, that line will be automatically indented in VS Code. If you stay on the same line, you can separate tactics by a semi-colon sign `;`.
-/

import Mathlib.Tactic.Cases

/-
In this file, we introduce the following basic tactics:

- `exact`
- `apply`
- `intro`
- `revert`
- `constructor`
- `rcases`
- `left` and `right`
- `rfl`
- `exists`
- `induction`

In the examples below, we often work with propositions `P Q R S : Prop`, so our functions between propositions will be thought of as logical implications.

## The `exact` tactic

The `exact` tactic is the one to use when we want to close the goal by entering a term of the required type.

For instance, if the goal is a type `P` and we have a term `p : P` in our local context, then `exact p` will close the goal. More generally, we can use `exact` followed by a more complicated expression, for instance a term of the form `f p`, where `f` is a function that is applied to `p`.
-/

def modus_ponens {P Q : Prop} (f : P → Q) (p : P) : Q := by
  exact f p

/-
The term after `exact` can be a function itself, between arbitrary propositions.
-/

example {P Q : Prop} (f : P → Q) : (P → Q) := by
  sorry

example {P Q R S : Prop} (f : P ∧ Q → R ∨ S) (h : P ∧ Q) : R ∨ S := by
  sorry

/-
## The `apply` tactic

If we have a type `Q` as a goal and a function `f : P → Q` in our local context, we can construct terms of type `Q` by applying the function `f`. In that situation, the `apply` tactic, used with `f`, will transform the goal `Q` into `P`. We can then try to find terms of type `P` in our local context and close the goal with the `exact` tactic.
-/

def modus_ponens' {P Q : Prop}  (f : P → Q) (p : P) : Q := by
  apply f
  exact p

/-
We can do this several times in a row to transform the goal and reduce it to something that is already proved in our local context.
-/

example {P Q R S : Prop} (p : P) (f : P → Q) (g : Q → R) (h : R → S) : S := by
  apply h
  sorry

/-
## The `intro` tactic

If our goal is of the form `P → Q`, it means that we want to define a function from `P` to `Q`. In that situation, it can be useful to fix a `p : P` and then introduce what `f p` would be. The `intro` tactic enables us to do that.

For instance, if we want to define a term `f : Nat → Nat` we can consider the function `n ↦ n ^ 2`, which can be defined as follows.
-/

def square : Nat → Nat := by
  -- exact fun n => n ^ 2
  intro n
  exact n ^ 2

/-
However, whether this is the best solution may depend on the precise situation at hand. To understand the following example, recall that a curried function `f : P → Q → R` takes a term `p : P`  and returns a a function `f p : Q → R`.
-/

example {P Q R : Prop} (f : P → Q → R) (p : P) : Q → R := by
  -- exact f p
  intro q
  exact f p q

/-
## The `revert` tactic

The `revert` tatctic acts as a converse to `intro`, in the sense that we have `p : P` in our local context and `Q` as a goal, then `revert p` will transform this goal into `P → Q`.
-/

def modus_ponens'' {P Q : Prop} (f : P → Q) (p : P) : Q := by
  revert p
  exact f

example {P Q R : Prop} (f : P → Q → R) (p : P) : Q → R := by
  revert p
  sorry

example {P Q R : Prop} (f : P → Q → R) (q : Q) : P → R := by
  intro p
  revert q
  sorry

/-
## The `constructor` tactic

When your goal is a *structure* (for instance `P ∧ Q`), in order to close the goal you need to introduce a term for each *field* of the structure (for instance a term of type `P` and a term of type `Q` if your structure is `P ∧ Q`). This can be achieved by using the tactic `constructor`, which replaces the structure in the goal by as many subgoals as there are fields in that structure.

To get more information about a given structure, you can use the `#print` command.
-/

#print And

/-
```lean
structure And : Prop → Prop → Prop
number of parameters: 2
constructor:
And.intro : ∀ {a b : Prop}, a → b → a ∧ b
fields:
left : a
right : b
```

It is recommended, after applying the tactic `constructor`, to separate each subgoal by a dot of the form `·` (obtained by typing `\.`) and  indent the lines consistenly under each dot).
-/

example {P Q : Prop} (p : P) (q : Q) : P ∧ Q := by
  constructor
  · exact p
  · sorry

example {P Q : Prop} : P → Q → P ∧ Q := by
  -- can you use `constructor` to solve this?
  sorry

/-
Propositional equivalence `P ↔ Q` is another example of a type (a proposition, in this case) which is defined as a structure. The constructor is named `Iff.intro` and it takes two parameters: one called called `mp` which is a proof of `P → Q`, and one called `mpr` which is a proof of `Q → P`.
-/

#print Iff

/-
```lean
structure Iff : Prop → Prop → Prop
number of parameters: 2
constructor:
Iff.intro : ∀ {a b : Prop}, (a → b) → (b → a) → (a ↔ b)
fields:
mp : a → b
mpr : b → a
````

This means two things:

- Terms of type `P ↔ Q` are introduced as terms of the form `Iff.intro mp mpr`.
- If `h` is a term of type `P ↔ Q`, it projects to two terms `h.mp : P → Q` and `h.mpr : Q → P`.

So, as a structure, `P ↔ Q` (which is notation for `Iff P Q`) has fields `mp : P → Q` and `mpr : Q → P`. Therefore, if the `constructor` tactic is applied to a goal of the form `P ↔ Q`, it will produce two subgoals, one called `mp` and one called `mpr`.
-/

example {P Q : Prop} (hPQ : P → Q) (hQP : Q → P): P ↔ Q := by
  constructor
  · sorry
  · sorry

/-
If one knows the name of the (unique) constructor of a structure, one can also replace the `constructor` tactic by `apply constructor_name`, possibly with `?term` or `_` as parameters. For the structure `P ∧ Q` (which is notation for `And P Q`), the name of the constructor is `And.intro`.
-/

example {P Q : Prop} (hPQ : P → Q) (hQP : Q → P): P ↔ Q := by
  apply Iff.intro ?direct_implication ?converse_implication
  · sorry
  · sorry

example {P Q : Prop} (p: P) (q : Q) : P ∧ Q := by
  apply And.intro
  · sorry
  · sorry

/-
## The `rcases` tactic

The `rcases` tactic can be used in a variety of situations.

If you have a *structure* (for instance `P ∧ Q`) in your local context, then you can *destruct* any term of type that structure into a collection of terms, one for each field in your structure (for instance a term of type `P` and a term of type `Q` if you start with a term of type `P ∧ Q`). More precisely, this can be achieved using the tactic `rcases t` where `t` is a term of type `S` and `S` is a structure.

To be able to access the terms thus introduced in the local context (one for each field of the structure), the full syntax should be `rcases t with ⟨t1, t2, ...⟩`. For instance, a term `t : P ∧ Q` is, by definition, of the form `⟨p, q⟩` where `p : P` and `q : Q` (more precisely, `t` is of the form `And.intro p q`, where `And.intro` is the unique constructor of the structure `And`, also denoted `∧`). The command `rcases t with ⟨p, q⟩` will extract `p` and `q` out of `t` (and `t` will disappear from the local context after this).
-/

example {P Q : Prop} : P ∧ Q → P := by
  intro t
  rcases t -- with ⟨p, q⟩
  sorry

/-
One can also use the `cases` tactic, but the syntax is a little different.
-/

example {P Q : Prop} : P ∧ Q → P := by
  intro t
  cases t with
  | intro p q => sorry

/-
Sometimes, the `rcases` tactic can dig into structures recursively. But some other times, a little care is required.
-/

example {P Q R : Prop} : P ∧ Q ∧ R → Q ∧ P ∧ R := by
  intro t
  rcases t with ⟨p, q, r⟩
  sorry

example {P Q R : Prop} : (P ∧ Q) ∧ R → Q ∧ P ∧ R := by
  intro t
  rcases t -- with ⟨p, q, r⟩
  sorry

/-
The `rcases` tactic also works with inductive types that have various contructors. Take for instance a term `t : P ∨ Q`. Then `t` is either of  the form `Or.inl p` or of the form `Or.inr q`, where `Or.inl` and `Or.inr` are the two constructors of the inductive type `Or P Q`, also denoted by `P ∨ Q`. The command `rcases t with p | q` will extract `p` and `q` out of `t` (and `t` will disappear from the local context after this). Note that the syntax is different from the cases of a structure, for which it was `rcases t with ⟨p, q⟩`.
-/

#print Or

/-
inductive Or : Prop → Prop → Prop
number of parameters: 2
constructors:
Or.inl : ∀ {a b : Prop}, a → a ∨ b
Or.inr : ∀ {a b : Prop}, b → a ∨ b
-/

example {P Q : Prop} : P ∨ (P ∧ Q) → P := by
  intro t
  rcases t with p | t'
  · exact p
  · exact t'.1  -- note the use of Lean's pre-implemented projection to the first field of a structure (you can also use `t'.left', because that field is called `left`)

/-
> **Observation.** When used with a structure, the `rcases` tactic produces *one* local context (with each one of the terms corresponding to the fields of the structure), while when used with an inductive type with various constructors, it produces various *different* local contexts, one for each constructor of the inductive type.

Again here we could use `cases` instead of `rcases`, but the syntax would be a little different.
-/

example {P Q : Prop} : P ∨ (P ∧ Q) → P := by
  intro t
  cases t with
  | inl p  => exact p
  | inr t' => exact t'.left

/-
We can use this to define a function that returns the length of a list. Indeed a list is either empty (the corresponding constructor is `List.nil` and it takes no parameters), or of the form `a :: l`, where `a` is a term of type `X` and `l` is a list of type `X` (the corresponding constructor is `List.cons` and it takes two parameters, `a` and `l`).
-/

#check (1 :: [2, 3])  -- [1, 2, 3] : List Nat

def List.length' {X : Type} : List X → Nat := by
intro L
rcases L with empty_list | ⟨a, l⟩
· exact 0
· exact 1 + List.length' l

/-
## The `left` and `right` tactics

When we have an inductive type with various constructors *as a goal*, we have multiple possibilities to try and close that goal (as many possibilities as there are constructors).

For instance, if we want to prove `P ∨ Q`, it suffices to prove either `P` or `Q`. If we want to prove `P`, say, we indicate this to Lean using the tactic `left`. Alternately, we could use `apply Or.inl`, to indicate which constructor we want to use to close the goal.
-/

example {P Q : Prop} : P → P ∨ Q := by
  intro p
  left
  exact p

def swap {P Q : Prop} : P ∨ Q → Q ∨ P:= by
  intro h
  rcases h with p | q
  · apply Or.inr; exact p
  · sorry

example {P Q R : Prop} : P ∧ (Q ∨ R) → (P ∧ Q) ∨ (P ∧ R) := by
  intro t
  rcases t with ⟨p, t'⟩
  sorry

example {P Q R : Prop} : (P ∧ Q) ∨ (P ∧ R) → P ∧ (Q ∨ R) := by
  sorry

/-
## The `rfl` tactic

In the type theory used by Lean, equality is an inductive type. Its only contructor is `Eq.refl` which takes one parameter. More precisely, `Eq.refl x` is by definition a proof of `x = x`.

This means that if we want to prove an equality `x1 = x2`, the first thing we should think of trying is `exact Eq.refl x`, where `x` is something that is *definitionally equal* to both `x1` and `x2` (this means that `x1` and `x2` both reduce to `x` in Lean's compiler).
-/

example : 1 + (1 + 1) = 4 - 1  := by
  exact Eq.refl 3

/-
Alternately, we can use `apply Eq.refl`, or even just `rfl`, which do not require a parameter. Using `rfl` instead of `apply Eq.refl` is similar to using `left` instead or `apply Or.inl`: in both cases, we want to enter terms of a certain inductive type, so we use `apply constructor_name`, and `refl` or `left` are just abbreviations for that.
-/

example : 1 + (1 + 1) = 4 - 1  := by
  apply Eq.refl

example : 1 + (1 + 1) = 4 - 1  := by
  rfl

/-
Note that, in the case of `apply Eq.refl`, there is only one parameter that could go after this expression, so either the goal is closed or an error message is returned, while if we use something like `apply Or.inl` to prove `P ∨ Q`, we still have to prove `P` to close the goal.

As a test, you can check that the parameter of `exact Eq.refl` can be left implicit (using a placeholder `_`).
-/

example : 1 + (1 + 1) = 4 - 1  := by
  exact Eq.refl _

/-
## The `exists` tactic

The case of an existential statement is similar to the `apply Or.inl` and `apply Eq.refl` situations that we have encountered before. A goal of the form `∃ n : Nat, 42 = 2 * n` is again an inductive type (or inductively defined proposition). Its only constructor is `Exists.intro`, which takes two parameters: a natural number `n` and a proof that `42 = 2 * n`.
-/

example : ∃ n : Nat, 42 = 2 * n := by
  apply Exists.intro 21
  exact Eq.refl _

/-
As we have said, terms of type `∃ n : Nat, 42 = 2 * n` are pairs of the form `⟨n, hn⟩` where `n` is a natural number and `hn` is a proof of the proposition `42 = 2 * n`. Such pairs are called *dependent pairs* (because the type of the second term `hn` depends on the term `n`). This is sometimes convenient to use as concise notation.
-/

example : ∃ n : Nat, 42 = 2 * n := by
  -- exact Exists.intro 21 (Eq.refl 42)
  exact ⟨21, Eq.refl 42⟩

/-
The type of dependent pairs `∃ n : Nat, 42 = 2 * n` can also be denoted by `(n : Nat) ×' (42 = 2 * n)`. Do not forget the `'` after the `×`, or this will not typecheck!
-/

#check (n : Nat) ×' (42 = 2 * n)  -- (n : Nat) ×' 42 = 2 * n : Type

/-
If we use the `exists` tactic instead of `apply Exists.intro`, Lean will try to close the goal automatically and will sometimes succeed. If you import `Mathlib.Tactic.Use`, you can also use the `use` tactic instead of `exists`.
-/

example : ∃ n : Nat, 42 = 2 * n := by
  exists 21  -- use 21

/-
## The `induction` tactic

The `induction` tactic can be used with *any* inductive type present in the local context. When used with the natural numbers, it behaves in a familiar way, distinguishing the cases `zero` and `succ n`. In general, it will distinguish cases according to the possible constructors of an inductive type, introducing an induction hypothesis where approrpiate. Note that the `induction` tactic is used on a *term*: if we have a term `t : I` in our local context, where `I` is an inductive type, then the syntax to start a proof by induction is `induction t`.

In the first example below, we use tactics that have not been introduced yet, namely `rfl` and `rewrite` (or its variant `rw` which tries to close the goal after rewriting). In the second example, we use Lean's `List.length` function, which is defined as the `List.length'` function we declared earlier, to prove that the length of a concatenated list `L1 ++ L2`  is equal to `L1.length + L2.length`.
-/

theorem zero_add (n : Nat) : 0 + n = n := by
  induction n with
  | zero      => rfl
  | succ n ih => rewrite [← Nat.add_assoc, ih]; rfl

theorem length_add {X : Type} (L1 L2 : List X) : (L1 ++ L2).length = L1.length + L2.length := by
  induction L1 with
  | nil         => simp only [List.nil_append, List.length_nil, Nat.zero_add]
  | cons a l ih => sorry -- try and solve this using `simp?` If it fails, try to incorporate the induction hypothesis `ih` in an appropriate manner.

/-
If you import `Mathlib.Tactic.Cases`, you will have access to an `induction'` tactic, which has a slightly lighter syntax than `induction`.
-/

theorem zero_add' (n : Nat) : 0 + n = n := by
  induction' n with n ih
  · sorry
  · sorry

theorem length_add' {X : Type} (L1 L2 : List X) : (L1 ++ L2).length = L1.length + L2.length := by
  induction' L1 with a l ih
  · sorry
  · sorry

/-
Since equality is inductively defined, you can use induction to prove certain properties of equality. Note that here the induction applies to the term `h : x = y` (the equality `x = y` is *an inductively defined proposition*, just as `Nat` is an inductively defined type). Upon using the tactic `induction h`, every occurence of `y` *in the goal and in the local context* will be replaced by an `x`.
-/

def Eq.symm' {X : Type} (x y : X) : x = y → y = x := by
  intro h
  induction h
  rfl

def Eq.trans' {X : Type} (x y z : X) : x = y ∧ y = z → x = z := by
  intro h
  rcases h with ⟨h1, h2⟩
  sorry  -- try to remove this `sorry` by using either `induction` or `rewrite`

/-
The `rewrite` tactic that we have already encountered is based on the following substitution properties, which are all proved by induction.
-/

example {X : Type} {P : X → Prop} {x y : X} : x = y → (P x ↔ P y) := by
  intro h
  induction h
  rfl  -- note that `rfl` enables you to prove, for all `P : Prop`, that `P ↔ P` (you do not need `P = P` here)

def congrArg' {X Y : Type} {x y : X} (f : X → Y) : x = y → f x = f y := by
 sorry

/-
As a challenge to conclude this introduction to Lean's basic tactics, see if you can prove the following theorem, whicg characterizes the inductively-defined equality in terms of the so-called *indiscernibility of identicals*. This means that `x` and `y` are equal as terms of type `X` if and only if for all predicate `P : X → Prop`, the proposition `P x` is equivalent to the proposition `P y`.
-/

theorem MLE {X : Type} (x y : X): x = y ↔ ∀ P : X → Prop, P x ↔ P y := by
  constructor
  · intro h P
    sorry
  · intro h
    have Q := h (fun (y : X) => x = y)
    sorry

/-
For the sake of completeness, here is the inductive definition of equality and a proof that `1 + 1 = 2` in `Nat`.
-/

inductive Eq' {X : Type} : X → X → Prop
| refl (x : X) : Eq' x x

#check Eq'       -- Eq' {X : Type} : X → X → Prop
#check Eq'.refl  -- Eq'.refl {X : Type} (x : X) : Eq' x x
#check Eq' 1 2   -- Eq' 1 2 : Prop

example : Eq' (1 + 1) 2 := by
  exact Eq'.refl _
