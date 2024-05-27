# Introduction to Lean

By Judith Ludwig and Florent Schaffhauser  
Proseminar on Computer-assisted mathematics, Heidelberg  
Summer Semester 2024

Lean is a *programming language* that can be used as a *proof assistant* (also called an *interactive theorem prover*). This means that Lean can be used to check and certify the correctness of certain computer programmes and formalised mathematical proofs.

It was created and first implemented by **Leonardo de Moura** at Microsoft Research, where the first version was launched in 2013. The current version is Lean 4, dating back to 2021. It is not backwards-compatible wih **Lean 3**.

## Goals for today

* Learn to read basic Lean syntax such `def t : T := sorry`.
* Learn to think about *propositions as types* and *terms as proofs*.
* Write simple equality proofs using the `reflexivity` tactic (or `refl`).
* See a first example of a function and of a proof that uses the `exact` tactic.

## Types and terms

The command `#check` tells us the type of an expression, for instance `Char` for a character, `String` for a string of characters, and `Nat` for a natural number.

If `#check t` returns `T`, one says that `t` is a term of type `T`*. This is abbreviated to `t : T`.

```lean
#check 'H'              -- Char.ofNat Char
#check "Hello, world!"  -- "Hello, world! : String"
#check 42               -- 42 : Nat
```

The function `String.append` takes two string of characters and concatenates them. The notation `+` can be used to mean the sum of two natural numbers.

```lean
#check @String.append             -- String.append : String → String → String
#check "Hello, ".append "world!"  -- String.append "Hello, " "world!" : String
#check 41 + 1                     -- 41 + 1 : Nat
```

The data types `string` and `Nat` are themselves terms, of type `Type`.

```lean
#check String  -- String : Type
#check Nat     -- Nat : Type
```

The notation `[ ]` is used to input lists of terms (separated by a comma).

```lean
#check ["Hello, ", "world!"]  -- ["Hello, ", "world!"] : List String
#check [1, 2, 3]              -- [1, 2, 3] : List Nat
```

If `T` is a type, `List T` is the type of lists of terms of type `T`.

```lean
#check List String  -- List String : Type
#check List Nat     -- List Nat : Type
```

Note that we cannot have a list containing terms of different types. Uncomment the following command to see that Lean does not accept it.

```lean
-- #check [1, "a"]
```

A particularly important type for us will be the type `Prop`, which he used to denote the type whose terms are formal statements, *regardless of whether they are true or not*.

```lean
#check 1 + 1 = 2  -- 1 + 1 = 2 : Prop
#check 1 + 1 = 3  -- 1 + 1 = 3 : Prop
```

Note that a formal statement does *not* have to be a mathematical statement. And if it is a mathematical statement, it does not have to be correct.

```lean
#check "Hello, ".append "world!" = "Hello, world!"  -- String.append "Hello, " "world!" = "Hello, world!" : Prop
```

If we typecheck `1 + 1`, Leans returns that it is a natural number but does not convert it to `2`.

```lean
#check 1 + 1   -- 1 + 1 : Nat
```

However, we can *evaluate* certain expressions and see whether the result corresponds to what we think these expressions are.

Not all expressions can be evaluated, though.

```lean
#eval 1 + 1                      -- 2
#eval "Hello, ".append "world!"  -- "Hello, world!"
```

Uncomment the next two lines to see that the proposed terms cannot be evaluated

```lean
-- #eval 1 + 1 = 2
-- #eval "Hello, ".append "world!" = "Hello, world!"
```

If we look at the term `1 + 1 = 2`, which is of type `Prop`, we see that it looks like something that should be *provable* in a formal sense. In fact it is so, and we will soon learn how to write a proof of it.

But first, a word about the syntax. And expression of the form `def t : T`, where `t` is of type `T`, means that that we are about to *define* a term `t` that will be of type `T`.

```lean
def my_first_sentence : String := "Hello, world!"
def my_favourite_integer : Nat := 42

#check my_first_sentence     -- my_first_sentence : String
#check my_favourite_integer  -- my_favourite_integer : Nat


def my_second_sentence : String := "Hello, ".append "world!"
def my_brother_s_favourite_integer : Nat := 41 + 1

#check my_second_sentence              -- my_second_sentence : String
#check my_brother_s_favourite_integer  -- my_brother_s_favourite_integer : Nat
```

Now let us see a particularly important case, in which we define a term of type `P` for `P` a term of type `Prop`.

> If `P` is a term of type `Prop`, then defining a term of type `P` means proving `P`.

As earlier, the actual definition of a term `p : P` comes after the `:=` symbol. So here, what comes after `:=` will be the proof of the proposition `P`. If we do not know what to put after that symbol, we can always write `sorry` and come back to it later.

Seeing a proposition `P` as a type, and terms of type `P` as proofs of `P`, is known as the *Curry-Howard correspondence*.

```lean
-- def one_plus_one_eq_two : 1 + 1 = 2 := sorry
-- #check one_plus_one_eq_two

-- def my_two_sentences_are_the_same : my_first_sentence = my_second_sentence := sorry
-- #check my_two_sentences_are_the_same

-- def my_brother_and_I_agree : my_favourite_integer = my_brother_s_favourite_integer := sorry
-- #check my_brother_and_I_agree
```

It is also possible to declare these as theorems, using the command `theorem`. Let us do it below but in a separate "environment", so there is no conflict and we can use the same name for the `theorem` as we did for the `def`.

We can enter a different environment by using the command `namespace`. The name `playground` is arbitrary. However, we cannot use it more than once in the entire document.

```lean
namespace playground

-- theorem one_plus_one_eq_two : 1 + 1 = 2 := sorry
-- #check one_plus_one_eq_two

-- theorem my_two_sentences_are_the_same : my_first_sentence = my_second_sentence := sorry
-- #check my_two_sentences_are_the_same

-- theorem my_brother_and_I_agree : my_favourite_integer = my_brother_s_favourite_integer := sorry
-- #check my_brother_and_I_agree

end playground
```

Note that Theorems `my_two_sentences_are_the_same` and `my_brother_and_I_agree` can be written in a way that is more similar to Theorem `one_plus_one_eq_two`.

```lean
namespace Spielplatz

-- theorem my_two_sentences_are_the_same : "Hello, world!" = "Hello, ".append("world!") := sorry
-- #check my_two_sentences_are_the_same

-- theorem my_brother_and_I_agree : 42 = 41 + 1 := sorry
-- #check my_brother_and_I_agree

end Spielplatz
```

## Proving equalities

Let us now prove the results stated above. There at least two ways to write these proofs and we will present both.

Note that what all our statement have in common is that they are *equalities*. In Lean, this is a strong requirement: an equality between terms in Lean means that the two terms are *definitionally* equal. It is difficult at this moment to explain what this means, but basically it says that `1 + 1 = 2` holds because the terms `1 + 1` and `2` *reduce to the same term* (in Lean's compiler).

The point is, if you have to prove an equality, you should first try to see if it holds *by definition*. This will indeed be the case for `1 + 1 = 2`.

### First way of writing the proof : tactic mode

Proofs are usually written using the *tactic mode*, which we enter using the `by` keyword.

At the end of the proof, one should get a `No goals` message in the *local context*, visible in the *Infoview* tab (usually located to the right).

The tactic that we use here is called `rfl` (for *reflexivity*).

```lean
def one_plus_one_eq_two : 1 + 1 = 2 := by {
  rfl
}
```

### Exercise 1

Use the `rfl` tactic to prove the results below.

```lean
-- def my_two_sentences_are_the_same : my_first_sentence = my_second_sentence := by {
--   sorry
-- }

-- def my_brother_and_I_agree : my_favourite_integer = my_brother_s_favourite_integer := by {
--   sorry
-- }
```

### Second way of writing the proof: term mode

A tactic proof is mostly useful when we reach a certain level of complexity, which requires that said proof be carried out in various steps (tactic mode is also the way proofs are usually constructed in the daily practice of mathematics).

But in any case, what Lean does is *compile the tactic proof into a proof term*, which becomes accessible via the `#print` command. We can then use that proof term to provide a proof without entering tactic mode, simply by copying the proof term generated via the `#print` command (it will appear in the Infoview* tab if you put the keyboard cursor on the same line as the `#print` command) and pasting it after the `:=` symbol.

We test this out below with the `my_brother_and_I_agree` proposition. Note that, in term mode, Lean does not generates a `No goals` message. If you use a proof term, the only way to know it worked is via the absence of an error message.

```lean
-- #print my_two_sentences_are_the_same

def my_two_sentences_are_the_same : my_first_sentence = my_second_sentence := Eq.refl my_first_sentence

def my_brother_and_I_agree : my_favourite_integer = my_brother_s_favourite_integer := Eq.refl my_favourite_integer
```

### Exercise 2

Use term mode to write a proof of `1 + 1 = 2`. Note that `Eq.refl (1 + 1)` and ` Eq.refl 2` work equally well and check that this is also the case for the definitions of the terms `my_two_sentences_are_the_same` and `my_brother_and_I_agree`.

At this stage, it might be instructive to try out `#check Eq.refl 2` and `#check Eq.refl (1 + 1)`. Or even `#check Eq.refl my_favourite_integer` and `#check Eq.refl my_first_sentence`. See below for the corresponding code and a remark on the content of `Eq.refl 2`.

Try also `#check Eq.refl` and `#check @Eq.refl`. Using `@` should produce something better-looking.

```lean
def one_plus_one_eq_two_again : 1 + 1 = 2 := Eq.refl (1 + 1)
```

The following command `#check Eq.refl 2` returns `Eq.refl 2 : 2 = 2`, which means that `Eq.refl 2` is a term of type `2 = 2`. In other words, `Eq.refl 2` *is a proof of the Proposition* `2 = 2`. This is crucial in understanding how proof assistants work.

```lean
#check Eq.refl 2  -- Eq.refl 2 : 2 = 2

-- #check Eq.refl (1 + 1)
-- #check Eq.refl my_favourite_integer
-- #check Eq.refl my_first_sentence

-- #check Eq.refl
-- #check @Eq.refl
```

To conclude, let us see an example of a case when we do not get what we might expect. If we write to write fractions naively, we see that the types of those terms is not what we think it is.

```lean
#check 42 / 21  -- 42 / 21 : Nat
#check 1 / 3    -- 1 / 3 : Nat

#eval 42 / 21   -- 2
#eval 1 / 3     -- 0
```

The above fact comes from the *definition* of the operation `/`, which is not what we might expect. And since this is a definition, we can prove funny identities. To understand the following, note that 42 / 15 = 2.8 as decimal numbers.

```lean
#check 42 / 15  -- 42 / 15 : Nat
#eval 42 / 15   -- 2

def fun_fact : 42 / 15 = 2 := Eq.refl (42 / 15)
```

## Deductive reasoning

Let us use tactic mode to write a proof of the rule of deductive reasoning known as *modus ponens*, which says that if we have a proof of the implication `P → Q` and a proof of the proposition `P`, then we have a proof of the proposition `Q`.

```lean
def MP {P Q : Prop} (f : P → Q) (p : P) : Q := by {
  apply f
  exact p
}
```

The proof we give can be understood as follows. First, let us make it clear that `P` and `Q` are propositions, that we have a proof `f` of `P → Q` a proof `p` of `P`, and that our goal is to prove `Q`.

Since by assumption we have a proof of the implication `P → Q`, it suffices to prove `P`. This is what the `apply` tactic enables us to do. More precisely, the term `f` is a function from `P` to `Q`, so it sends a term of type `P` (i.e. a proof a `P`) to a term of type `Q`, i.e. a proof of `Q`. Now, after the `apply` tactic, the goal is changed to `P`. And since, again by assumption, we have a proof of `P`, we can close the goal using the `exact` tactic.

Alternately, we can write the proof using just the `exact` tactic, because `f p` is the result of applying the function `f : P → Q` to the term `p`, and the latter is a term of type `Q`.

```lean
def MP_bis {P Q : Prop} (f : P → Q) (p : P) : Q := by {
  exact f p
}
```

Finally, in term mode, `MP` can be defined (or proven) as follows.

```lean
def MP_ter {P Q : Prop} (f : P → Q) (p : P)  : Q := f p
```

Note that in tactic mode, *one works on the goal to reduce it to the assumptions*. One can then *close the goal* using the `exact` tactic.

We now check that `MP` is indeed a function that, in the presence of Propositions `P` and `Q`, sends a proof of the propositions `P → Q` and `P` to a proof of `Q`.

```lean
#check @MP  -- @MP : ∀ {P Q : Prop}, (P → Q) → P → Q
```

Here we use the `@` because `MP` has implicit arguments (namely `P` and `Q`). The result of `#check @MP` then looks as follows.

MP : ∀ {P Q : Prop}, P → (P → Q) → Q

It is instructive to check that the three definitions we have given are identical.

```lean
-- #print MP
-- #print MP_bis
-- #print MP_ter
```

Next, by using the command `variable`, we add to our context the Propositions `P` and `Q`, as well as a proof of the implication `P → Q` and a proof of `P`.  This is just for convenience in our code below.

```lean
variable {P Q : Prop} (f : P → Q) (p : P)
```

And now, using the function MP and the variables `f` and `p`, we can give a proof of Proposition `Q`: we simply apply the *modus ponens* function to the proofs of the propositions `P` and `P → Q`. Note that `proof_of_Q` is a term of type `Q` and that we are *defining* it.

```lean
def proof_of_Q : Q := MP f p
```

Let us check that the term MP p f is indeed of type `Q`, i.e. that it is a proof of the Proposition `Q`.

```lean
#check MP f p  -- MP f p : Q
```

Alternately, we can write the following (but in the compiler it reduces to `MP f p`):

```lean
#check @MP P Q f p  -- MP f p : Q
```

The two terms `MP f p` and `@MP P Q f p` are in fact identical, but in the second notation we include the *implicit parameters* `P` and `Q`. These implicit parameters were declared with curly brackets `{ }` (see the definition of `MP`), as opposed to `f` and `p`, which were defined using round brackets `( )`.

We now give the tactic mode version of our proof of `Q`, using only the `exact` tactic.

```lean
def proof_of_Q_bis : Q := by {
  exact MP f p
}
```

We can check that the proof terms of `proof_of_Q` and `proof_of_Q_bis` are identical.

```lean
-- #print proof_of_Q
-- #print proof_of_Q_bis
```

To conclude, we give an alternate formulation for the definition of the *modus ponens*, where the terms `f : P → Q` and `p : P` do not appear explicitly, making the definition more compact. The tactic proof, however, is longer, as we must now introduce the variables ourselves, using the `intro` tactic.

```lean
def MP_no_var {P Q : Prop} : (P → Q) → P → Q := by {
  intro f
  intro p
  apply f
  exact p
}
```

Equivalently, we can write `(P → Q) ∧ P → Q`, instead of `(P → Q) → P → Q`. The symbol `∧` is read *and* and can be obtained by typing in the command `\and` or `\we` (as in *wedge*). In that case, the proof is slightly longer, because we wust apply the `rcases` tactic in order to replace the hypothesis `h : (P → Q) ∧ P` by the two hypotheses `f : (P → Q)` and `p : P`.

Here, the names `h`, `f` and `p` are chosen arbitrarily by the user. If we simply write `rcases h` instead of `rcases h with ⟨f, p⟩`, *Lean* will assign names automatically but they will not be directly usable.

```lean
def MP_no_var_bis {P Q : Prop}: P ∧ (P → Q) → Q := by {
  intro h
  rcases h with ⟨p, f⟩
  apply f
  exact p
}
```

### Exercise 3

Formalise the following statement and write a proof of it: given propositions `P`, `Q` and `R`, if `P → Q` and `Q → R`, then `P → R`.
