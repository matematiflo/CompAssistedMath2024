# Searching mathlib

There are many ways to search Lean's mathematics library `mathlib` for theorems, and not all of these are obvious to new users. Here we demonstrate some techniques. But before we start, a word of warning.

The binomial theorem in Lean will not be called `binomial_theorem`, it will be called `add_pow`, because this is Lean's [naming convention]([add link](https://leanprover-community.github.io/contribute/naming.html)). However, the phrase "binomial theorem" will occur in mathlib, in the *docstring* of the theorem, and possibly also in *module docstring* at the top of the file.

Here are some possibilities for searching.

## Moogle

[Moogle](https://www.moogle.ai/) is an AI-based search algorithm, where you can just type in a text string and it will do its best to point you to relevant mathematics lemmas. Moogle searches everything in mathlib, from the code to the docstrings, and is very easy to use. Note that, like all AI resources, 

For example, if you want to find the cosine rule in mathlib, you can just type "cosine rule" into the search bar in Moogle and it will find it, and even tell you mathlib's rather wacky name for it.

### Good examples

Try searching for the cosine rule! Search for the fact that tensor product is commutative. 


## The API docs

The [mathlib API docs](https://leanprover-community.github.io/mathlib4_docs/) don't search comments *at all*, but are great if you can guess some of the words in the *name* of the theorem. You will get much better at being able to make these guesses if you understand mathlib's [naming convention](https://leanprover-community.github.io/contribute/naming.html). For example theorems about addition might well have `add` in the name (note: not `sum`, which is about finite sums), theorems about subtraction will have `sub` in the name and so on. There is a big list at the aforementioned link.

 A good tip is to type everything in lower-case, because then the search will be case-insensitive.

**Warning**: if you go to a traditional search engine and search for "mathlib documentation" you may well be sent to the mathlib3 documentation, which is probably not where you want to be.

### Examples

Try typing `muladd` into the search box. Or `mul_add`. Now try `Muladd` and see that we don't find `mul_add` any more.

## Loogle

If you're looking for a certain theorem and you know, for example, how to write the hypotheses or conclusion in Lean (because you know the naming
convention), then you can use [loogle](https://loogle.lean-lang.org/). This is a search tool which searches for patterns in theorem statements. It does not read docstrings. You can search using unicode characters by just typing them as you would type them in VS Code.

### Example

Try searching for all functions `ℕ → ℕ` by typing `ℕ → ℕ` into the search box in loogle. There are plenty more examples on the loogle home page.


