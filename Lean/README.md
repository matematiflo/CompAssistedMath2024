# Lean resources

## Practice files

- An [introduction](07_intro_to_Lean.md) to Lean as a programming language.
- Some [basic tactics](08_basic_tactics.md) in Lean.
- A homework assignement about [logic in Lean](Assignment/LeanAssignment.md).

## Projects

Here are some Lean project suggestions (in format **Title** *(prerequisites)*: Goal).

1. [Convergence of sequences][conv] *(Analysis 1)*: Prove basic properties of convergent sequences. Show that the sequence of the $n$-th root of $n$ converges to one.
1. [Continuity of real functions][cont] *(Analysis 1)*: Define the notion of a continuous function. Explore some examples. Show the equivalence of continuity and left- and right-continuity combined.
1. [Affine isometries][isom] *(Linear algebra 1)*: Define affine isometries and show that they are always of the form $x \mapsto g*x + y$ for some orthogonal matrix $g$.
1. [Inner automorphisms][inner] *(Group theory)*: Define the group of inner automorphisms of a group. Show that the group $\mathrm{GL}_n(ℝ)$ has an automorphism that is not inner.
1. [Involutions][inv] *(Group theory)*: Define involutions on groups. Prove that if a finite group has an involutive automorphism with no non-trivial fixed points, it is commutative. Construct a counter-example in the non-finite case.
1. [Divisibility in rings][div] *(Algebra 1)*: Define irreducible and prime elements of a ring. Define factorial rings and to show that in a factorial ring, every irreducible element is prime.
1. [Euclidean domains][Euc] *(Linear algebra 2 / Algebra 1)*:  Introduce principal ideal domains and Euclidean rings. Explore some examples and show that every Euclidean domain is a principal ideal domain. Potential extension: Smith Normal Form.
1. [Noetherian rings][Noeth] *(Algebra 1)*: Define Noetherian rings and show a basic characterisation.
1. [Lagrange Polynomials][Lag] *(Linear Algebra 1)*: Define Lagrange polynomials and show that they form a basis of the vector space of bounded polynomials.
1. [The Schröder-Bernstein Theorem][SB] *(Set theory)*: Prove the Schröder-Bernstein Theorem: If two sets $X$ and $Y$ have injections $X \rightarrow Y$ and $Y \rightarrow X$, there exists a bijection $X \rightarrow Y$.

[conv]: Lean/Projects/01_Convergence_of_sequences_(Analysis_1)/Convergence.md
[cont]: Lean/Projects/02.%20Continuity%20of%20real%20functions%20%20(Analysis%201)/Continuity.md
[isom]: Projects/03.%20Affine%20isometries%20(Linear%20algebra%201)/AffineIsometries.md
[inner]: Projects/04.%20Inner%20automorphisms%20(group%20theory)/InnerAutomorphisms.md
[inv]: Projects/05.%20Involutions%20(group%20theory)/Involutions.md
[div]: Projects/06.%20Divisibility%20in%20rings%20(algebra%201)/Divisibility.md
[Euc]: Projects/07.%20Euclidean%20domains%20(Linear%20algebra%202,%20Algebra%201)/Euclidean.md
[Noeth]: Projects/08.%20Noetherian%20rings%20(Algebra%201)/Noetherian.md
[Lag]: Projects/09.%20Lagrange%20polynomials%20(Linear%20Algebra%201)/Lagrange.md
[SB]: Projects/10.%20Schroeder-Bernstein%20theorem%20(Set%20theory)/SchroederBernstein.md

1.%20Convergence%20of%20sequences%20(Analysis%201)/Convergence.md