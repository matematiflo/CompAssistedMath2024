## Explaining the Theorems: isIrreducible_of_isPrime and isPrime_of_isIrreducible

### Definitions

1. **Divisibility**: We say `x` divides `y` if there exists some `a` such that `y = a * x`. Notation: `x | y`.
2. **Nontrivial Element**: An element `x` is nontrivial if `x ≠ 0` and `x` is not a unit (a unit is an element that has a multiplicative inverse).
3. **Irreducible Element**: An element `x` is irreducible if it is nontrivial and whenever `x = a * b`, either `a` or `b` is a unit.
4. **Prime Element**: An element `x` is prime if it is nontrivial and whenever `x` divides a product `a * b`, `x` divides either `a` or `b`.

### Theorems

#### 1. **Every Prime Element is Irreducible**

**Theorem Statement**: In an integral domain, every prime element is irreducible.

**Proof Idea**:
- Start with a prime element `x`.
- By definition, `x` is nontrivial.
- Assume `x = a * b`.
- Because `x` is prime, `x` divides either `a` or `b`.
- Show that if `x` divides `a`, then `b` must be a unit (and vice versa).
- Conclude that `x` is irreducible because it can only be factored into a product where one of the factors is a unit.

#### 2. **Every Irreducible Element is Prime in a Factorial Ring**

**Theorem Statement**: In a factorial ring (unique factorization domain), every irreducible element is prime.

**Proof Idea**:
- Factorial rings ensure every non-unit can be factored into irreducibles. Given `p` is irreducible and non-trivial, and `a` and `b` are non-units, the product `a ° b` can be factored uniquely into irreducibles.
- Since `p` is a part of the factorization of `a ° b` and `p` is irreducible, `p` must appear in the factorization of either `a` or `b`. Otherwise, it would contradict the unique factorization property.
- Therefore, `p` divides either `a` or `b`.

### Summary

- **Prime implies Irreducible**: Prime elements have a special property of divisibility that ensures they cannot be factored into two non-units, making them irreducible.
- **Irreducible implies Prime in Factorial Rings**: In a unique factorization domain, the structure of factorization ensures that irreducible elements must divide one of the factors of any product they divide, making them prime.
