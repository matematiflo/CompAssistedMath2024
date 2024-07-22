
**Definition:**

An integral domain $D$ is called a unique factorization domain (UFD) if for every nonzero non-unit element $a$ of $D$, $a$ can be factored into irreducible elements, $a=p_1 p_2 \cdots p_m$ and if there $a=p_1 p_2 \cdots p_m=q_1 q_2 \cdots q_n$ are two irreducible factorizations of $a$, then $m=n$ and there is a permutation $\sigma$ such that each $p_i$ is an associate of $q_{\sigma(i)}$.

**Proof:**

1. Let $p$ irreducible, and $pc=ab$. We need to show that $p|a\lor p|b$.
2. $a$ and $b$ are non-zero and non-unit:
    1. Case 1: $a=0$, then $p|a$, similarly for $b$.
    2. Case 2: $a$ is a unit, then we can rearrange $pc=ab$ to $b=pa^{-1}c\implies p|b$ .
3. c is also non-zero and non-unit: 
    1. $a$ and $b$ are non-zero, therefore $ab=pc\neq 0$ and thus $c\neq 0$.
    2. If $c$ is a unit, then $pc$ is irreducible, and either $a$ or $b$ is a unit, so $c$ is not a unit.
4. Since $D$ is a UFD, there exist unique factorisations: $a=a_{1}a_{2}\dots a_{r}$, $b=b_{1}b_{2}\dots b_{s}$, $c=c_{1}c_{2}\dots c_{t}$. <br>Since $ab$ is non-trivial, and $$ ab=c_{1}c_{2}\dots c_{t}\cdot p=a_{1}a_{2}\dots a_{r}\cdot  b_{1}b_{2}\dots b_{s} $$ $p$ must be an associate of one of $a_{i}$ or $b_{i}$.
5. Suppose $up=a_{i}$, where $u$ is a unit. Then rewriting $a$ as $a=a_{1}a_{2}\dots a_{i-1}pu\cdot a_{i+1}\dots a_{r}$ shows $p|a$. Similarly, if $up=b_{i}$, $p|b$. Thus, $p$ is prime.
