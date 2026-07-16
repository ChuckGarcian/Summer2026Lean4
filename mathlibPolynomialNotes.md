### Definitions

<!-- **Def 1:** Define map homomorphism $\tau\colon R \rightarrow S$ that maps scalars in $R$ into scalars in $S$. -->

<!-- **Def 2:** Let $\phi: S\rightarrow S[X]$ be the inclusion map from constants in $R$ to polynomials with coefficients in $R[X]$. -->

**Def: Constant map** Let $C: R \rightarrow R[X]$ be the *constant homomorphism* which maps constants in $R$ to polynomials with coefficients in $R$. Given by

$$a \in R \overset{C}{\mapsto} a X^0 \in R[X]$$

Link: [Link here](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Polynomial/Basic.html#Polynomial.C)

<!-- u**Def 4:** Let $Eval\colon$ -->

<!-- Compose $\tau$ with $\phi$ to get $(\phi \circ \tau): S \rightarrow S[X]$ -->

### The substitution map in lean4

Let $\phi:R\rightarrow R^\prime$ be a ring homomorphism.

We can define a unique homomorphism $T: R[X] \rightarrow R^\prime$ which agrees with $\phi$ on constant polynomials (polynomials of the form $X^0$) and maps all others $x \mapsto \alpha \in R^\prime$. (This *substitution map* definition is borrowed from: [Artin's Algebra Book ](https://www.cse.iitb.ac.in/~sohoni/CS782/ArtinAlgebra.pdf))

Lean defines exactly such a map via the $\text{eval}_2$ definition:

```lean4
irreducible_def eval₂ (p : R[X]) : S :=
  p.sum fun e a => f a * x ^ e
```

Where sum is defined by

```lean4
p.sum f = ∑ n ∈ p.support, f n (p.coeff n)
```

We will therefore notate the eval_2 function with the following

$$T = \sum_{n \in \sup (p)} f (\cdot) (\cdot)^n\colon (p,X) \in R[X]\times S\mapsto \sum_{n \in \sup (p)} f (p_i) X^n$$

Link: [Eval_2 map](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Polynomial/Eval/Defs.html#Polynomial.eval%E2%82%82_def)

Observe that $T$ is semantically equivalent with a *substitution* homomorphic map

## **Realizations:**

#### Evaluation map

[Evaluating a polynomial at](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Polynomial/Eval/Defs.html#Polynomial.eval) a particular value in lean4 is given by eval:

```lean4
def eval (x : R) (p : R[X]) : R :=
  eval₂ (RingHom.id _) x p
```

Let $\alpha\in R$, $p(x) \in R[X]$ and let $I$ be the identity ring homomorphism. Then we can notationally represent the eval map as

$$T_{(I, \alpha)}(p(x)) = T_{I, \alpha}\left(\sum_k a_k x^k\right)$$

**Prop:** $T_{I,\alpha}(p)(x) = p(\alpha)$. That is, $T_{I, \alpha}$ gives the polynomial $p$ as a function evaluated at value $\alpha \in R$

**Proof:** Observe, using the fact that $T$ itself is homomorphic

$$T_{(I, \alpha)}(p(x)) = \sum_k T_{I, \alpha}\left(a_k x^k\right)$$

$$T_{(I, \alpha)}(p(x)) = \sum_k T_{I, \alpha}\left(a_k\right)\cdot T_{I, \alpha}\left(x\right)^k$$

Using the fact that $T_{I, \alpha}$ agrees with $I$ on constant polynomials and sends $x \mapsto \alpha$.

$$T_{(I, \alpha)}(p(x)) = \sum_k I\left(a_k\right) \cdot \alpha^k$$

$$T_{(I, \alpha)}(p(x)) = \sum_k a_k \cdot \alpha^k$$

Indeed, the right hand side is in $R$ which is what we expect from an evaluation map.

#### Composition

[Composition in lean4](https://github.com/leanprover-community/mathlib4/blob/3d1773a1de56b88e2dc19e80110d95f4a2a73545/Mathlib/Algebra/Polynomial/Eval/Defs.lean#L380-L382) is given by

```lean4
def comp (p q : R[X]) : R[X] :=
  p.eval₂ C q
```

Notationally we can represent with

$$T_{(C, q)}(p(x)) = T_{C, q}\left(\sum_k a_k x^k\right)$$

Where $C$ is the constant homomorphism and $q$ is a polynomial in $R[X]$

**Prop:** $T_{C,q}(p)(x) = (q\circ p)(x)$

**Proof:**
Observe,

$$T_{(C, q)}(p(x)) = T_{C, q}\left(\sum_k a_k x^k\right)$$

Using the fact that $T$ itself is homomorphic

$$T_{(C, q)}(p(x)) = \sum_k T_{C, q}\left(a_k\right)\cdot T_{C, q}\left(x\right)^k$$

Using the fact that $T$ acts as $C$ on constants in $R$ and acts maps $x\mapsto q$

$$T_{(C, q)}(p(x)) = \sum_k C\left(a_k\right) \cdot q^k$$

Finally, use the fact that for all $\alpha\in R, C(\alpha) = \alpha x^0 \in R[X]$

$$T_{(C, q)}(p(x)) = \sum_k a_k x^0 \cdot q^k$$

Indeed, $T_{(C, q)}$ is a homomorphic map that has the effect of composition of polynomials $p,q\in R[X]$. $\square$