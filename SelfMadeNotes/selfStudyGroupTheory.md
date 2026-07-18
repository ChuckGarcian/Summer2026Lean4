## Description

My notes about group theory. References below:

-- 'Abstract algebra theory and applications, by T. Judson. https://github.com/twjudson/aata

-- A book of abstract algebra, by C. Pinter: https://math.umd.edu/~jcohen/402/Pinter%20Algebra.pdf


## Algebraic Structures

\question

What is a relation $R$?

\answer

A *relation* $R$ is a subset of the cartesian product $A \times B$

$$R = \{ (a, b)\in A\times B \mid a R b \}$$

\question

What are operations?

\answer

An operation is a

\question

What are the group properties of a group $G$?

\answer

Let $U$ and $V$ be in $G$. Then

1. *Inverse:* $U^{-1},V^{-1} \in G$
2. *Closure:* $UV \in G$
3. *Identity:* $I \in G$

\question

What is an abelian group?

\answer
An *abelian group* (also called a *commutative group*) is a group $G$ with binary operation $R$ that also is endowed with the invariant of commutativity. That is, for $a,b \in G$ we have $a + b = b + a$

\question What is a ring?

\answer
A ring is a set $A$ that is an abelian group with commutative binary operation $R_1$, that is also endowed under/with a second binary operation that satisfies the two invariant properties:

1. *Distributivity:* $a R_2 (b R_1 c) = (a R_2 b) R_1 (a R_2 c)$
2. *Associativity:* $a(bc) = (ab)c$

It is the interaction between the two binary operations $R_1$ and $R_2$ that we get the full expressiveness and complexity of a ring (like polynomials for example).

\question Examples of rings?

[Judson Pg 245]

**Example:**

Claim: the set of 2x2 matrices with entries of $\mathbb{R}$ is a ring under addition and multiplication.

Proof: Let $S = \{\begin{bmatrix}a & b \\ c & d\end{bmatrix} \mid a,b,c,d \in \mathbb{R}\}$. Then we must show $S$ is a ring under addition and multiplication. This means that $S$ is an abelian group with operation addition and also endowed with the binary operation of multiplication that satisfies distributivity and associativity.

First we show $S$ is an abelian group under addition. Observe that

1. Identity: $0$ is the element for the addition operation; this is a trivial fact.
2. Associativity: Clearly for any $U, V, T \in S$ we have $U + (V + T) = (U + V) + T$
3. Inverse: Finally, it is trivially true that any $U \in S$ has an inverse $U^{-1} \in S$ since it is just the additive inverse of $U$.
4. Commutativity: For any $U, V \in S$, it is trivial to check that $U + V = V + U$

Therefore, indeed $S$ is an abelian group under addition. Now we must show that $S$ is closed under the multiplication operation and satisfies the invariant properties of distributivity and associativity. I leave such a proof to future me, for it is a tedious thing to type.

\question What are the types of rings?

**Ring with Unity/Identity:** A ring $S$ is said to be a ring with identity if there is an identity element in $S$, call it $e_2$, such that $e_2$ is an identity for the multiplication operation: $e_2 R_2 a = e_2 R_2 a = a$. Note I used the subscript $2$ since $e_1$ is associated with the identity of the abelian group operation that $S$ has (the addition operation)

*Example*

1. Set of binary strings under the $\lor$ and $\wedge$ operators


**Commutative Ring:** A ring is said to be a *commutative ring* if the $R_2$ binary operation is endowed with the commutativity invariant. That is, for $a, b\in S$ we have $a R_2 b = b R_2 a$

*Examples of commutative rings:*

1. Stabilizer group: $Stab (\psi)$. The stabilizer group is the set of stabilizer matrices and by definition they are commutative under multiplication, e.g. $ZI = IZ$

\question What is a monoid?

\answer

1. *Closure:* Operation $R$ s.t. for $a, b\in M$ we have $a R b$
2. *Associativity*
3. *Identity*

Observe: Every group is a monoid, but not every monoid is a group. There is no inverse element in a monoid.

Example: String concat. Let $\Sigma^*$ be a set of strings from alphabet $\Sigma$. Let $R$ be the operation $a R b \iff a.append(b)$. Then $(\Sigma, R)$ is a monoid since,

1. Closure: The concatenation of two strings is a string; therefore the operation has closure

2. Associativity: Let $a, b, c \in \Sigma^*$. We must show $(a R b) R c = a R (b R c)$. In particular, observe $a.append(b) = ab$. So, $(ab).append(c)$ is $abc$. Moreover, $b.append(c)$ is $ab$ and $a.append(bc)$ is $abc$. Therefore, the operation is associative.

3. Identity: Take the empty string $e = \text{""} \in \Sigma^*$ to be the identity since clearly, for any $a \in \Sigma^*$ we have $a.append(e) = a.append(\text{" "}) = a$

We have shown $\left(\Sigma^*, concat\right)$ is closed under the operation, associative, and has an identity element. Therefore it is a monoid. $\square$

## Polynomials

First we define polynomials over a commutative ring $A$ and then we define the set of all such polynomials. From those two definitions, we then show that the set of all polynomials in x is also a commutative ring with unity.

\question

Define polynomial

\answer

Let $A$ be a commutative ring under addition and multiplication operations with unity. Then the object $p(x) = ax^1 + a_2x^2+\ldots + a_n a^n$ is called a *polynomial in x* over $A$.

<!-- class Polynomial A [CommRing A] where
  coeffs: List A -->

\question Define polynomial $A[x]$

\answer

$A[x]$ is a set of polynomials in $x$ whose coefficients are in the set $A$

\question Prove the following

**Claim:** Let $A$ be a commutative ring with unity. We claim $A[x]$ is a commutative ring.

\answer

**Proof:**

Let $A$ be a commutative ring with unity. We want to show that $A[X]$ is also a commutative ring with unity.

Part 1: Showing that $A[X]$ is an abelian group.

Let $p, q \in A[X]$, then they are of the form

$$p(x)$$

1. Identity: We want a polynomial $e_1 \in A[X]$ s.t. $p + e_1 = p$. Simply take $e_1$ as the monomial of degree 0 and coefficient zero. $e_1 \in A[X]$ by construction.

2. Associativity: $(q + p) + z = (q + p) + z$.

$p,q,z \in A[X]$ so we can write $p(x)$

3. Inverse
4. Commutativity


## Maps

\question What is a homomorphic map?

\answer

Let $G$ and $H$ be groups with group operation $\cdot$ and $\circ$ respectively. Then a homomorphism is a map $L: G \rightarrow H$ such that $\forall x, y \in G\colon L(x \cdot y) = L(x)\circ L(y) \in Y$.

\question

Example 1 (Judson Pg169): Let $G$ be a group and $g \in G$. Define a map $L: Z \rightarrow G$ by $L(m) = g^m$ where $m\in \mathbf{Z}$. Show that $L$ is a homomorphic map from group $G$ to group $Z$

\answer

A map is said to be homomorphic if for all $L(\alpha \cdot \alpha) = L(\alpha)L(\alpha)$. In this case, let $m, n \in Z$, then we have

$$L(m + n) = g^{m + n} = g^m g^n = L(m)L(n)$$

Hence, $L$ is homomorphic.