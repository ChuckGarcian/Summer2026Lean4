---
header-includes:
  - \usepackage{amsmath}  
---

## Definitions

**Def:** An Airthmetic Progresion is a sequence $a_1,\ldots, a_n$ that satisifies the following invariant (It is defined invariantly)

$$\forall n \in \mathbf{Z},\quad a_{n + 2} - a_{n+1} = a_{n + 1} - a_n$$

---------------------------------------------------------------------

## Theorems

From the invariant definition, we have the following properties

**Theorem 1:** For any arithmetic progression, the common difference is constant. That is, $\forall n \in \mathbf{N}\quad a_{n+1} - a_{n} = d$ where $d$ is some constant.

**Theorem 2:** Let $a_n$ be an arithmetic progression with common difference $d$. Then the $a_i$ value of the sequence is given by $a_i = a_0 + i \cdot d$.

**Thoerem 3:** Let $a_n$ be an arithmic progression with common difference $d$, then the sum of of values from $\{a_0, \ldots, a_k\}$ is given by $\sum_i a_i = k\cdot a_0+\frac{k (k - 1)}{2}d$.

---------------------------------------------------------------------
\newpage

## Proofs

**Theorem 1:** For any arithmetic progression, the common difference is constant. That is, $\forall n \in \mathbf{N}\quad a_{n+1} - a_{n} = d$ where $d$ is some constant

**Proof of Thm 1**:

Let $a_n$ be an arithmetic progression. Let $d = a_1 - a_0$ be the common difference between the first two elements of the sequence. Then we must show the common difference is the same for every consequetive element of $a_n$. That is, we want to show

$$\forall n \in \mathbf{N}\quad a_{n+1} - a_{n} = d$$

Let $P(n)$ be the claim up to $n$. We will use induction.

Base Case: $P(0)$ then we must show $a_1 - a_0 = d$

This is true by the definition of $d$

Inductive Case: Suppose $P(k)$ is true for some partiuclar $k \geq 0$. We must show that $P(k+1)$ is also true. That is

$$a_{k+1+1} - a_{k+1} = d$$

Observe, we can use the invariant definition of airthmetic progression to write

$$a_{k+1+1} - a_{k+1} = a_{k+1} - a_{k}$$

Using the inductive hypothesis on the right hand side, gives the claim. This completes the inductive case $\square$.

\newpage

**Theorem 2:** Let $a_n$ be an arithmetic progression with common difference $d$. Then the $a_i$ value of the sequence is given by $a_i = a_0 + i \cdot d$

**Proof:**

Let $a_n$ be an arithmetic progression with common difference $d$. This means each consequtive elemnet in the seqence has distance $|d_{k} - d_{k+1}| = d$. We want to show $a_i$ is given by $a_i = a_0 + i * d$.

We will prove the statement by induction. Let $P(n)$ be the statement with respect to $n$.

**Base Case: $P(n = 0)$**

We must show $a_0 = a_0 + 0 \cdot d$ is true. Oberve,

$$a_0 = a_0 + 0 \cdot d$$

Mul by zero

$$a_0 = a_0 + 0$$

Identity element (add by zero)

$$a_0 = a_0$$

This is true by reflexivity invariant of groups. Hence the base case is true.

**Inductive Case:** Suppose $P(k)$ is true for some $k\geq 0$. We must show that $P(k+1)$ is also true. That is

Assume: $P(k)\colon a_k = a_0 + k \cdot d$  
Goal: $P(k+1)\colon a_{k+1} = a_0 + (k + 1) d$
 
$$a_{k+1} = a_0 + (k + 1) d$$ 

Distribute,

$$a_{k+1} = a_0 + d\cdot k + d$$ 

associativity 

$$a_{k+1} = \left(a_0 + d\cdot k\right) + d$$ 

Use the inductive hypothesis

$$a_{k+1} = a_k + d$$

$$a_{k+1} -  a_k = d$$

Use the invariant definition of arithmetic progressions

$$
a_{k+1} = a_k + d
$$

$$d = d$$

This is a true statement by reflexivity of additive commutative groups. This completes the base case. $\square$

\newpage

**Thoerem 3:** Let $a_n$ be an arithmic progression with common difference $d$, then the sum of of values from $\{a_0, \ldots, a_k\}$ is given by $\sum_i a_i = k\cdot a_0+\frac{k (k - 1)}{2}d$.

**Proof:**

Let $a_n$ be an arithmic progression with common difference $d$.

We want to show that the sum of values from $\{a_0, \ldots, a_k\}$ is given by $\sum_i a_i = k\cdot a_0+\frac{k (k - 1)}{2}d$.

We will use induction. Let $P(n)$ be the statement.

**Base Case:** $P(n=0)$

Observe,
The left hand side of $P(0)$ is

$$\sum_{i=0}^0 a_0 = a_0$$

Moreover, the right hand is

$$a_0 + \frac{0 (0 - 1)}{2}d$$
$$ = a_0 + 0$$
$$ = a_0$$

By reflexivity, $(2)$ and $(5)$ are equal. This completes the base case.

**Inductive Case:** Let the inductive hypothesis be that the statement is true for some $k\geq 0$. We must show that it is also true for $k+1$. That is:

$$\tag{IH} \text{Assume: } P(k): \sum_{i=0}^{k} a_i = k\cdot a_0+\frac{k (k - 1)}{2}d $$
$$\tag{Goal} \text{Goal: } P(k+1): \sum_{i=0}^{k+1} a_i = (k+1)\cdot a_0+\frac{(k+1) (k + 1- 1)}{2}d $$

Observe, the left hand side we can write

$$=\sum_{i=0}^{k+1} a_i = \sum_{i=0}^{k}a_i + a_{k+1}$$

$$=\sum_{i=0}^{k+1} a_i = \sum_{i=0}^{k}a_i + a_{k+1}$$

Invoke the inductive hypothesis

$$=k\cdot a_0+\frac{k (k - 1)}{2}d + a_{k+1}$$

Using theorem 2, we can write $a_{k+1} = a_0 + (k+1)d$. Subsituting this in $(8)$, we have

$$=k\cdot a_0+\frac{k (k - 1)}{2}d + a_0 + (k+1)d$$

$$=k\cdot a_0+\frac{k (k - 1)}{2}d + a_0 + (k+1)d$$
