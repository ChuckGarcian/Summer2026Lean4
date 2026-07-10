## ArithProg

**Def:** An Airthmetic Progresion is a sequence $a_1,\ldots, a_n$ that satisifies the following invariant (It is defined invariantly)

$$\forall n \in \mathbf{Z},\quad a_{n + 2} - a_{n+1} = a_{n + 1} - a_n$$

## Properties:

From the invariant definition, we have the following properties

**Theorem 1:** For any arithmetic progression, the common difference is constant. That is, $\forall n \in \mathbf{N}\quad a_{n+1} - a_{n} = d$ where $d$ is some constant.

**Theorem 2:** Let $a_n$ be an arithmetic progression with common difference $d$. Then the $a_i$ value of the sequence is given by $a_i = a_0 + i \cdot d$.

**Thoerem 3:** Let $a_n$ be an arithmic progression with common difference $d$, then the sum of of values from $\{a_0, \ldots, a_k\}$ is given by $\sum_i a_i = k\cdot a_0+\frac{k (k - 1)}{2}d$.

-------------

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


**Theorem 2:** Let $a_n$ be an arithmetic progression with common difference $d$. Then the $a_i$ value of the sequence is given by $a_i = a_0 + i \cdot d$

**Proof:**

