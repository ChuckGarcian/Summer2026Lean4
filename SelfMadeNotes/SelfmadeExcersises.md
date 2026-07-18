\question

Define what it means for a function a multi-variate function $f$ to be symetric.

\answer

A function $f(x_1, x_2, \ldots, x_n)$ is said to be symmetric, if:

$$\forall \pi \in S_n: \quad f(x_1,x_2, \ldots, x_n) = f(x_{\pi(1)}, x_{\pi(2)}, \ldots, x_{\pi(n)})$$

Where, $S_n$ is the set of all permtuation operators on $n$ elements.

\question

Show that for any symetric polynomial, say $p$, were can write $p$ in the following form

$$p (x_1, \ldots, x_n) = a_1 V_1 + \ldots a_n V_n$$

Where $V_k = \sum_A \prod^k_j x_j$, i.e. the sum of all monomolias of degree $k$ (their permutation)

\answer

Proof:

------

$$f_{imp}(x_1, x_2) = f_{or}(f_{not}(x_1)) x_2$$

$$= f_{not} (x_1) + x_2 - f_{not}(x_1) x_2$$
$$=(1-x_1) + x_2 - (1- x_1) x_2$$

$$=1-x_1 + x_2 - ( x_2- x_1 x_2)$$

$$=1-x_1 + x_2 - x_2+ x_1 x_2$$

$$=1-x_1  + x_1 x_2$$

The coordinate vector of $f$ with respect to the ordered basis $\{1, x_1, x_2, x_1x_2\}$ is 

$$[f]_B = (1, -1, 0, 1)$$

Now Consider what happens if we permute the inputs into $f$. That is we want $f(x_2, x_1)$ instead of $f(x_1, x_2)$

Then 

$$f(x_2, x_1) = 1-x_2  + x_1 x_2$$

And the coordinate vector in the $B$ basis is

$$[f]_B = (1, 0, -1, 1)$$

-----------------------------------------------------------------

$$E_{(x_1, \ldots, x_n \in bern^n (\frac{\mu}{n}))}[\langle f, x\rangle]$$

$$= \sum fPr(\vec{x})$$

$$= \sum f(x) (\frac{\mu}{n})^n$$

$$= \sum \langle f, \vec{x}\rangle (\frac{\mu}{n})^n$$

## Artin Algebra Notes

\question

Define inclusion map

\answer

Let $A$ and $B$ be sets, with $A \subset B$. Then we define an *inclusion map* as the map $i\colon A \rightarrow B$ where 

$$i: a \in A \mapsto a \in B$$

That is, $i$ takes  an element in $A$ and takes it into the same element in $B$. An example is $\mathbb{Z}\rightarrow \mathbb R$ $i(3 \in \mathbb Z) = 3 \in \mathbb  R$

\question

We claim that the map $\psi: \mathbb Z \rightarrow R$ is unique and given by $\psi: n\in \mathbb \mapsto \sum^n1_R\in R$.

Show why the map $\Phi: \mathbb Z \rightarrow R$ given by $\Phi\colon n \in \mathbb Z \mapsto 0_R^n \in R$, does satify. 

\answer

[below is wrong!!!]

By counter example, consider $\Phi$ on $1+2\in Z$. That is consider $\Phi (1 + 2) = \Phi (3) = 0^3_R$

On the other hand, we have 

$$\Phi (1) + \Phi (2) = 0^1_R + 0^2_R$$

Using $R$'s distributive axiom

$$=0_R^1 (1_R + 0_R)$$

Using the fact that $0_R$ is $R$'s additive identity

$$=0_R^1 (1_R)$$

Using the act that $1_R$ is R's multiplicative idenitty. 

$$=1_R$$

Indeed $0^3_R \neq 1_R$


----

\question

In exact case, what is it that we want?

\answer

Let $(x_1, \ldots, x_m)\in [0, n]^m$

1. $\exists x_i=0$, then output 0
2. $\forall x_i \neq0$, then output 1

This is $AND$ composition OR.

\question



\ansewer