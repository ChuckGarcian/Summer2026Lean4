
**Claim:**

$$\begin{equation}p(z) = (z - \lambda)q(z)\end{equation}$$

**Proof:**
Forward Direction: Suppose $\lambda$ is a root of $p$. This means $p(\lambda) = 0$

We want to show there exists a polynomial of, $q \in R[X]$, of degree $m-1$, such that

$$\begin{equation} p(z) = (z - \lambda)q(z)\end{equation}$$

Let $T(k)$ be the statement

**Basecase:** $T(1)$

Suppose $p$ is a degree 1 polynomial. Then $p(x) = ax$ where $a$ is some constant in $R$.

Observe, that 

$T(k)$

T(k+1)

Assume a $k$ degree polynomial $p$ can be written 

$p(z) = (z - \lambda)q(z) + r (z)$

$p(z) - r(z) = (z - \lambda) q(z)$

-------

Let $R$ be a commutative ring and $f, g \in R[X]$. Let $n$ be a natural number.
Then $f$ can be written in the form 
$$g^n \cdot \left(q + \sum_{i \in \text{Fin } n} \frac{r_i}{g^{i+1}}\right)$$
where $\deg(r_i) < \deg(g)$ and the denominator cancels formally.
See \texttt{quo\_mul\_pow\_add\_sum\_rem\_mul\_pow\_unique} for the uniqueness of this

Comp

$$p,q,r \in P(F)$$

, then

$$(p + q)\circ r = p\circ r + q \circ r$$

$$((p + q)\circ r)(x) = (p\circ r)(x) + (q \circ r)(x)$$
