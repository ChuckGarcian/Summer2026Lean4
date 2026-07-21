### Fin (Struct)

**Def:** Fin is a struct is a number i along with the condition that $i < n$. 

**Code:**

      structure Fin (n : Nat) where
        val  : Nat
        isLt : val < n 


      structure Fin' (n : Nat) where
        val  : Nat
        isLt : val < n

      def myFin : Fin' 3 := {val := 2, isLt := by simp}
      
      example (a b : Fin' 3) : a.val < 4 := by simp 
      
      #check myFin
      #eval myFin

**Examples:**

def fin1 : Fin 1:= Fin 1
Fin 2

### (Fin n) --> (X: Type*)

**Def:** A function that takes in a value $i\in [1,\ldots, n]$ and outputs $X$ at the associated value.

Lean4 provides syntatic sugar so that this function can be isntantiated as ![...]

**Examples:**
    import Mathlib.Data.Matrix.Basic

    def ex1 := ![1,0]
    def ex2 := !["a", "b"]

    #eval ex1 0 -- Outputs 1
    #eval ex1 1 -- Outputs 0
    #eval ex2 0 -- Outputs "a"

### Fintype (Type Class)

**Def:** Suuplies every isntance of $X$ as a finite enumeration. 

**Code:**

    class Fintype (X : Type) where
      elems    : Finset X
      complete : ∀ x : X, x ∈ elems

**Examples:**

Fintype Bool, Fintype (Fin 4), Fintype (Bool x Bool)

### Finset

Structure of a finite

### Finsup


## MV Eval

Source: [Evaluating a multivarate polynomial.](https://www.leanexplore.com/?pkg=Batteries&pkg=Init&pkg=Lean&pkg=Mathlib&pkg=Std&q=multivariate+eval#:~:text=GEMINI%203.0%20FLASH%3A-,Evaluation%20of%20Multivariate%20Polynomials.%20Given%20a%20ring%20homomorphism,.,-Find%20similar)

> Evaluation of Multivariate Polynomials. Given a ring homomorphism $f: R \rightarrow S$ and a mapping $g: \sigma \rightarrow S$ that assigns a value in $S$ to each variable index, the evaluation of a multivariate polynomial $p \in \text{MvPolynomial}(\sigma, R)$ is the sum over the terms of $p$ obtained by applying $f$ to each coefficient and substituting $g(n)$ for each variable $n$. Specifically, if $p = \sum_s a_s \prod_n x_n^{s(n)}$, then its evaluation is

$$\text{eval}_2(f, g, p) = \sum_{s} f(a_s) \prod_{n} g(n)^{s(n)}$$

```lean4
def eval₂ (p : MvPolynomial σ R) : S₁ :=
  (AddMonoidAlgebra.coeff p).sum fun s a => f a * s.prod fun n e => g n ^ e
```

    -- Variables indexed by Fin 2, coefficients in ℤ
    -- This represents x₀ and x₁
    noncomputable def myPoly : MvPolynomial (Fin 2) ℤ :=
      X 0 * X 1 + X 0 ^ 2 + C 3 * X 1



        noncomputable def circleEquation : MvPolynomial (Fin 2) ℤ := X 0 ^ 2 + X 1 ^ 2 - 1

    def f := ![1, 0]

    #check @MvPolynomial.eval

    #check (MvPolynomial.eval ![1, 0])

    -- p(1,0) = 0
    example : (MvPolynomial.eval ![1, 0]) circleEquation = 0 := by simp [circleEquation]

## Symmetric

https://github.com/leanprover-community/mathlib4/blob/fd1d54bcac5caba4eff2ea3421c47d907333f515/Mathlib/RingTheory/MvPolynomial/Symmetric/Defs.lean#L104-L105    

    def IsSymmetric [CommSemiring R] (φ : MvPolynomial σ R) : Prop :=
      ∀ e : Perm σ, rename e φ = φ

---------

* (\sum rename e φ )

Perm \sigma 

