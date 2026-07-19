import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Algebra.MvPolynomial.Variables
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Finset.Image
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.Explode

noncomputable section

-- set_option trace.Meta.synthInstance true
open MvPolynomial
open BigOperators
open Finset


/- Define global variables -/
variable (σ τ : Type*)
variable [Fintype σ] [DecidableEq σ]
variable [Fintype τ] [DecidableEq τ]
variable (p : MvPolynomial σ Int)


/-
Let p be a symmetric multivariate polynomial; then p is invariant
under any permutation of its variables.
-/
theorem symmInv
  (π : ↑(Equiv.Perm σ))
  : (MvPolynomial.IsSymmetric p) → (MvPolynomial.rename π p  = p) := by
  exact fun a =>
    MvPolynomial.ext ((MvPolynomial.rename π) p) p
      fun m =>
        congrArg (MvPolynomial.coeff m) (a π)


#explode symmInv
#check Finset.sum Finset.univ fun π ↦ MvPolynomial.rename π p -- Symmetrization


variable (fn := fun (q : MvPolynomial σ Int) (π : ↑(Equiv.Perm σ)) ↦ MvPolynomial.rename π q)
variable (N := p.vars.card) -- Number of variables in a multivarirate poly


/- Sanity Checks -/
#check Finset.sum
#check Finset.sum Finset.univ (fn p) -- Summation over all permutations of the polynomial p
#check Finset.card

#check N
#check Nat.factorial N
#check  (Finset.sum Finset.univ (fn p)) * MvPolynomial.C ((1.0:Real) / N.factorial)


/-
Let p: Rᴺ ↦ R be a polynomial, then $L(p)(x) = \frac{1}{N!}\sum_{\pi \in S_n}
p(x\circ \pi)$ is the symmtization of $p$
-/
noncomputable def symmetrization : MvPolynomial σ Int :=
  (Finset.sum Finset.univ (fn p)) * MvPolynomial.C ((1: Int) / N.factorial)


/- Define: p(x,y) = x² + y² -/
def basicSymmetric: MvPolynomial (Fin 2) Int := X 0 ^2 + X 1 ^2

#check MvPolynomial.rename
#check MvPolynomial.coeff
#check MvPolynomial.ext


/- Example 1: Indeed, p(x,y) = x² + y² is symmetric -/
example : MvPolynomial.IsSymmetric basicSymmetric:= by
  intro π
  simp [basicSymmetric]
  fin_cases π
  simp
  conv=> lhs
  simp
  ring


/- Example 2:
  p(x,y) = x² + y² is symmetric and therefore should be invariant
  to symmetriziation.
-/
example : basicSymmetric = symmetrization (p := basicSymmetric) := by sorry


/- Define: p(x,y) = x² + y + 1 -/
def NotSymmetricPoly: MvPolynomial (Fin 2) Int := X 0 ^2 + X 1 + 1


/- Example 3: Indeed, p(x,y) = x² + y + 1 is not symmetric! (duh) -/
example : ¬MvPolynomial.IsSymmetric NotSymmetricPoly := by sorry


/- Example 4: p(x,y) = x² + y + 1 is symmetric under symmetrization -/
example : MvPolynomial.IsSymmetric (symmetrization (p := NotSymmetricPoly)) := by sorry


/- Theorem 1: Symmetric polynomials are invariant to symmetrization:
Let $p \in R[x_1, \ldots, x_n]$ be a multiviariate polynomial in $n$ variables.
Then if $p$ is symmetric, it shall be invariant under $L(p)$. Formally
\forall p \in R[x_1, \ldots, x_n]\colon\quad isSymm(p) \implies p = p^{symm}, p^{symm} = L(p)
-/
theorem thm1 : ∀ p : MvPolynomial σ Int, MvPolynomial.IsSymmetric p → p = symmetrization (p := p) := by sorry


/- Theorem 2: Any multivariate function can be made symmetric:
Let $p \in R[x_1, \ldots, x_n]$ be a multiviariate polynomial in $n$ variables.
Then if $p$ is not symmetric, then certaintly it shall be symmetric on
application of $L$. Formally, the following is a true statement
-/
theorem thm2 : ∀ q: MvPolynomial σ Int, MvPolynomial.IsSymmetric (symmetrization (p:=q)) := by sorry


-- Hi!


-- Could I possibly get a hint on a problem im having.

-- I'm trying to show that the bivariate polynomial p(x,y) = x² + y² is indeed symmetric.
-- So far, I've been trying to show it using externalty (code below) but am unsure how to handle
-- the coefficient function.

-- Another approach i thought of was to some brute force through all permutatoin maps
-- (2! in this case) and show equality in each case, but am unsure how I would go
-- about setting that up. Mainly, in this approach, im unsure of what I would actually
-- pass to the cases tactic -- one would have to turn Equiv.perm (fin 2) into an
-- inductive type somehow? Then from there it should be straight forward calc.

-- Any help/hint is appreciated. below is my info view and current code.
-- Thanks!

-- Infoview:
-- N : ℕ
-- π : Equiv.Perm (Fin 2)
-- ⊢ ∀ (m : Fin 2 →₀ ℕ), coeff m (X (π 0) ^ 2 + X (π 1) ^ 2) = coeff m (X 0 ^ 2 + X 1 ^ 2)

-- Code:
-- /- Define: p(x,y) = x² + y² -/
-- def basicSymmetric: MvPolynomial (Fin 2) Int := X 0 ^2 + X 1 ^2
