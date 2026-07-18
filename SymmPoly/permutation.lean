import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Algebra.MvPolynomial.Variables
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Finset.Image
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.Explode

-- set_option trace.Meta.synthInstance true
open BigOperators
open Finset


/- Define global variables -/
variable (σ τ : Type*)
variable [Fintype σ] [DecidableEq σ]
variable [Fintype τ] [DecidableEq τ]
variable (p : MvPolynomial σ Real)


/-
Let p be a symmetric multivariate polynomial; then p is invariant
under any permutation of its variables.
-/
theorem symmInv
  (π : ↑(Equiv.Perm σ))
  : (MvPolynomial.IsSymmetric p) → (MvPolynomial.rename π p  = p) := by
  exact fun a ↦ MvPolynomial.ext ((MvPolynomial.rename π) p) p fun m ↦ congrArg (MvPolynomial.coeff m) (a π)


#explode symmInv
#check Finset.sum Finset.univ fun π ↦ MvPolynomial.rename π p -- Symmetrization


variable (fn := fun (q : MvPolynomial σ Real) (π : ↑(Equiv.Perm σ)) ↦ MvPolynomial.rename π q)
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
noncomputable def symmetrization : MvPolynomial σ Real :=
  (Finset.sum Finset.univ (fn p)) * MvPolynomial.C ((1.0:Real) / N.factorial)


/- Sanity Checks-/
#check symmetrization
#check Fintype
#reduce Fintype
