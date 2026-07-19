import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Algebra.MvPolynomial.Variables
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Finset.Image
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.Explode
import Mathlib.Tactic.Widget.LibraryRewrite
import Paperproof


noncomputable section


-- set_option trace.Meta.synthInstance true
open MvPolynomial
open BigOperators
open Finset


/- Define global variables -/
variable (σ τ : Type*)
variable [Fintype σ] [DecidableEq σ]
variable [Fintype τ] [DecidableEq τ]
variable (p : MvPolynomial σ Rat)


variable (fn := fun (q : MvPolynomial σ Rat) (π : Equiv.Perm σ) ↦ MvPolynomial.rename π q)
variable (N := p.vars.card) -- Number of variables in a multivarirate poly


/- Sanity Checks -/
#check Finset.sum
#check Finset.sum Finset.univ (fn p) -- Summation over all permutations of the polynomial p
#check Finset.card
#check Finset.sum Finset.univ fun π ↦ MvPolynomial.rename π p -- Symmetrization

#check N
#check Nat.factorial N
#check  (Finset.sum Finset.univ (fn p)) * MvPolynomial.C ((1.0:Real) / N.factorial)


/------------------------------- Definitions -------------------------------/


/-
Let p: Rᴺ ↦ R be a polynomial, then $L(p)(x) = \frac{1}{N!}\sum_{\pi \in S_n}
p(x\circ \pi)$ is the symmtization of $p$
-/
def symmetrization : MvPolynomial σ Rat :=
  (Finset.sum Finset.univ (fn p)) * MvPolynomial.C ((1: Rat) / N.factorial)


def symmetrization' (q : MvPolynomial σ Rat) : MvPolynomial σ Rat :=
  (1/(Fintype.card (Equiv.Perm σ)) : Rat) • ∑ π : (Equiv.Perm σ), MvPolynomial.rename π q


/- Define: p(x,y) = x² + y² -/
def basicSymmetric: MvPolynomial (Fin 2) Rat := X 0 ^2 + X 1 ^2


/- Define: p(x,y) = x² + y + 1 -/
def NotSymmetricPoly: MvPolynomial (Fin 2) Rat := X 0 ^2 + X 1 + 1


/------------------------------- Examples -------------------------------/

/- Example 1: Indeed, p(x,y) = x² + y² is symmetric (Chuck Solution)-/
example : MvPolynomial.IsSymmetric basicSymmetric:= by
  intro π
  simp [basicSymmetric]
  fin_cases π; simp; simp
  ring


/- Example 1 sol by Albert Smith, Zulip:
https://leanprover.zulipchat.com/#narrow/channel/113488-general/topic/Showing.20x.C2.B2.20.2B.20y.C2.B2.20is.20symmetric/near/611508693
-/
example : basicSymmetric.IsSymmetric := by
  convert psum_isSymmetric (Fin 2) Rat 2
  simp +locals [psum]

/- Example 1 sol Albert's alternative -/
example : basicSymmetric.IsSymmetric := by
  convert psum_isSymmetric (Fin 2) Rat 2
  rw[psum]
  simp [basicSymmetric]


/- Example 1 sol other Zulip User solution -/
example : IsSymmetric basicSymmetric := by
  rw [IsSymmetric, basicSymmetric]
  intro σ
  by_cases h : σ 0 = 0
  · have h1 : σ 1 = 1 := by sorry
    simp [h, h1]
  · have h' : σ 0 = 1 ∧ σ 1 =0 := by sorry
    simp [h', add_comm]


/- Example 1 sol, Chatgpt solution (for comparison) -/
example : MvPolynomial.IsSymmetric basicSymmetric := by
  unfold basicSymmetric
  have h := MvPolynomial.psum_isSymmetric (Fin 2) Rat 2
  rw [MvPolynomial.psum, Fin.sum_univ_two] at h
  exact h


/- Example 2:
  p(x,y) = x² + y² is symmetric and therefore should be invariant
  to symmetriziation.
-/
example : basicSymmetric = symmetrization' (q:=basicSymmetric) := by
  simp [basicSymmetric, symmetrization']


/- Example 3: Indeed, p(x,y) = x² + y + 1 is not symmetric! (duh) -/
example : ¬MvPolynomial.IsSymmetric NotSymmetricPoly := by sorry


/- Example 4: p(x,y) = x² + y + 1 is symmetric under symmetrization -/
example : MvPolynomial.IsSymmetric (symmetrization (p := NotSymmetricPoly)) := by sorry


/------------------------------- Theorems -------------------------------/


/-
Let p be a symmetric multivariate polynomial; then p is invariant
under any permutation of its variables.
    ∀a ∈ Sₙ: p(x₁, … , xₙ) = p(xₐ₍₁₎, … , xₐ₍ₙ₎)
-/
theorem symmInv
  (π : Equiv.Perm σ)
  : (MvPolynomial.IsSymmetric p) → (MvPolynomial.rename π p  = p) := by
    exact fun a =>
      MvPolynomial.ext ((MvPolynomial.rename π) p) p
        fun m =>
          congrArg (MvPolynomial.coeff m) (a π)


/- Theorem 1: Symmetric polynomials are invariant to symmetrization:
Let p ∈ R[x₁, … , xₙ] be a multiviariate polynomial in n variables.
Then if p is symmetric, it shall be invariant under Symmetrization. Formally,
        ∀ p ∈ R[x₁, …, xₙ]: isSymm (p) → p = p^symm
-/
theorem thm1 : ∀ p : MvPolynomial σ Rat, MvPolynomial.IsSymmetric p → p = (symmetrization' (q:=p)) := by
  intro p hs

  -- Simplify into definitions
  simp [symmetrization']

  -- Simpilify summation into a sum of N p's, where N is normalization cnst
  conv=>
    rhs
    conv=>
      rhs
      conv=>
        rhs
        enter [π]
        -- Symmetric hypothesis gives invariance in sum terms: p = π p
        rw [(symmInv (p := p) (π:=π)) hs]
  simp

  -- Make goal easier to read
  set n := Fintype.card (Equiv.Perm σ) with h

  -- Finiky Typed multiplication
  rw [← MvPolynomial.C_eq_coe_nat (R := Rat) (σ := σ) n]
  rw [MvPolynomial.C_mul']

  -- Show the norm constants cancel
  have hn : (n : Rat)⁻¹ * (n : Rat) = 1 := by sorry --Clearly n*n^⁻¹=1
  rw [smul_smul ((n : Rat)⁻¹) (n : Rat) p]
  rw[hn]; simp


/- Theorem 2: Any multivariate function can be made symmetric:
Let p ∈ R[x₁, … , xₙ] be a multiviariate polynomial in n variables.
Then if p is not symmetric, then certaintly it shall be symmetric on
application of symmetrization. Formally, the following is a true statement
-/
theorem thm2 : ∀ q: MvPolynomial σ Rat, MvPolynomial.IsSymmetric (symmetrization' (q:=q)) := by
  intro h
  simp [symmetrization']
  simp[MvPolynomial.IsSymmetric]
