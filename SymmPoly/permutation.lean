import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Algebra.MvPolynomial.Variables
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Finset.Image

open BigOperators
open Finset

variable (R : Type*) [CommSemiring R]
variable (σ τ : Type*)

-- variable (fnset : Finset σ)

variable [Fintype σ] [DecidableEq σ]
variable [Fintype τ] [DecidableEq τ]

variable (p : MvPolynomial σ R)
-- variable (f : Equiv.Perm σ → σ)

-- set_option trace.Meta.synthInstance true

variable {α β : Type*} [AddCommMonoid β] [Fintype α] [DecidableEq α]
variable (g : Equiv.Perm α → β)

-- #check ∑ σ : Equiv.Perm α, g σ
#check Finset.sum Finset.univ g

-- def mapperm : σ → τ := fun (x : σ)
variable (π : Equiv.Perm σ)
#check π

#check MvPolynomial.rename π p

/-
Let p be a symmetric multivariate polynomial; then p is invariant
under any permutation of its variables.
-/
example : (MvPolynomial.IsSymmetric p) → (MvPolynomial.rename π p  = p) := by
  exact fun a ↦ MvPolynomial.ext ((MvPolynomial.rename ⇑π) p) p fun m ↦ congrArg (MvPolynomial.coeff m) (a π)

#check Finset.sum Finset.univ fun π ↦ MvPolynomial.rename π p

def test := Finset.sum

noncomputable def fns (P : MvPolynomial σ ℤ)  : MvPolynomial σ ℤ  := MvPolynomial.rename π P

#check (fns p _)
  -- dbg_trace f!"Current value of x: {x}"

#check Fintype
#reduce Fintype

