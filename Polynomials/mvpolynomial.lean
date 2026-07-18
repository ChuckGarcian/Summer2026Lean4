import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Variables
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Finset.Image

variable (R : Type*) [CommSemiring R]
variable (σ : Type*)
variable (p : MvPolynomial σ R)

open MvPolynomial
open Equiv (Perm)

-- Variables indexed by Fin 2, coefficients in ℤ
-- This represents x₀ and x₁
noncomputable def myPoly : MvPolynomial (Fin 2) ℤ :=
  X 0 * X 1 + X 0 ^ 2 + C 3 * X 1

noncomputable def circleEquation : MvPolynomial (Fin 2) ℤ := X 0 ^ 2 + X 1 ^ 2 - 1

example : MvPolynomial.eval ![1, 0] circleEquation = 0 := by simp [circleEquation]

#check MvPolynomial.rename
#check permsOfFinset

variable (R : Type*) [CommSemiring R]
variable (σ : Type*)
variable (p : MvPolynomial σ R)


variable (Q : MvPolynomial (Fin 3) ℤ)

-- noncomputable def symtrz (P : MvPolynomial (Fin 3) ℤ) : MvPolynomial (Fin 3) (ℤ) :=
--   ∑ σi ∈ permsOfFinset (Finset.range 3), (MvPolynomial.rename (fun vars P => σi)) P

-- def indexmap (q: MvPolynomial σ R) := (fun vars q => (Finset.range 3))



variable {σ R : Type*} [CommSemiring R] [DecidableEq σ] (p : MvPolynomial σ R)


variable (R : Type*) [CommSemiring R]
variable (σ : Type*)


variable {σ R : Type*} [CommSemiring R] [DecidableEq σ] (p : MvPolynomial σ R)

#check MvPolynomial.vars

noncomputable def t (p : MvPolynomial σ R) : Finset σ := p.vars


open Finset

-- Definition of an embedding (e.g., adding 1 is strictly injective)

def indexmap :=
  Finset.range 3



#check MvPolynomial.rename (fun Finset.range 3)

#check MvPolynomial.rename

#check (indexmap (vars Q))
#check indexmap Q.vars

#check MvPolynomial.rename Finset.range 3

#check Equiv.Perm σ

noncomputable def symtrz3 (P : MvPolynomial (Fin 3) ℤ) : MvPolynomial (Fin 3) (ℤ) :=
  ∑ Eq.Perm


noncomputable def symtrz3 (P : MvPolynomial (Fin 3) ℤ) : MvPolynomial (Fin 3) (ℤ) :=
  MvPolynomial.rename  P



-- def symtrz (P : MvPolynomial σ R) : (P : MvPolynomial σ R) :=
  -- ∀ e : Perm σ
  -- P.sum

#exit

-- #check (Fin 2) 2

#eval (Fin 2) 2

#print (Fin 2)2

#check myPoly




-- σ : Type* (indexing the variables)
-- R : Type* [CommSemiring R] (the coefficients)
-- s : σ →₀ ℕ, a function from σ to ℕ which is zero away from a finite set. This will give rise to a monomial in MvPolynomial σ R which mathematicians might call X^s
-- a : R
-- i : σ, with corresponding monomial X i, often denoted X_i by mathematicians
-- p : MvPolynomial σ R



-- example (P : MvPolynomial σ R) (h MvPolynomial.IsSymmetric P) :




-- def


-- def addOneEmbedding : ℕ ↪ ℕ :=
--   ⟨fun x => x + 1, fun x y h => Nat.succ.inj h⟩

-- -- Mapping using the embedding
-- def shiftFinset (s : Finset ℕ) : Finset ℕ :=

--   s.map addOneEmbedding
