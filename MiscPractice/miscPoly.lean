import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.Tactic.LinearCombination
import Mathlib.Algebra.Polynomial.Eval.Defs

open Complex Polynomial

universe u
variable (α : Type u)
variable (R : Type*) [CommRing R] (P Q: R[X]) (x : R)

-- Getting the coefficients:

-- Returns a function that takes an index and outputs the scalar coefficent in ring R
#check P.coeff
#check P.coeff 2
#check P.coeff 1

-- Showing two polynomials are equal iff their scalar coefficients are equal
example (p q : R[X]) (h : ∀ n : ℕ, p.coeff n = q.coeff n) : p = q := by
  ext

-- Various examples

-- Creating a polynomial
-- Let R be an arbaryy type endowed by commutative Ring properties. Then X is a polynomial over R
noncomputable example {R : Type*} [CommRing R] : R[X] := X

noncomputable example {R : Type*} [CommRing R] (r : R) := X - C r

-- Coeffient of a polynomial
/-
Let R be an arbary set endowed with the properties of a commutative ring.
Then the polynomial X^2 + 3*x + C 1 has a coefficient 1 in it's first coordinate
-/
noncomputable example {R : Type*} [CommRing R] : (X^2 + 3*X + C 1 : R[X]).coeff 0 = 1 := by simp

/-
Let p and q be polynomials over R, with degrees m and n respectively. Then the
polynomial p * q is the a polynomial over R with degree m + n
-/
example {R : Type*} [Semiring R] [NoZeroDivisors R] {p q : R[X]} :
    degree (p * q) = degree p + degree q :=
  Polynomial.degree_mul

example {R : Type*} [Semiring R] [NoZeroDivisors R] {p q : R[X]} :
   degree (p * q) = degree p + degree q :=
-- degree (p * q) = degree p + natDegree q :=
  Polynomial.degree_mul

-- Getting the support of a polynomial is getting where its terms are defined
#check (((X^2 + X : R[X])).support).toFinsupp

variable (Y : R)
#check (((X^2 + X : R[X])).eval Y)
#check (((X^2 + X : R[X])).sum fun _ => 1)
#check (aeval (X^2 + X : R[X]))



-- #check (X^2 + 3*X + X : R[X]).coeffs
-- #eval (X^2 + 3*X + X : ℤ[X]).coeffs

#check comp (X^2 : R[X]) (X+1: R[X])

-- Polynomial.add_comp 📋 Mathlib.Algebra.Polynomial.Eval.Defs
-- {R : Type u} [Semiring R] {p q r : Polynomial R} : (p + q).comp r = p.comp r + q.comp r

-- #check add_comp P

example :  comp (X^2 : R[X]) (X+1: R[X]) = ((X+1)^2 :R[X] ) := by simp

-- #check ∑ n ∈ p.support, f n (a.coeff n)
-- #check (X^2 : ℝ[X]).sum (fun n: Nat

#check (X^2 : ℝ[X]).sum (fun n c => c • (X^n : ℝ[X]))

-- A polynomial is equal to itself: p(x) = a_1x + a_2 x^2 ....
example : (X^2 : ℝ[X]).sum (fun n c => c • (X^n : ℝ[X])) = (X^2 : ℝ[X]) := by apply?


-- def pev : R[X]

-- The difference of a polynomial and the polynomial evalauted at its root is equal to itself: p(x) - p(r) = p(x) ∧ p(r) = 0
example {R : Type*} [CommGroup R] {p : R[X]} (r : R) (h : isRoot r) : p - pev(r) = p := by

-- example {R : Type*} [Semiring R] [NoZeroDivisors R] {p q : R[X]} :

  -- Polynomial.natDegree_comp

-- Ignore
example : aroots (X ^ 2 + 1 : ℝ[X]) ℂ = {Complex.I, -I} := by
  suffices roots (X ^ 2 + 1 : ℂ[X]) = {I, -I} by simpa [aroots_def]
  have factored : (X ^ 2 + 1 : ℂ[X]) = (X - C I) * (X - C (-I)) := by
    have key : (C I * C I : ℂ[X]) = -1 := by simp [← C_mul]
    rw [C_neg]

    linear_combination key
  have p_ne_zero : (X - C I) * (X - C (-I)) ≠ 0 := by
    intro H
    apply_fun eval 0 at H
    simp [eval] at H
  simp only [factored, roots_mul p_ne_zero, roots_X_sub_C]
  rfl

#check aeval (X : R[X]) 2 = 2
-- #eval aeval (X : R[X]) 2


-- #eval P.eval x

-- #check Fintype α

-- -- variable {R : Type*} [Semiring R ]

-- -- #check Polynomial R[X]


-- -- example (R : Type*) [CommRing R] (r : R) : (C r).coeff 0 = r := by simp

-- -- example (R : Type*) [CommRing R] (r : R) : (X^2 + C r * X : R[X]).coeff 1 = r := by
-- --   apply?

-- -- #check Polynomial.degree (X^2)
-- -- #eval Polynomial.degree (X^2)
-- --  prove using `natDegree_add_eq_left_of_natDegree_lt`

-- variable (R : Type*) [CommRing R] (P : R[X]) (x : R)


-- example (R : Type*) [CommRing R] (P : R[X]) (x : R) : R := P.eval x
-- example (R : Type*) [CommRing R] (r : R) : (X - C r).eval r = 0 := by simp


-- -- example [Nontrivial R] : natDegree (C r * X + C 1) = 1 := by
--   -- rw [natDegree_add_eq_left_of_natDegree_lt]


-- -- example : natDegree (C r * X + C 1) = 1 := by
-- --   apply?


-- example (r : R) : ((X + C 1)^2 : R[X]) = (X^2 + 2 * X + 1: R[X]) := by sorry
--   -- rw[sq, mul_add]

-- -- example {R : Type*} [Semiring R] [NoZeroDivisors R]x {p q : R[X]} :
--     -- degree (p * q) = degree p + degree q :=
--   -- Polynomial.degree_mul
