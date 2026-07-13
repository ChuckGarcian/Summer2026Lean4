import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic
import Mathlib.Algebra.Divisibility.Basic

open Polynomial Finset

variable (R : Type*) [CommRing R]


/-
For all a b : R, the polynomial a·X² + b·X + 3 in R[X], evaluated at 1,
equals a + b + 3.
-/
example (a b : R) : (a • X^2 + b • X + 3 : R[X]).eval 1 = a + b + 3 := by
  simp


/-
The square of a ring element is equivalent to the ring element together with
itself under the ring operation
-/
example (G : Type*) [CommRing G] (a : G) : a^2 = a * a := by
  exact pow_two a


/-
for all a b : R, the constant polynomial C (a * b²) equals C a * C b * C b
in R[X].
-/
example (a b : R) : C (a * b^2) = C a * C b * C b:= by
  rw [map_mul]
  conv =>
    lhs
    conv =>
      rhs
      conv=>
        rhs
        rw[pow_two]
      rw[map_mul]
  ring


#check dvd_def


-- for all a b c : R, if a ∣ b then a ∣ b * c.
example {a b c : R} (h : a ∣ b) : a ∣ (b * c) := by
  rw [dvd_def]
  rw [dvd_def] at h
  have ⟨k, hx⟩ := h

  --  Construct the goal in parts
  apply Exists.intro

  -- Take the witness k * c
  case w =>
    exact k * c

  -- Now we show k * c yeilds a | b * c
  case h =>
      rw[hx]
      ring


/-
Difference of squares!
For all l : R, the polynomial (X - C l) divides (X² - C l ²) in R[X].
-/
example (l : R)
        (p q : R[X] )
        (h₁ : p  = (X - C l))
        (h₂ : q = X^2 - (C l)^2 ) :
        p ∣ q := by

        -- Rewrite using divisibility defn
        rw[dvd_def]

        apply Exists.intro

        -- Serve the witness
        case w =>
          exact X + C l

        -- Prove witness correct
        case h =>
          rw[h₁, h₂]
          ring

-- Exercise 5 (Finset sum, concrete).
-- Formalize and prove: the sum over k ∈ range 3 of (k : ℤ)² equals 5.
-- Suggested tools: Finset.sum_range_succ, Finset.sum_range_zero, or decide/norm_num.


-- Exercise 6 (Congruence of sums).
-- Formalize and prove: for all f g : ℕ → R, if f k = g k for every
-- k ∈ range 10, then the sums of f and of g over range 10 are equal.
-- Suggested tool: Finset.sum_congr.

-- Exercise 7 (Divisibility through a sum).
-- Formalize and prove: for all d : R[X], f : ℕ → R[X], n : ℕ, if d divides
-- f k for every k ∈ range n, then d divides the sum of f over range n.
-- Suggested tool: Finset.dvd_sum.

-- Exercise 8 (A polynomial evaluated is the sum of its evaluated monomials).
-- Formalize and prove: for all P : R[X] and l : R, P.eval l equals the sum
-- over k ∈ range (P.natDegree + 1) of (P.coeff k) * l ^ k.
-- Suggested tools: as_sum_range' (with natDegree P < natDegree P + 1),
-- eval_finset_sum, then simp.

-- Exercise 9 (Termwise divisibility).
-- Formalize and prove: for all l a : R and k : ℕ, the polynomial (X - C l)
-- divides (C a * X ^ k - C a * C l ^ k) in R[X].
-- Suggested tools: sub_dvd_pow_sub_pow applied at X and C l, then the
-- technique of Exercise 3 to absorb the coefficient (or mul_sub + Dvd.dvd.mul_left).

-- Exercise 10 (Assembly: the forward direction of Axler 4.6).
-- Formalize and prove: for all P : R[X] and l : R, if P.eval l = 0 then
-- (X - C l) divides P.
-- Plan: rewrite P as P - C (P.eval l) using the hypothesis; express both P
-- and C (P.eval l) as sums over range (P.natDegree + 1) (as_sum_range',
-- Exercise 8, map_sum); combine with Finset.sum_sub_distrib; conclude with
-- Exercises 7 and 9.
-- Forbidden: X_sub_C_dvd_sub_C_eval, dvd_iff_isRoot (they are the answer).
