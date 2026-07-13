import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic
import Mathlib.Algebra.Divisibility.Basic

open Polynomial Finset

variable (R : Type*) [CommRing R]

-- or all a b : R, the polynomial a·X² + b·X + 3 in R[X],
-- evaluated at 1, equals a + b + 3.
example (a b : R) : (a • X^2 + b • X + 3 : R[X]).eval 1 = a + b + 3 := by
  simp


-- The square of a ring element is equivalent to the ring element together with itself
-- under the ring operation
example (G : Type*) [CommRing G] (a : G) : a^2 = a * a := by
  exact pow_two a

-- for all a b : R, the constant polynomial C (a * b²)
-- equals C a * C b * C b in R[X].

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

  apply Exists.intro
  case w =>
    exact k * c
  case h =>
      rw[hx]
      ring

