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


/-
For all a b c : R, if a ∣ b then a ∣ b * c.
-/
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
Difference of squares: (a² - b²) = (a - b)(a + b)
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


#check Finset.sum_range_succ
#eval Finset.sum (Finset.range 3) (fun k => k^2)


/-
The sum over k ∈ range 3 of (k : ℤ)² equals 5.
-/
example : Finset.sum (Finset.range 3) (fun k => k^2) = 5 := by
  simp [Finset.sum_range_succ]


#check Finset.sum_congr


/-
For all f g : ℕ → R, if f k = g k for every k ∈ range 10, then the sums of
f and of g over range 10 are equal.
-/
example
  (f g : ℕ → R)
  (h₂ : ∀ x ∈ Finset.range 10, f x = g x) :
  Finset.sum (Finset.range 10) (fun x => f x) = Finset.sum (Finset.range 10) (fun x => g x)
  := by

  -- It will suffice to show  the functions are equal on the set {1, …, 10}
  apply Finset.sum_congr

  case a =>
    intro x hx
    exact h₂ x hx

  case h => rfl

