import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Algebra.MvPolynomial.Variables
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Finset.Image
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Tactic.Explode
import Mathlib.Tactic.Widget.LibraryRewrite
import Mathlib.Logic.Function.Basic
import Mathlib.Logic.Function.Defs
import Init.Data.BitVec
import Init.Prelude
import Paperproof

open Function MvPolynomial


noncomputable section


open MvPolynomial
open BigOperators
open Finset Fintype


variable {σ: Type*} [Fintype σ] [DecidableEq σ]
variable (p : MvPolynomial σ Rat)


-- class exactParity ()
#check {q : ℝ // q = 0 ∨ q = 1}
variable (t : Fin (2^n) → {q : ℝ // q = 0 ∨ q = 1})
#check Or.by_cases

/- Canononical Definition of Parityₙ -/
def parityCanon (n : Nat) (m : Fin (2^n)) : ℝ := Nat.mod m 2
-- def parityCanon (m : Fin (2^n)) : R where
--   val := Nat.mod m 2
--   property := by
--     simp
--     by_cases h : m.val % 2 = 0
--     case pos => exact Or.symm (Or.inr h)
--     case neg =>
--       simp at h
--       exact Or.symm (Or.inl h)

#check parityCanon 2 2

/- Example: Indeed the canoncical representation of Parity₂ evaluated at 2 is 0 -/
example : parityCanon 2 2 = 0 := by
  simp [parityCanon]


/- p(x) = x₁ + x₂ - 2x₁x₂ -/
def parity2bitPoly : MvPolynomial (Fin 2) ℝ := X 0 + X 1 - 2 * X 1 * X 2

variable (f := ![(1 : ℝ), (0 : ℝ)])

/- Example: Check the bit string 01 has odd parity -/
example : MvPolynomial.eval ![0, 1] parity2bitPoly = 1 := by
  simp [parity2bitPoly] -- Apparently this is definitional ¯\_(ツ)_/¯

/- Example: Check the bit string 00 has even parity -/
example : MvPolynomial.eval ![0, 0] parity2bitPoly = 0 := by
  simp [parity2bitPoly]

/- Example: Check the bit string 11 has odd parity -/
example : MvPolynomial.eval ![1, 1] parity2bitPoly = 0 := by
  simp [parity2bitPoly]
  ring

