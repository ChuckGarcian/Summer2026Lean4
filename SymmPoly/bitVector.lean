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
import Mathlib.Algebra.Ring.BooleanRing
import Paperproof

open Function MvPolynomial


noncomputable section


open MvPolynomial
open BigOperators
open Finset Fintype


variable {σ: Type*} [Fintype σ] [DecidableEq σ]
variable (p : MvPolynomial σ Rat)


/- p(x) = x₁ + x₂ - 2x₁x₂ -/
def parity2bitPoly : MvPolynomial (Fin 2) ℝ := X 0 + X 1 - 2 * X 1 * X 2

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


def valuation (m : Fin n) : (Bool) := 0

variable {Z₂ : Type*} [BooleanRing Z₂]

/- Canoncical parity boolean function defined using mod 2 ring (ring on
integers 0 and 1 with binary operations XOR and 'and')
-/
def parityₙ (n : Nat): MvPolynomial (Fin n) Z₂ := ∑ i : Fin n, (X i)

def parity₂ : MvPolynomial (Fin 2) Z₂ := parityₙ (n := 2)

/-
Example: Indeed 2 bit parity works.
-/
example : MvPolynomial.eval (R := Bool) ![0, 0] parity₂ = 0 := by
  simp [parity₂]


structure PolyApprox (p : MvPolynomial (Fin n) ℝ) (f : MvPolynomial (Fin n) Bool) where
  -- 1. Indstinguishability on the restricted domain
    indst: ∀ x : (Fin n) → BitVec 1, p x - f x = 0
