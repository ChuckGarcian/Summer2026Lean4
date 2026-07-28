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


noncomputable section


open MvPolynomial
open BigOperators
open Finset Fintype
open Function MvPolynomial


abbrev Z₂ := Bool
variable {σ: Type*} [Fintype σ] [DecidableEq σ]
variable (p : MvPolynomial σ Rat)


local notation:max "⟦" n "⟧" => Fin n
local notation "{0,1}" => BitVec 1


-- set_option checkBinderAnnotations false
-- set_option diagnostics true


/-
Evaluates a boolean function fₙ at x ∈ {0,1}^n, where x is represented as a
function [n] → {0,1}.
-/
def evalBoolFunction
  (n : Nat)
  (x : ⟦n⟧ → {0,1})
  (fₙ : MvPolynomial ⟦n⟧ Z₂)
  : ℝ :=
  (
    (
      MvPolynomial.eval
      (R := Bool)
      (f := (fun i => (x i).toNat))
    )
    fₙ
  ).toNat


/- Definition: polynomial representation of parity on 2 bits given by
      p(x) = x₁ + x₂ - 2x₁x₂
-/
def parity2bitPoly : MvPolynomial ⟦2⟧ ℝ := X 0 + X 1 - 2 * X 1 * X 2

/- Example: Let p ∈ R[x, y] be the polynomial representation of parity on 2 bits.
Then p(0,1) = 1 -/
example : MvPolynomial.eval ![0, 1] parity2bitPoly = 1 := by
  simp [parity2bitPoly] -- Apparently this is definitional ¯\_(ツ)_/¯

/- Example: Check the bit string 00 has even parity -/
example : MvPolynomial.eval ![0, 0] parity2bitPoly = 0 := by
  simp [parity2bitPoly]

/- Example: Check the bit string 11 has odd parity -/
example : MvPolynomial.eval ![1, 1] parity2bitPoly = 0 := by
  simp [parity2bitPoly]
  ring


/- Canonical parity boolean function defined using mod 2 ring (ring on
integers 0 and 1 with binary operations 'XOR' and 'AND')
-/
def parityₙ (n : Nat) : MvPolynomial ⟦n⟧ Z₂ := ∑ i : ⟦n⟧, (X i) -- i.e. for each bit bᵢ compute ⊕ bᵢ

#check parityₙ

/- Parity boolean function on 2 bits -/
def parity₂ : MvPolynomial ⟦2⟧ Z₂ := parityₙ (n := 2)


/-
Example: parity₂ (00) = 0
-/
example : evalBoolFunction 2 ![0, 0] parity₂ = 0 := by
  simp [parity₂, parityₙ, evalBoolFunction]


/- Example 4: Parity as a polynomial defined over modular 2 addition is equal
to parity defined over addition on real numbers when evaluated at 00 -/
example : (MvPolynomial.eval (R := Bool) ![0, 0] parity₂).toNat = (MvPolynomial.eval ![0, 0] parity2bitPoly) := by
  simp [parity₂, parityₙ, parity2bitPoly]


/- Example 4: Alt solution using 'evalBoolFunction' -/
example : evalBoolFunction
  (n := 2)
  (x := ![0, 0]) parity₂ =
  MvPolynomial.eval ![0, 0] parity2bitPoly:= by
  simp [evalBoolFunction, parity₂, parityₙ, parity2bitPoly]

example : ∀ x : ⟦2⟧ → {0,1}, (evalBoolFunction (n := 2) (x) parity₂) = MvPolynomial.eval (f:=x) parity2bitPoly := by
  intro x
  simp [evalBoolFunction, parity₂, parityₙ, parity2bitPoly]


/- Example: Indeed parity as a polynomial defined over modular 2 addition is equal
to parity defined over addition on real numbers when evaluated at any 2 bit string -/
example : ∀ x : Fin 2 → {0,1},
  -- Why oh why must you be so wretched
  ((MvPolynomial.eval (R := Bool) (f := fun i => ((x i).toNat : Bool)) parity₂).toNat : Real) -
  (MvPolynomial.eval (R := Real) (f := fun i => ((x i).toNat : ℝ))  parity2bitPoly) = 0
  := by sorry


  -- simp[parity₂, parityₙ, parity2bitPoly]
  -- push_cast

  norm_cast




structure PolyApprox (p : MvPolynomial (⟦n⟧) ℝ) (f : MvPolynomial (⟦n⟧) Bool) where
  -- 1. Indstinguishability on the restricted domain
    indst: ∀ x : (⟦n⟧) → {0,1}, p x - f x = 0
