import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Finset.Image
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Explode
import Mathlib.Tactic.Widget.LibraryRewrite
import Mathlib.Logic.Function.Basic
import Mathlib.Logic.Function.Defs
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

variable {σ: Type*} [Fintype σ] [DecidableEq σ]
variable (p : MvPolynomial σ Rat)

open Function

variable (e x : σ ≃ σ)
variable (f := (Equiv.bijective e))
variable (g := (Equiv.bijective x))
variable (fcmpg := Function.Bijective.comp f g) -- Proof that composition is also bijective

#check f
#check g

#check Function.Bijective.comp f g
#check (Equiv.ofBijective (f := e ∘ x) (hf := fcmpg))

#check Equiv.bijective e
#check (Equiv.ofBijective e e.bijective)
#check Function.Bijective.comp


def permperm (e : σ ≃ σ) : (σ ≃ σ) ≃ (σ ≃ σ) where
      -- L: σ ≃ σ → σ ≃ σσ ≃ σ
      toFun := fun (x : σ ≃ σ) ↦ {
        -- toFun := e ∘ x,
        -- toFun := (Equiv.bijective e) \
        invFun := (x.invFun ∘ e.invFun)
        left_inv := by simp; apply e.left_inv
        right_inv := by simp}
      -- e ∘ x
      -- S(x) = L(x)
      -- S^-1 (L(x)) = x
      -- invFun := fun (y : σ ) ↦ e ∘ y
      invFun := fun (x : σ ≃ σ) ↦ {
        toFun := e ∘ x,
        invFun := (x.invFun ∘ e.invFun)
        left_inv := by sorry
        right_inv := by sorry}

      left_inv := by sorry
      right_inv := by sorry


------- Now testing bijective composition over different types


variable {σ: Type*} [Fintype σ] [DecidableEq σ]
variable {τ: Type*} [Fintype τ] [DecidableEq τ]
variable {α: Type*} [Fintype α] [DecidableEq α]
variable (p : MvPolynomial σ Rat)
universe u
universe v

open Function
noncomputable section

variable (e: σ ≃ τ)
variable (x: τ ≃ α)

variable (g := (Equiv.bijective e))
variable (f := (Equiv.bijective x))
variable (fcmpg := Function.Bijective.comp f g) -- Proof that composition is also bijective

#check f
#check g

#check Function.Bijective.comp f g
#check (Equiv.ofBijective (f := x ∘ e) (hf := fcmpg))

#check Equiv.bijective e
#check (Equiv.ofBijective e e.bijective)
#check Function.Bijective.comp


lemma getEquivFromComp (f : σ ≃ τ) (g : τ ≃ σ) : Bijective (g ∘ f) := by

  /- Obtain proofs that f and g are indeed bijective -/
  have Hbjf := Equiv.bijective f
  have Hbjg := Equiv.bijective g

  /- Now show their composition is necessarly bijective as well -/
  have fcmpg := Function.Bijective.comp Hbjg Hbjf

  /- Hence, the function coresponding to the composition of f and g is also an equivelence
  since it is bijective -/
  exact fcmpg


variable (e: σ ≃ τ)
variable (x: τ ≃ σ)

#check (getEquivFromComp (f := e) (g := x))

def permperm' (e: σ ≃ σ) : (σ ≃ σ) ≃ (σ ≃ σ) where
    toFun := fun (x: σ ≃ σ) ↦
      Equiv.ofBijective (e ∘ x)
      (hf := (getEquivFromComp (g := e) (f := x)))
    invFun := fun x ↦
      Equiv.ofBijective (e.symm ∘ x)
      (hf := getEquivFromComp (g := e.symm) (f := x))
    left_inv := by
      intro x
      ext a
      simp [Function.comp_def]
    right_inv := by
      intro x
      ext a
      simp [Function.comp_def]
