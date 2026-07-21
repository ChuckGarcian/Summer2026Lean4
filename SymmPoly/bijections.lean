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

theorem Injective.comp {g : Y → Z} {f : X → Y}
    (Hg : Injective g) (Hf : Injective f) :
  Injective (g ∘ f) := by
  intro x₁ x₂ (h : (g ∘ f) x₁ = (g ∘ f) x₂)
  have : f x₁ = f x₂ := Hg h
  show x₁ = x₂
  exact Hf this

theorem Surjective.comp {g : Y → Z} {f : X → Y}
    (hg : Surjective g) (hf : Surjective f) :
  Surjective (g ∘ f) := by
  intro z
  cases hg z with
  | intro y hy =>
    cases hf y with
    | intro x hx =>
      show ∃ a, (g ∘ f) a = z
      rw [← hy, ← hx]
      show ∃ a, (g ∘ f) a = g (f x)
      exact ⟨x, rfl⟩

theorem Bijective.comp {g : Y → Z} {f : X → Y}
    (hg : Bijective g) (hf : Bijective f) :
  Bijective (g ∘ f) :=
have gInj : Injective g := hg.left
have gSurj : Surjective g := hg.right
have fInj : Injective f := hf.left
have fSurj : Surjective f := hf.right
And.intro (Injective.comp gInj fInj)
  (Surjective.comp gSurj fSurj)

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
#check Equiv.

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

open Function

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


