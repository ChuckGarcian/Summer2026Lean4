/-
Description: Proofs about polynomials from Sheldon Axler's "Linear Algebra Done Right, Chapter 4"
References: Axler, S. (2024). Linear algebra done right (4th ed.). Springer. doi.org
-/
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Eval.Defs


open Polynomial
universe u
variable (α : Type u)
variable (R : Type*) [CommRing R] (P Q: R[X]) (x : R)

-- Syntatic sugar macros
local notation "p" x:max => P.eval x
local notation "q" x:max => Q.eval x

/-
Theorem 4.6 - Each zero of a polynomial corresponds to a degree-one factor:
Suppose 𝑚 is a positive integer and 𝑝 ∈ 𝒫(𝐅) is a polynomial of degree 𝑚.
Suppose 𝜆 ∈ 𝐅. Then 𝑝(𝜆) = 0 if and only if there exists a polynomial
𝑞 ∈ 𝒫(𝐅) of degree 𝑚 − 1 such that 𝑝(𝑧) = (𝑧 − 𝜆)𝑞(𝑧) for every 𝑧 ∈ 𝐅.
-/
example
  (m : ℤ)
  (h₁ : m > 0)
  (h₂ : natDegree P = m)
  (l : R)
  :
  p(l) = 0 ↔ ∃ Q : R[X], (natDegree Q = m - 1) ∧  ∀ z : R, p(z) = (z - l) * q(z) := by

  -- (l : R) : P.eval l = 0 ↔ ∀ z : R, P.eval z = (z - l) * Q.eval z := by
    apply Iff.intro
    case mp =>
      intro h z

    -- Suppose there is poly q ∈ R[x] s.t degree(q) = m-1 and 𝑝(𝑧) = (𝑧 − 𝜆)𝑞(𝑧)
    case mpr =>
      intro h1

      obtain ⟨q, hq⟩ := h1
