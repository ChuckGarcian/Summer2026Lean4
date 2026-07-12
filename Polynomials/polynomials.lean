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
variable (R : Type*) [CommRing R] (P : R[X]) (x : R)


/-
Theorem 4.6: Suppose 𝑚 is a positive integer and 𝑝 ∈ 𝒫(𝐅) is a polynomial of degree 𝑚.
Suppose 𝜆 ∈ 𝐅. Then 𝑝(𝜆) = 0 if and only if there exists a polynomial
𝑞 ∈ 𝒫(𝐅) of degree 𝑚 − 1 such that 𝑝(𝑧) = (𝑧 − 𝜆)𝑞(𝑧) for every 𝑧 ∈ 𝐅.
-/

#check natDegree P

example
  (m : ℤ)
  (h₁ : m > 0)
  (P Q: R[X])
  (h₂ : natDegree P = m)
  (h₃ : natDegree Q = m - 1)
  (l : R) : P.eval l = 0 ↔ ∀ z : R, P.eval z = (z - l) * Q.eval z := by sorry




