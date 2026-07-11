-- Descripition: Defines an arithemtic progression object and then proves basic properties about it.
-- Credit: Class implementation is followed from the link below. The lean4 proofs are all written by me
-- Link: https://www.youtube.com/watch?v=84Gx0XbqQq8&t=3006s

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Cases
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Group.Defs


universe u
variable {α : Type u}


-- Define an Arithmetic progression invariantly
class ArithProg (a: ℕ → α) [AddCommGroup α] where
  equal_diff : ∀ n : ℕ, a (n + 1) - a n = a (n + 2) - a (n + 1)


namespace ArithProg

variable {α : Type u} [AddCommGroup α]
variable (a : ℕ → α) [inst : ArithProg a]

local notation "d" => a 1 - a 0


------- Theorems -------


/-
For any arithmetic progression, the common difference is constant. That is,
$\forall n \in \mathbf{N}\quad a_{n+1} - a_{n} = d$ where $d$ is some constant
-/
theorem thm1 : ∀ n : ℕ, a (n + 1) - a n = d := by
  intro n

  induction' n with k hk

  -- Base Case
  case zero =>
    simp only [zero_add]

  -- Inductive Case
  case succ =>

    -- Simplify the left hand side so we can apply the defn arithProg
    rw[add_assoc, show 1 + 1 = 2 by norm_num]

    -- Get the invariant definition of an arithemtic progresion
    have hinv := inst.equal_diff k

    -- Apply the inv def to the goal
    rw[← hinv]

    -- Use the inductive hypothesis
    apply hk


/-
Let $a_n$ be an arithmetic progression with common difference $d$. Then the
$a_i$ value of the sequence is given by $a_i = a_0 + i \cdot d$
-/
theorem thm2 : ∀ i : ℕ, a i = a 0 + (i • (d)) := by
  intro i

  induction' i with k hk

  -- Base case
  case zero =>
    simp

  case succ =>
    -- Swap the equality and simplify
    symm
    rw[succ_nsmul, ← add_assoc, add_comm]

    -- Apply the inductive hypothesis
    rw [← hk]

    -- Use property that conseq elements are equidistant
    have h2 := thm1 a k
    rw[← h2]
    simp
