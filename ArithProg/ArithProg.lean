-- Descripition: Defines an arithemtic progression object and then proves basic properties about it.
-- Credit: Class implementation is followed from the link below. The lean4 proofs are all written by me
-- Link: https://www.youtube.com/watch?v=84Gx0XbqQq8&t=3006s

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Cases

universe u
variable {α : Type u}

-- Define an Arithmetic progression invariantly
class ArithProg (a: ℕ → α) [AddCommGroup α] where
  equal_diff : ∀ n : ℕ, a (n + 1) - a n = a (n + 2) - a (n + 1)


-- variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]


namespace ArithProg

variable {α : Type u} [AddCommGroup α]
variable (a : ℕ → α) [inst : ArithProg a]

local notation "d" => a 1 - a 0

-- Theorems
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
