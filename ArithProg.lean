import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Cases

universe u
variable {α : Type u}

-- Define an Arithmetic progression invariantly
class ArithProg (a: ℕ → α) [AddCommGroup α] where
  equal_diff : ∀ n : ℕ, a (n + 1) - a n = a (n + 2) - a (n + 1)

namespace ArithProg


variable {α : Type u} [AddCommGroup α]
variable (a : ℕ → α) [inst : ArithProg a]

local notation "d" => a 1 - a 0

-- Theorems
theorem thm1 : ∀ n : ℕ, a (n + 1) - a n = d := by
  intro n

  induction' n with k hk

  case zero =>
    simp only [zero_add]

  case succ =>

    -- Simplify the left hand side so we can apply the defn arithProg
    rw[add_assoc, show 1 + 1 = 2 by norm_num]

    -- Get the invariant definition of an arithemtic progresion
    have hinv := inst.equal_diff k

    -- Apply the inv def to the goal
    rw[← hinv]

    -- Use the inductive hypothesis
    apply hk
