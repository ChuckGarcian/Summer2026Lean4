import Mathlib.Algebra.Module.Basic

class ArithProg (a: ℕ → α) [AddCommGroup α] where
  equal_diff : ∀ n : ℕ, a (n + 1) - a n = a (n + 2) - a (n + 1)

namespace PartialTrace

-- Variables used throughout
variable {K : Type*} [Field K]
variable {V : Type*} [AddCommGroup V]
variable [Module K V]

class VectorSpace (K : Type u) (V : Type u) [Field K] [AddCommGroup V] [Module K V]

instance
