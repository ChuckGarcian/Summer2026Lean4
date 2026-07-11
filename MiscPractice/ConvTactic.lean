example (a b c : Nat) : a * (b * c) = a * (c * b) := by
  conv =>
    lhs
    congr
    rfl
    rw[Nat.mul_comm]

example : (fun x : Nat => 0 + x) = (fun x => x) := by
  conv =>
    lhs
    intro x
    rw[Nat.zero_add]
example (x : Nat) (h : x + x - x = 3) : x + x - x = 3 := by

  set y := x with ← h2

  sorry
