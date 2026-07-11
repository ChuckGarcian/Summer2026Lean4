import Mathlib

/-
FORMALIZATION PRACTICE: Finset / Fintype / Finset.range
For each comment, write the `example : ... := by sorry` yourself.
Getting the STATEMENT to typecheck is the exercise; proving it is round two.

Tip: hover errors about `ℕ` vs `Finset ℕ` usually mean you forgot a
type ascription like `({1, 2} : Finset ℕ)`.
-/

------------------------------------------------------------
-- PART 1: Finset
------------------------------------------------------------

-- F1. The finite set {1, 2} is a subset of the finite set {1, 2, 3}
--     (as finsets of natural numbers).


-- F2. For any finset s of naturals: if 3 is an element of s,
--     then inserting 3 into s gives back s itself.


-- F3. For any two finsets s and t of naturals: the cardinality of
--     their union is at most the sum of their cardinalities.


-- F4. For any finset s of naturals: the subset of s consisting of
--     its even elements is a subset of s.
--     (Formalize "even elements" with a filter on the predicate
--      "n mod 2 = 0", or with Even — your choice.)


-- F5. For any finset s of naturals: if s is nonempty,
--     then its cardinality is strictly positive.


------------------------------------------------------------
-- PART 2: Fintype
------------------------------------------------------------

-- T1. The type (Fin 3 × Fin 4) has exactly 12 elements.


-- T2. The sum type (Bool ⊕ Fin 3) has exactly 5 elements.


-- T3. Every element of Fin 7 belongs to the universal finset of Fin 7.


-- T4. For any finset s of elements of Fin 9: the cardinality of s
--     is at most the cardinality of the whole type Fin 9.


-- T5. If f is an injective function from Fin 5 to Fin 8, then the
--     cardinality of Fin 5 is at most the cardinality of Fin 8.
--     (State the cardinalities with Fintype.card.)


------------------------------------------------------------
-- PART 3: Finset.range
------------------------------------------------------------

-- R1. The number 4 belongs to Finset.range 10.


-- R2. For any naturals m and n: if m ≤ n,
--     then Finset.range m is a subset of Finset.range n.


-- R3. For any natural n: summing the constant 1 over Finset.range n
--     gives n.


-- R4. For any function f : ℕ → ℕ and any natural n: the sum of f
--     over Finset.range (n + 1) equals the sum of f over
--     Finset.range n, plus f n.


-- R5. For any natural n: twice the sum of i over Finset.range n
--     equals n * (n - 1).      (Gauss — do it by induction.)


------------------------------------------------------------
-- BONUS: statements that should FAIL to typecheck or be false.
-- Try to write them anyway and understand the error / find the
-- counterexample. This teaches you as much as the true ones.
------------------------------------------------------------

-- B1. Try to state "ℕ has a Fintype instance" — why can't you
--     synthesize it?

-- B2. Try to state Finset.range n = Finset.univ (for Fin n) —
--     why does this not even typecheck?

-- B3. State "for all finsets s t, (s ∪ t).card = s.card + t.card"
--     and find the counterexample showing it's false.
