-- #eval P.eval x

-- #check Fintype α

-- -- variable {R : Type*} [Semiring R ]

-- -- #check Polynomial R[X]


-- -- example (R : Type*) [CommRing R] (r : R) : (C r).coeff 0 = r := by simp

-- -- example (R : Type*) [CommRing R] (r : R) : (X^2 + C r * X : R[X]).coeff 1 = r := by
-- --   apply?

-- -- #check Polynomial.degree (X^2)
-- -- #eval Polynomial.degree (X^2)
-- --  prove using `natDegree_add_eq_left_of_natDegree_lt`

-- variable (R : Type*) [CommRing R] (P : R[X]) (x : R)


-- example (R : Type*) [CommRing R] (P : R[X]) (x : R) : R := P.eval x
-- example (R : Type*) [CommRing R] (r : R) : (X - C r).eval r = 0 := by simp


-- -- example [Nontrivial R] : natDegree (C r * X + C 1) = 1 := by
--   -- rw [natDegree_add_eq_left_of_natDegree_lt]


-- -- example : natDegree (C r * X + C 1) = 1 := by
-- --   apply?


-- example (r : R) : ((X + C 1)^2 : R[X]) = (X^2 + 2 * X + 1: R[X]) := by sorry
--   -- rw[sq, mul_add]

-- -- example {R : Type*} [Semiring R] [NoZeroDivisors R]x {p q : R[X]} :
--     -- degree (p * q) = degree p + degree q :=
--   -- Polynomial.degree_mul
