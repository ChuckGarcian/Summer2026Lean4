/-
Descripition: Proof that a symmetric polynomial, p, when restricted to boolean domain,
is exactly equal to a univarite polynomial q, when q is evaluated at the sum
of variables of p  (Minksey-Paport).

My notes on this file are in 'SelfMadeNotes/730.pdf'
-/
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Algebra.MvPolynomial.Variables
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Tactic.Explode
import Mathlib.Tactic.Widget.LibraryRewrite
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset

open MvPolynomial BigOperators Finset Fintype

noncomputable section
section


/- Define global variables -/
variable {σ: Type*} [Fintype σ] [DecidableEq σ]
variable (p : MvPolynomial σ ℝ)

/- Define first three elementary symmetric polynomials in 3 variables -/
def E₁ : MvPolynomial (Fin 3) ℝ := MvPolynomial.esymm (Fin 3) ℝ 1
def E₂ : MvPolynomial (Fin 3) ℝ := MvPolynomial.esymm (Fin 3) ℝ 2
def E₃ : MvPolynomial (Fin 3) ℝ := MvPolynomial.esymm (Fin 3) ℝ 3

/- p(x,y,z) = x + y + z - xyz -/
def basicSymmetric: MvPolynomial (Fin 3) ℝ := X 0 + X 1 + X 2 - X 0 * X 1 * X 2


/- Example: Prove Mathlib's elementary symmetric polynomials in 1, 2, and 3 variables
are equal to what I think they should be (which should be trivially true,
provided they are what I think they are).
-/
example : E₁ = (X 0 + X 1 + X 2: MvPolynomial (Fin 3) ℝ) := by
  dsimp [E₁]
  simp
  exact Fin.sum_univ_three X


example : E₂ = (X 0 * X 1 + X 1 * X 2 + X 0 * X 2 : MvPolynomial (Fin 3) ℝ) := by
  dsimp [E₂]
  simp [esymm]
  rw [show (Finset.univ : Finset (Fin 3)).powersetCard 2 =
    {{0, 1}, {0, 2}, {1, 2}} by decide]
  rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  repeat' rw [Finset.prod_insert (by decide)]
  repeat' rw [Finset.prod_singleton]
  ring


/- Example 1: A symmetric polynomial has an expansion in the elementary
symmetric basis.
-/
example : basicSymmetric = 1 * E₁ + 0 * E₂ - 1 * E₃ := by
  -- Unfold definitions
  simp [basicSymmetric, E₁, E₂, E₃]
  rw [Fin.sum_univ_three]
  simp[esymm]
  rw[show ((Finset.univ : Finset (Fin 3)).powersetCard 3) = {{0, 1, 2}} by decide]

  -- Show the sums and products unroll into equal values (below rewrites found with rw??)
  rw [sum_singleton (fun x ↦ ∏ i ∈ x, X i) {0, 1, 2}]
  rw [Finset.prod_insert (by decide)]
  rw [Finset.prod_insert (by decide)]
  rw [prod_singleton X 2]
  ring

end section

/- Define first three elementary symmetric polynomials in 3 variables -/
-- def E₁ : MvPolynomial (Fin 2) ℝ := MvPolynomial.esymm (Fin 2) ℝ 1
-- def E₂ : MvPolynomial (Fin 2) ℝ := MvPolynomial.esymm (Fin 2) ℝ 2
-- def E₃ : MvPolynomial (Fin 3) ℝ := MvPolynomial.esymm (Fin 3) ℝ 3

variable (p : MvPolynomial (Fin 3) ℚ)
variable (q : MvPolynomial (Fin 1) ℚ)
abbrev n := 3


/- Define first three elementary symmetric polynomials in N variables -/
def E₁N (N : Nat) : MvPolynomial (Fin N) ℝ := MvPolynomial.esymm (Fin N) ℝ 1
def E₂N (N : Nat) : MvPolynomial (Fin N) ℝ := MvPolynomial.esymm (Fin N) ℝ 2
def E₃N : MvPolynomial (Fin N) ℝ := MvPolynomial.esymm (Fin N) ℝ 3


/- Takes univariate constant to bivariate constant-/
def uniConstantBi  (N : Nat) : (ℝ) →+* (MvPolynomial (Fin N) ℝ) where
  toFun := fun (x : ℝ) => C x
  map_one' := C_1
  map_mul' := fun x y ↦ C_mul
  map_zero' := C_0
  map_add' := fun x y ↦ C_add


/- Take polynomial q(t) into the polynomial q evaluated at x + y:
              q(t) ↦ q(x + y)
-/
def substMapE₁N  (N : Nat) (q : MvPolynomial (Fin 1) ℝ) : MvPolynomial (Fin N) ℝ := (MvPolynomial.eval₂Hom (f := uniConstantBi N) (fun (t : (Fin 1)) => E₁N N)) q


/- Make a boolean bit value be interpreted as a real valued number -/
def boolToReal (b : Bool) : ℝ :=
  if b then 1 else 0


#check ∑ k : Fin 3, ((X k) : MvPolynomial (Fin 3) ℝ)

-- TODO: I need to comment this example (and ultimately finish)!!
example
  :
  -- ∃ q ∈ R[t]:
  ∃ q : MvPolynomial (Fin 1) ℝ,
    -- ∀x, y ∈ {0,1}²: p(x, y) = q(x + y)
    ∀ (x : (Fin 3) → Bool),
      eval (fun i ↦ boolToReal (x i)) ((E₁ + 0 * E₂ - 1 * E₃) : MvPolynomial (Fin 3) ℝ) = eval (fun i ↦ boolToReal (x i)) (substMapE₁N q) := by

  apply Exists.intro

  -- Witness: q(t) = -⅙ t³ + ½t²+ ⅔t
  case w =>
    exact
      - C (1/6) * (X 0) ^ 3
      + C (1/2) * (X 0) ^ 2
      + C (2/3) * (X 0)

  -- Verifier: p(x,y) = q*(x + y)
  -- TODO: Finish the below
  case h =>
    intro x
    apply congrArg
    sorry

    -- simp [substMapE₁, uniConstantBi, E₁, E₃]
    -- have h : (∑ k : Fin 3, ((X k) : MvPolynomial (Fin 3) ℝ)) = (X 0 : MvPolynomial (Fin 3) ℝ) + X 1 + X 2 := by sorry
    -- repeat' rw [C_eq_smul_one]
    -- rw [h]
    -- ring
    -- rw??
    -- norm_num
    -- ring
    -- repeat' rw [← mul_smul_comm]
    -- ring
    -- simp

/- Example 3: Any symmetric polynomial in 2 variables can be written as
a single variable polynomial in the sum of x and y, provided x and y are restricted
to 0 and 1. Formally,
   if isSymmetric (p), then ∃ q ∈ R[t] s.t. ∀ x, y ∈ {0,1}²: p(x, y) = q(x + y)
-/
example
  (p : MvPolynomial (Fin 2) ℝ)
  (h : IsSymmetric p)
  :
  -- /- ∃ q ∈ R[t]: -/
  ∃ q : MvPolynomial (Fin 1) ℝ,
    /- ∀ x, y ∈ {0,1}²: p(x, y) = q(x + y) -/
    ∀ (x : (Fin 2) → Bool),
      eval (fun i ↦ boolToReal (x i)) p = eval (fun i ↦ boolToReal (x i)) (substMapE₁ q)
    := by

    apply Exists.intro
    case h =>
      intro x


    case w =>
    sorry

/- Theorem: Generalization of the previuous two examples: For any symmetric
multivariate polynomial in n variables, we can produce a single varaible polynomial
that is equal to p in the sum of p's variables, provided we restrict the domain to boolean
-/
theorem thmMain
  (N : Nat)
  (p : MvPolynomial (Fin N) ℝ)
  (h : IsSymmetric p)
  :
  -- /- ∃ q ∈ R[t]: -/
  ∃ q : MvPolynomial (Fin 1) ℝ,
    /- ∀ x, y ∈ {0,1}²: p(x, y) = q(x + y) -/
    ∀ (x : (Fin N) → Bool),
      eval (fun i ↦ boolToReal (x i)) p = eval (fun i ↦ boolToReal (x i)) (substMapE₁N N q)
    := by

    apply Exists.intro
    case h =>
      intro x
      repeat' rw [MvPolynomial.eval_eq']


    case w =>
