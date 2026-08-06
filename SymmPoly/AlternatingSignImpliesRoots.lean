import Mathlib.Topology.Defs.Basic
import Mathlib.Topology.UniformSpace.Real
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Continuous
import Mathlib.Tactic.Cases
import Mathlib.Data.Finset.Range
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.Group.Even
import Mathlib.Tactic.Basic -- brings in rcases/and_destruct
import Mathlib.SetTheory.Cardinal.Finite
import Init.Classical
import Mathlib.Data.Set.Card

open Set Finset

noncomputable section

open Set

/-Define Predicates-/
def isRoot (f : ℝ → ℝ) (x : ℝ) : Prop := f x = 0

def P (f : ℝ → ℝ) (x : Nat) : Prop :=
  (Even x ∧ f x ≤ -(1 / 6 : ℝ)) ∨
  (Odd x ∧ f x ≥ (1 / 6 : ℝ))

def Q (S : Set ℝ) (n : Nat) (f : ℝ → ℝ) : Prop := S.ncard = n ∧ ∀ x ∈ S, isRoot f x ∧ x ∈ (Set.Icc 0 (n : ℝ))

/- Example: Let g(x) = 0 and f(x) be a continuous function such that
for some x and y we have that f(x) < g(x) and g(y) < f(y). Then there must
be some value, c ∈ ℝ, such that f(c) = 0.
-/
lemma thm0
  (x y : ℝ)
  (g : ℝ → ℝ) (hg : Continuous g) (hgz : ∀ a, g a = 0)
  (f : ℝ → ℝ) (hf : Continuous f)
  (ha : f x ≤ g x)
  (hb : g y ≤ f y) :
  ∃ c : ℝ, f c = 0 := by
    -- Use special case of the intermediate value theorem
    -- Obtain proof that a root exists using IVU
    obtain ⟨w, h⟩ := intermediate_value_univ₂ hf hg ha hb

    -- IVU gives a witness in terms of the zero function, g. So we rewrite in terms of 0 ∈ ℝ
    rw [hgz w] at h
    apply Exists.intro
    exact h

def zeroFunc : ℝ → ℝ := fun _ => 0

/- Example: Let f(x) be a continuous function such that
for some x and y we have that f(x) < 0 and 0 < f(y). Then there must
be some value, c ∈ ℝ, such that f(c) = 0.
-/
lemma thm1
  (x y : ℝ)
  (f : ℝ → ℝ) (hf : Continuous f)
  (ha : f x ≤ 0)
  (hb : 0 ≤ f y) :
  ∃ x : ℝ, f x = 0 := by

    -- Rewrite the 0 constants as the zero function: g(y) = 0, y ∈ ℝ
    change f x ≤ zeroFunc x at ha
    change zeroFunc y ≤ f y at hb

    -- Certificate showing the zero function is continuous and always equal to zero
    have hg : Continuous zeroFunc := by exact continuous_of_const fun x ↦ congrFun rfl
    have hgz : ∀ l, zeroFunc l = 0 := by exact fun l ↦ Real.ext_cauchy rfl

    -- Reduced to the thm0 case
    apply thm0; repeat' assumption

#check LE.le.trans

/- Theorem: Special case Intermediate value theorem:
Let f(x) be a continuous function such that
for some real numbers x and y, we have that f(x) < -⅙ and ⅙ < f(y). Then there must
be some real value, c, such that f(c) = 0.
-/
theorem thm2IVT
  (x y : ℝ)
  (f : ℝ → ℝ)
  (hf : Continuous f)
  (ha : f x ≤ -1/6)
  (hb : 1/6 ≤ f y) :
  ∃ x : ℝ, isRoot f x := by

    -- Reduce the statement to the more general statement at f(x) ≤ 0 and f(x) ≥ 0; this should be trivial -- emphasis on should :(
    have lowerBoundConv : (-1 : ℝ) / 6 ≤ 0 := by norm_num
    have upperBoundConv : (1/6 : ℝ) ≥ 0 := by norm_num
    have h1 : f x ≤ 0 := by exact LE.le.trans ha lowerBoundConv
    have h2 : 0 ≤ f y := by exact Std.IsPreorder.le_trans 0 (1 / 6) (f y) upperBoundConv hb

    -- Theorem one can prove the rest
    apply thm1; repeat' assumption

/- Quantifer Split -/
lemma lemma0
  (N : ℕ)
  {f : ℝ → ℝ}
  (hf : Continuous f) :
  (∀ x : Fin (N + 1), P f x) ↔ P f (N) ∧ ∀ x : Fin (N), P f x := by sorry


/-
Two consective naturals numbers satify predicate P, then there is a root.
-/
lemma lemma1
  (f : ℝ → ℝ) (hf : Continuous f)
  (n : Nat)
  (h₁ : P f n)
  (h₂ : P f (n + 1))
  :
  ∃ S : Set ℝ , Q S 1 f := by sorry
  -- ∃ x : ℝ, isRoot f x ∧ x ∈ (Set.Icc (n : ℝ ) (n + 1 : ℝ)):= by sorry

lemma lemma2
  (f : ℝ → ℝ)
  (hf : Continuous f)
  (n : Nat)
  (h₁ : ∃ S₁ : Set ℝ , Q S₁ n f)
  (h₂ : ∃ S₂ : Set ℝ , Q S₂ 1 f) :
  ∃ T : Set ℝ, Q T (n + 1) f := by sorry

/-
Theorem: If every adjecent pair of integers in the set {0, …, n}, when n ≥ 1,
alternate sign under f (e.g. f(0) < 0 ∧ f(1) > 0), then there is a set S that
contains roots of f, where |S| = nf.

Formaly, the predicate Q(n) is true for any n:

        Q(n): ∀l ∈ {0, …, n}: R(f, l) ⟹ ∃S((|S| = n) ∧ (∀s ∈ S: f(s) = 0))

-/
theorem thmMain
  (f : ℝ → ℝ) (hf : Continuous f)
  (n : Nat)
  (hn : 1 ≤ n)
  -- (f : ℝ → ℝ) (hf : Continuous f)
  :
  (∀ x : Fin (n + 1), P f x) → ∃ S : Set ℝ, Q S n f := by

  intro h
  simp [Q]

  induction n, hn using Nat.le_induction with
  -- Base Case: n = 1
  | base =>
    rw [show (1 + 1 = 2) by norm_num] at h

    -- Simplify h to: f(0) ≤ -6⁻¹ ∧ 6⁻¹ ≤ f(1)
    unfold P at h
    rw [Fin.forall_fin_two] at h
    simp at h

    -- subst: 6⁻¹ = ⅙
    nth_rw 1 [inv_eq_one_div 6] at h
    rw [neg_div' 6 1] at h
    rw [inv_eq_one_div 6] at h

    -- Finaly, extract lhs and rhs bounds
    have f0le6 : f 0 ≤ -1/6 := h.left
    have f1ge6 : 1/6 ≤ f 1 := h.right

    -- Using IVT, get roots, then put it in a set
    classical
    have rtw := thm2IVT 0 1 f hf f0le6 f1ge6
    -- change (isRoot f ivtw) at ivth

    -- refine ⟨{ivtw}, ?_⟩

    apply Exists.intro
    -- Supply witness
    case w =>
      exact {Exists.choose rtw}
    case h =>

      apply And.intro

      case left =>
        simp

      case right =>
        sorry
        -- simp; exact Exists.choose_spec (rtw)

  | succ k hk ih =>
    rw [show (k + 1 + 1 = k + 2) by norm_num] at h

    -- Obtain set Sₖ₋₁ from I.H.
    have s := (lemma0 (k + 1) hf).mp
    rw [show (k + 1 + 1 = k + 2) by norm_num] at s

    -- Show there is a root somewere in [k, k + 1]
    have hpfkr :=   (s h).right
    have hpfk2  :=  (s h).left
    have pfk1 : P f k := by sorry

    have ihs := ih hpfkr
    have ⟨S, b⟩  := ihs
    have lm := lemma1 f hf k pfk1 hpfk2
    change Q S k f at b

    exact lemma2 f hf k ihs lm



#check Set.ncard_union_eq
