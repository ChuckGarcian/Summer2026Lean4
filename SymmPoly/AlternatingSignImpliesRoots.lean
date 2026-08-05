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

open Set Finset

noncomputable section

open Set

#check intermediate_value_univ₂
#check intermediate_value_univ₂ hf hg
#check intermediate_value_univ₂ hf hg ha hb

/- Example: Let g(x) = 0 and f(x) be a continuous function such that
for some x and y we have that f(x) < g(x) and g(y) < f(y). Then there must
be some value, c ∈ ℝ, such that f(c) = 0.
-/
lemma thm0
  (x y : ℝ)
  (g : ℝ → ℝ) (hg : Continuous g) (hgz : ∀ a, g a = 0)
  (f : ℝ → ℝ) (hf : Continuous f)
  (ha : f x ≤ 0)
  (ha : f x ≤ g x)
  (hb : g y ≤ f y) :
  ∃ x : ℝ, f x = 0 := by

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
theorem thm1
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

/- Example: Let f(x) be a continuous function such that
for some real numbers x and y, we have that f(x) < -⅙ and ⅙ < f(y). Then there must
be some real value, c, such that f(c) = 0.
-/
theorem thm2
  (x y : ℝ)
  (f : ℝ → ℝ)
  (hf : Continuous f)
  (ha : f x ≤ -1/6)
  (hb : 1/6 ≤ f y) :
  ∃ x : ℝ, f x = 0 := by

    -- Reduce the statement to the more general statement at f(x) ≤ 0 and f(x) ≥ 0; this should be trivial -- emphasis on should :(
    have lowerBoundConv : (-1 : ℝ) / 6 ≤ 0 := by norm_num
    have upperBoundConv : (1/6 : ℝ) ≥ 0 := by norm_num
    have h1 : f x ≤ 0 := by exact LE.le.trans ha lowerBoundConv
    have h2 : 0 ≤ f y := by exact Std.IsPreorder.le_trans 0 (1 / 6) (f y) upperBoundConv hb

    -- Theorem one can prove the rest
    apply thm1; repeat' assumption

#eval Finset.range 1

section
  variable (f : ℝ → ℝ) (hf : Continuous f)

  #check ∀ x : Fin 3, (Even x ∧ f x.val ≤ -1/6) ∨ (Odd x.val ∧ f x ≥ 1/6)
end section


def P (f : ℝ → ℝ) (x : Nat) : Prop :=
  (Even x ∧ f x ≤ -(1 / 6 : ℝ)) ∨
  (Odd x ∧ f x ≥ (1 / 6 : ℝ))

def isRoot (f : ℝ → ℝ) (x : ℝ) : Prop := f x = 0

/-

-/
lemma base0
  (f : ℝ → ℝ) (hf : Continuous f)
  :
  (∀ x : Fin (0), P f x) → ∃ s : Finset ℝ, s.card = 0 ∧ ∀ x ∈ s, isRoot f x := by
    intro h

    apply Exists.intro
    -- Witness: ∅
    case w =>
      exact Finset.empty

    -- Witness Proof
    case h =>
      apply And.intro

      -- Prove card(∅) = 0
      case left =>
          trivial

      case right =>
        -- Quanitifer over Emptyset is vacuously true
        have vacuousTrue := Finset.forall_mem_empty_iff (isRoot f)
        apply vacuousTrue.mpr; simp


-- theorem {P : α → Prop} {a : α} {s : Set α} : (∀ x ∈ insert a s, P x) ↔ P a ∧ ∀ x ∈ s, P x
example (k N : Nat) (P : Nat → Prop) : (∀ x ∈ (Finset.range N), P x) ↔ P k ∧ (∀ x ∈ (Finset.range N), P x) := by
-- lemma lemma0 : ∀ x ∈ Finset.range (k + 1), Even x ∧ f ↑x ≤ -1 / 6 ∨ Odd x ∧ f ↑x ≥ 1 / 6 := by sorry

variable (n : Nat)
-- #check Finset.univ (Finset (Fin 3))
#check Finset.range (nP)


  --
/- Quantifer Split -/
lemma lemma0
  (N : ℕ)
  {f : ℝ → ℝ}
  (hf : Continuous f) :
  (∀ x : Fin (N + 1), P f x) ↔ P f (N + 1) ∧ ∀ x : Fin (N), P f x := by sorry

variable (N : Nat)
variable (f : ℝ → ℝ) (hf : Continuous f)

#check base0
#check base0 f
#check base0 f hf
#check (lemma0 N hf)

-- theorem helper1 (α : Type) (P : α → Prop) (B : Prop) (h : ∀ x, P x → B) :
--   (∀ x, P x) → B := by sorry

  -- (expose_names; exact fun a ↦ Nonempty.elim inst fun a_1 ↦ h a_1 (a a_1))
-- example (k : Nat) : (Finset ℝ, s.card = k ∧ ∀ x ∈ s, isRoot f x) ∧ (P f (k + 1)) →
#check Finset.range 3
#check Finset (Fin 3)

#check Finset.map Fin.castSuccEmb (Finset.univ: Finset (Fin N)) ∪ {Fin.last N}
#check Finset.map Fin.castSuccEmb (Finset.univ : Finset (Fin N)) ∪ {Fin.last N}

#check Fin.last N
#check Fin.last N
#check Fin.castSuccEmb N



variable (S : Finset ℝ)

def Q (S : Finset ℝ) (n : Nat) (f : ℝ → ℝ) : Prop := S.card = n ∧ ∀ x ∈ S, isRoot f x

#check Finset.insert_eq
variable (α : Type) (p q : α → Prop)
variable (α : Type) (p q : α → Prop)


example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x := by
  apply Exists.elim h
    (fun w =>
     fun hw : p w ∧ q w =>
     show ∃ x, q x ∧ p x from ⟨w, hw.right, hw.left⟩)


theorem thmMain
  (n : Nat)
  (hn : 1 ≤ n)
  -- (f : ℝ → ℝ) (hf : Continuous f)
  :
  (∀ x : Fin (n + 1), P f x) → ∃ s : Finset ℝ, Q S n f := by

  intro x
  induction n, hn using Nat.le_induction with
  -- Base Case: n = 1
  | base =>

    rw [Q]
    rw [show (1 + 1 = 2) by norm_num] at x

    -- Supply witness and supporting proof
    apply Exists.intro
    case w =>

      unfold P at x
      rw [Fin.forall_fin_two] at x
      simp at x

      nth_rw 1 [inv_eq_one_div 6] at x
      rw [neg_div' 6 1] at x
      rw [inv_eq_one_div 6] at x

      have f0le6 : f 0 ≤ -1/6 := x.left
      have f1ge6 : 1/6 ≤ f 1 := x.right

      -- Obtain witness root and proof of witness
      have whp := thm2 0 1 f hf f0le6 f1ge6
      classical
      exact {Exists.choose whp}

    case h =>
      apply And.intro

        -- Prove card(∅) = 0
      case left =>
            trivial

      case right =>
          -- Quanitifer over Emptyset is vacuously true
          have vacuousTrue := Finset.forall_mem_empty_iff (isRoot f)
          apply vacuousTrue.mpr; simp
      -- have s := base1 f hf x

  | succ =>


    -- Obtain set Sₖ₋₁ from I.H.
    have ihsk := (lemma0 k hf).mp x
    have hfpx := (lemma0 k hf).mp x


    --  hfpx : P f (k + 1) ∧ ∀ (x : Fin k), P f ↑x

    have pL := hfpx.left
    have pR := hfpx.right
    have h : P f k := by sorry


    -- Get the witness set for card k. Now it remains to be shown that the singleton set exists

    -- TODO: Once we get
    have s := hk pR



    -- apply lemma0

    rw [Finset.forall_mem_insert (by decide)] at h2
    sorry


example (p q : Nat → Prop) : (∃ x, p x) → ∃ x, p x ∨ q x := by
  intro h
  cases h with
  | intro x px => exists x; apply Or.inl; exact px
