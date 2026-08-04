import Mathlib.Topology.Defs.Basic
import Mathlib.Topology.UniformSpace.Real
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Continuous
import Mathlib.Data.Finset.Range
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.Group.Even

open Set Finset

noncomputable section

open Set

def isRoot (f : ℝ → ℝ) (x : ℝ) : Prop := f x = 0

#check intermediate_value_univ₂
#check intermediate_value_univ₂ hf hg
#check intermediate_value_univ₂ hf hg ha hb

/- Example: Let the g(x) = 0 and f(x) be a continous function such that
for some x and y we have that f(x) < g(x) and g(y) < f(y). Then there must
be some value, c ∈ ℝ, such that f(c) = 0.
-/
lemma thm0
  (x y : ℝ)
  (g : ℝ → ℝ) (hg : Continuous g) (hgz : ∀ a, g a = 0)
  (f : ℝ → ℝ ) (hf : Continuous f)
  (ha : f x ≤ 0)
  (ha  : f x ≤ g x)
  (hb  : g y ≤ f y)     :
  ∃ x  : ℝ, f x = 0:= by

    -- Use special case of intermediate value theorem
    -- Obtain proof of root exists using IVU
    obtain ⟨w, h⟩ := intermediate_value_univ₂ hf hg ha hb

    -- IVU gives witness in terms of the zero function, g. So we rewrite in terms of 0 ∈ ℝ
    rw [hgz w] at h
    apply Exists.intro
    exact h

def zeroFunc : ℝ → ℝ := fun _ => 0

/- Example: Let f(x) be a continous function such that
for some x and y we have that f(x) < 0 and 0 < f(y). Then there must
be some value, c ∈ ℝ, such that f(c) = 0.
-/
theorem thm1
  (x y : ℝ)
  (f : ℝ → ℝ) (hf : Continuous f)
  (ha : f x ≤ 0)
  (hb : 0 ≤ f y) :
  ∃ x : ℝ, f x = 0 := by

    -- Rewerite 0 constants as zero function: g(y) = 0, y ∈ ℝ
    change f x ≤ zeroFunc x at ha
    change zeroFunc y ≤ f y at hb

    -- Certicate showing zerofunction is continous and always equal to zero
    have hg : Continuous zeroFunc := by exact continuous_of_const fun x ↦ congrFun rfl
    have hgz : ∀ l, zeroFunc l = 0 := by exact fun l ↦ Real.ext_cauchy rfl

    -- Reduced to thm0 case
    apply thm0; repeat' assumption



#check LE.le.trans

/- Example: Let f(x) be a continous function such that
for some real numbers x and y, we have that f(x) < -⅙ and ⅙ < f(y). Then there must
be some real value, c, such that f(c) = 0.
-/
theorem thm2
  (x y : ℝ)
  (f : ℝ → ℝ)
  (hf : Continuous f)
  (ha : f x ≤ -1/6)
  (hb: 1/6 ≤ f y) :
  ∃ x : ℝ, f x = 0 := by

    -- Reduce statement as the more general statement at f(x) ≤ 0 and f(x) ≥ 0; This should be trivial -- emphasis on should :(
    have lowerBoundConv : (-1 : ℝ) / 6 ≤ 0 := by norm_num
    have upperBoundConv : (1/6 : ℝ) ≥ 0  := by norm_num
    have h1 : f x  ≤ 0 := by exact LE.le.trans ha lowerBoundConv
    have h2 :  0 ≤ f y := by exact Std.IsPreorder.le_trans 0 (1 / 6) (f y) upperBoundConv hb

    -- Thoerem one can prove the rest
    apply thm1; repeat' assumption

#eval Finset.range 2

section
variable (f : ℝ → ℝ) (hf : Continuous f)
#check ∀ x ∈ Finset.range 2, (Even x ∧ f x ≤ -1/6) ∨ (Odd x ∧ f x ≥ 1/6)
end section

example
  (f : ℝ → ℝ) (hf : Continuous f)
  (h2 :  ∀ x ∈ Finset.range 2, (Even x ∧ f x ≤ -1/6) ∨ (Odd x ∧ f x ≥ 1/6)) :
  ∃ s : Finset ℝ, s.card = 2 ∧ ∀ x ∈ s, isRoot f x := by
  
