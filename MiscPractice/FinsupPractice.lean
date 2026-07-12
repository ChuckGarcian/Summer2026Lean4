import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Finsupp.Single

#check Finsupp

noncomputable def et : ℕ →₀ ℕ := Finsupp.single 3 4

#check (Finsupp.single 3 9).mapRange
