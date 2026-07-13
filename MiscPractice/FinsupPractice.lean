import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Finsupp.Single
import Mathlib.Data.List.ToFinsupp
#check Finsupp

-- Create a function with finite support only defined at 3.
noncomputable def finSuppFunc3 : ℕ →₀ ℕ := Finsupp.single 3 4

#check (Finsupp.single 3 9).mapRange

-- Create a list then turn that list into a fintely suppoed function
def myNumbers : List Nat := [1,2,3,4]

#check myNumbers
#print myNumbers

def myListFinsup := myNumbers.toFinsupp

-- List should be the defined on the support
#eval myListFinsup 2
#eval myNumbers.toFinsupp 2
