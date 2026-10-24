import WR2XiRationalTightArithmetic

/-! Rational arithmetic for the original cells entirely above S-2. Analytic comparison is separate. -/
namespace Xi2RationalTop
open Xi2RationalCheck (refined)
open scoped BigOperators

def factors : Fin 4 → Fin 5 → ℚ := ![
  ![6/5, 177/50, 253/100, 19/10, 36/25],
  ![13/10, 7/2, 127/50, 47/25, 143/100],
  ![7/5, 173/50, 257/100, 187/100, 7/5],
  ![3/2, 78/25, 64/25, 191/100, 3/2]]

def massLower : Fin 9 → ℚ := ![
  111258826147199/6000000000000000, 11015108859877/3000000000000000,
  795917363183/200000000000000, 400954892897/93750000000000,
  27380225768713/6000000000000000, 75612009467/15625000000000,
  10208761954023/2000000000000000, 267961103141/50000000000000,
  700494974059/125000000000000]

def target : Fin 4 → Fin 9 → ℚ := ![
  ![154/1000,26/1000,26/1000,26/1000,27/1000,27/1000,27/1000,28/1000,28/1000],
  ![152/1000,25/1000,26/1000,26/1000,26/1000,27/1000,27/1000,27/1000,27/1000],
  ![151/1000,25/1000,25/1000,25/1000,26/1000,26/1000,26/1000,27/1000,27/1000],
  ![154/1000,23/1000,24/1000,25/1000,25/1000,26/1000,26/1000,26/1000,27/1000]]

def left (k : Fin 9) : ℚ := if k = 0 then 1 else (21 + (k.val:ℚ))/10
def right (k : Fin 9) : ℚ := (22 + (k.val:ℚ))/10
def count (r : Fin 4) (k : Fin 9) : ℕ := if r = 1 ∧ k = 5 then 512 else 32
def sigmaCoeff (k : Fin 9) : ℚ := massLower k / (1 - 858467/5000000)
def scalar (r : Fin 4) : ℚ := (∑ j : Fin 5, refined (4 / factors r j)) / 5
def endpoint (r : Fin 4) (k : Fin 9) (m : ℕ) : ℚ :=
  left k + (right k - left k) * m / count r k

def payment (r : Fin 4) (k : Fin 9) (m : ℕ) : ℚ :=
  ((endpoint r k (m+1) - endpoint r k m) / (5 * endpoint r k (m+1))) *
    ∑ j : Fin 5, refined ((endpoint r k m + 1) / factors r j)

def entry (r : Fin 4) (k : Fin 9) : ℚ :=
  sigmaCoeff k * scalar r + ∑ m ∈ Finset.range (count r k), payment r k m

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem other_top_arithmetic : ∀ r k, ¬(r = 1 ∧ k = 5) →
    factors r 1 - 1 ≤ left k → target r k ≤ entry r k := by
  decide +kernel

end Xi2RationalTop
#print axioms Xi2RationalTop.other_top_arithmetic
