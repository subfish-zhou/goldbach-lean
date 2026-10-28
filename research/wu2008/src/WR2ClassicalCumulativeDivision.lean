import WR2ClassicalCumulativePayment
import Mathlib.Tactic.Linarith

namespace WuPaper.ClassicalCumulativeDivision
open ClassicalCumulativeTable

def ceilDiv (n d : ℕ) : ℕ := (n+d-1)/d

def quotient (q : ℕ → ℕ) (base i : ℕ) : ℕ := ceilDiv (4000*q i) (base+i)

theorem ceilDiv_paid (n d : ℕ) (hd : 0 < d) : n ≤ d*ceilDiv n d := by
  have hm := Nat.mod_lt (n+d-1) hd
  have he := Nat.div_add_mod (n+d-1) d
  unfold ceilDiv
  omega

theorem quotient_paid (q : ℕ → ℕ) (base i : ℕ) (hm : 0 < base+i) :
    4000*q i ≤ (base+i)*quotient q base i := ceilDiv_paid _ _ hm

/-- Multiplying the rounded endpoint bounds shows that they pay the exact divided values. -/
theorem divided_step_paid (q : ℕ → ℕ) (base E i p : ℕ) (hm : 0 < base+i) :
    let m := base+i
    6*4000^3*m*(m+1)*p+
      3*4000^3*((m+1)*q i+m*q (i+1))+E*1000000000000000*m*(m+1) ≤
        6*4000^3*m*(m+1)*(p+increment (quotient q base) E i) := by
  dsimp only
  have h0 := quotient_paid q base i hm
  have h1 := quotient_paid q base (i+1) (by omega)
  have h0' := Nat.mul_le_mul_left (base+i+1) h0
  have h1' := Nat.mul_le_mul_left (base+i) h1
  have hs := increment_payment (quotient q base) E i
  have hs' := Nat.mul_le_mul_left ((base+i)*(base+i+1)) hs
  nlinarith only [h0',h1',hs']

theorem divided_table_paid (q : ℕ → ℕ) (base E : ℕ) (anchor : ℕ → ℕ) {i : ℕ}
    (hi : i < 10540) (hb : i%4 ≠ 3) (hm : 0 < base+i) :
    let m := base+i
    6*4000^3*m*(m+1)*table (quotient q base) E anchor i+
      3*4000^3*((m+1)*q i+m*q (i+1))+E*1000000000000000*m*(m+1) ≤
        6*4000^3*m*(m+1)*table (quotient q base) E anchor (i+1) := by
  dsimp only
  rw [table_succ (quotient q base) E anchor hi hb]
  exact divided_step_paid q base E i _ hm

end WuPaper.ClassicalCumulativeDivision
#print axioms WuPaper.ClassicalCumulativeDivision.divided_step_paid
