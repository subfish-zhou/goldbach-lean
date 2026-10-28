import WR2ClassicalFourthDataBq
namespace WuPaper.FourthBqInteger
open IntegerLogUpper ClassicalFourthData

def splitUpper (t : ℚ) : ℚ :=
  (ExactRational.logHi ((1+(t-1))/2)+ExactRational.logHi (2*(t-1)/(1+(t-1))))/t

theorem combine (K S A B C D : ℚ) (hS : S ≠ 0) (hC : C ≠ 0) (hD : D ≠ 0) :
    K*4000*(A*D+B*C)/(S*C*D) = K*((A/C+B/D)/(S/4000)) := by
  field_simp [hS,hC,hD]

theorem rawDenominator_pos (i : ℕ) : 0 < BqRawDenominator i := by
  have hC := hiDenominator_pos (show i < 16000+i by omega)
  have hD := hiDenominator_pos (show i < 16000+3*i by omega)
  unfold BqRawDenominator
  exact Nat.mul_pos (Nat.mul_pos (by omega) hC) hD

theorem raw_fraction_eq (i : ℕ) :
    (BqRawNumerator i:ℚ)/(BqRawDenominator i:ℚ) =
      1000000000000000*splitUpper (2+(i:ℚ)/4000) := by
  have h1 := logHi_nat_ratio (show 8000 ≤ 8000+i by omega) (show 0 < (8000:ℕ) by omega)
  have h2 := logHi_nat_ratio (show 8000+i ≤ 8000+2*i by omega) (show 0 < 8000+i by omega)
  rw [show 8000+i-8000=i by omega,show 8000+i+8000=16000+i by omega] at h1
  rw [show 8000+2*i-(8000+i)=i by omega,show 8000+2*i+(8000+i)=16000+3*i by omega] at h2
  have hS : ((8000+i:ℕ):ℚ) ≠ 0 := by positivity
  have hC : (hiDenominator i (16000+i):ℚ) ≠ 0 := by
    exact_mod_cast (hiDenominator_pos (show i<16000+i by omega)).ne'
  have hD : (hiDenominator i (16000+3*i):ℚ) ≠ 0 := by
    exact_mod_cast (hiDenominator_pos (show i<16000+3*i by omega)).ne'
  have harg1 : ((8000+i:ℕ):ℚ)/((8000:ℕ):ℚ) = (1+((2+(i:ℚ)/4000)-1))/2 := by
    push_cast
    ring
  have harg2 : ((8000+2*i:ℕ):ℚ)/((8000+i:ℕ):ℚ) =
      2*((2+(i:ℚ)/4000)-1)/(1+((2+(i:ℚ)/4000)-1)) := by
    have hs : (8000:ℚ)+i ≠ 0 := by simpa only [Nat.cast_add,Nat.cast_ofNat] using hS
    have ht : 1+((2+(i:ℚ)/4000)-1) = (8000+(i:ℚ))/4000 := by ring
    rw [ht]
    push_cast
    field_simp [hs]
    ring
  rw [harg1] at h1
  rw [harg2] at h2
  have ht : (2+(i:ℚ)/4000) = ((8000+i:ℕ):ℚ)/4000 := by push_cast; ring
  unfold splitUpper
  rw [h1,h2,ht]
  simpa only [BqRawNumerator,BqRawDenominator,Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat] using
    combine 1000000000000000 ((8000+i:ℕ):ℚ)
      (hiNumerator i (16000+i):ℚ) (hiNumerator i (16000+3*i):ℚ)
      (hiDenominator i (16000+i):ℚ) (hiDenominator i (16000+3*i):ℚ) hS hC hD

theorem Bq_paid {i : ℕ} (hi : i ≤ 10540) :
    splitUpper (2+(i:ℚ)/4000) ≤ (Bq i:ℚ)/1000000000000000 := by
  simpa only [Bq,if_pos hi,Nat.cast_ofNat] using
    ceil_payment_of_exact (rawDenominator_pos i)
      (show 0 < (1000000000000000:ℕ) by norm_num) (raw_fraction_eq i)

example : Bq 0 = 0 := by decide +kernel
example : Bq 10541 = 0 := by decide +kernel
end WuPaper.FourthBqInteger
#print axioms WuPaper.FourthBqInteger.Bq_paid
