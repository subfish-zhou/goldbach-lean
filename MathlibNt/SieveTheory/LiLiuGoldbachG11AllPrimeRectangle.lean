import MathlibNt.SieveTheory.LiLiuGoldbachG11RectangleCount

open Finset
open scoped BigOperators Classical
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
open MathlibNt.SieveTheory.LiLiuPrereqWF
noncomputable section
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- Nonnegative high-band envelope: only the short-prime copN filter is dropped.
The original long labelled coefficient is unchanged. -/
def goldbachG11AllPrimeWeight (N : ℕ) (v : ℕ × ℕ) : ℝ :=
  (goldbachG11ProductCoefficient N ((N : ℝ)^(4/53 : ℝ))
    ((N : ℝ)^(4/33 : ℝ)) v.1 : ℝ)*primeSWBeta v.2

def goldbachG11AllPrimeMass (N : ℕ) (U V : Finset ℕ) : ℝ :=
  ∑ v ∈ U ×ˢ V, goldbachG11AllPrimeWeight N v*
    (if ((N : ℤ)-(v.1 : ℤ)*v.2).natAbs.Prime then 1 else 0)

def goldbachG11AllPrimeSiftedMass (N : ℕ) (U V P : Finset ℕ) : ℝ :=
  weightedSequenceSifted (U ×ˢ V) (fun v : ℕ × ℕ => ((N : ℤ)-(v.1 : ℤ)*v.2).natAbs)
    (goldbachG11AllPrimeWeight N) P

def goldbachG11AllPrimeSmallMass (N : ℕ) (U V : Finset ℕ) (z : ℝ) : ℝ :=
  ∑ v ∈ U ×ˢ V, goldbachG11AllPrimeWeight N v*
    (if (((N : ℤ)-(v.1 : ℤ)*v.2).natAbs : ℝ) < z then 1 else 0)

theorem goldbachG11AllPrimeWeight_nonneg (N : ℕ) (v : ℕ × ℕ) :
    0 ≤ goldbachG11AllPrimeWeight N v := by
  apply mul_nonneg (Nat.cast_nonneg _)
  unfold primeSWBeta
  split_ifs <;> norm_num

theorem goldbachG11RectangleWeight_le_allPrime (N : ℕ) (v : ℕ × ℕ) :
    goldbachG11RectangleWeight N v ≤ goldbachG11AllPrimeWeight N v := by
  by_cases h : v.2.Coprime N
  · simpa only [goldbachG11RectangleWeight,goldbachG11AllPrimeWeight,if_pos h] using
      (le_refl (goldbachG11AllPrimeWeight N v))
  · simpa only [goldbachG11RectangleWeight,if_neg h,mul_zero] using goldbachG11AllPrimeWeight_nonneg N v

/-- The high envelope is explicitly an upper bound on the unchanged actual count. -/
theorem goldbachG11RectanglePrimeMass_le_allPrime (N : ℕ) (U V : Finset ℕ) :
    goldbachG11RectanglePrimeMass N U V ≤ goldbachG11AllPrimeMass N U V := by
  apply sum_le_sum
  intro v _
  exact mul_le_mul_of_nonneg_right (goldbachG11RectangleWeight_le_allPrime N v)
    (by split_ifs <;> norm_num)

theorem goldbachG11AllPrimeMass_le_sifted_add_small (N : ℕ) (U V : Finset ℕ) (z : ℝ) :
    goldbachG11AllPrimeMass N U V ≤
      goldbachG11AllPrimeSiftedMass N U V (fouvryG9SievePrimes N z)+
        goldbachG11AllPrimeSmallMass N U V z := by
  unfold goldbachG11AllPrimeMass goldbachG11AllPrimeSiftedMass
    goldbachG11AllPrimeSmallMass weightedSequenceSifted
  rw [← sum_add_distrib]
  apply sum_le_sum
  intro v _
  have h := mul_le_mul_of_nonneg_left
    (fouvryG9PrimeOutput_indicator N ((N : ℤ)-(v.1 : ℤ)*v.2).natAbs z)
    (goldbachG11AllPrimeWeight_nonneg N v)
  simpa only [mul_add,mul_ite,mul_one,mul_zero] using h

/-- Drop the short copN filter only in the sifted term, not in the small-output budget. -/
theorem goldbachG11RectangleSiftedMass_le_allPrime (N : ℕ) (U V P : Finset ℕ) :
    goldbachG11RectangleSiftedMass N U V P ≤ goldbachG11AllPrimeSiftedMass N U V P := by
  apply sum_le_sum
  intro v _
  exact mul_le_mul_of_nonneg_right (goldbachG11RectangleWeight_le_allPrime N v)
    (by split_ifs <;> norm_num)

/-- The already paid original small-output term suffices for the high envelope. -/
theorem goldbachG11RectanglePrimeMass_le_allPrime_sifted_add_small
    (N : ℕ) (U V : Finset ℕ) (z : ℝ) :
    goldbachG11RectanglePrimeMass N U V ≤
      goldbachG11AllPrimeSiftedMass N U V (fouvryG9SievePrimes N z)+
        goldbachG11RectangleSmallMass N U V z := by
  exact (goldbachG11RectanglePrimeMass_le_sifted_add_small N U V z).trans
    (add_le_add (goldbachG11RectangleSiftedMass_le_allPrime N U V _) (le_refl _))

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig