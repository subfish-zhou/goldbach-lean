import MathlibNt.SieveTheory.LiLiuGoldbachG11ProductGrouping
import MathlibNt.SieveTheory.LiLiuFouvryG9SmallOutputPrime
import MathlibNt.SieveTheory.LiLiuGoldbachG11FouvryRectangle

open Finset Filter
open scoped BigOperators Classical
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
open MathlibNt.SieveTheory.LiLiuPrereqWF

noncomputable section
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

def goldbachG11RectangleWeight (N : ℕ) (v : ℕ × ℕ) : ℝ :=
  (goldbachG11ProductCoefficient N ((N : ℝ)^(4/53 : ℝ))
    ((N : ℝ)^(4/33 : ℝ)) v.1 : ℝ)*
    (if v.2.Coprime N then primeSWBeta v.2 else 0)

theorem goldbachG11RectangleWeight_nonneg (N : ℕ) (v : ℕ × ℕ) :
    0 ≤ goldbachG11RectangleWeight N v := by
  unfold goldbachG11RectangleWeight
  apply mul_nonneg (Nat.cast_nonneg _)
  dsimp [primeSWBeta]
  split_ifs <;> norm_num

/-- The original first-prime fibre, merely restricted to a rectangle. -/
def goldbachG11RectangleMotherCount (N : ℕ) (ε : ℝ) (U V : Finset ℕ) : ℝ :=
  ∑ m ∈ U, (goldbachG11ProductCoefficient N ((N : ℝ)^(4/53 : ℝ))
    ((N : ℝ)^(4/33 : ℝ)) m : ℝ)*
    ((goldbachG11ProductFirstPrimeFiber N ε ((N : ℝ)^(4/53 : ℝ)) m).filter
      (fun p => p ∈ V)).card

/-- Positive rectangular enlargement, retaining all coefficient multiplicities. -/
def goldbachG11RectanglePrimeMass (N : ℕ) (U V : Finset ℕ) : ℝ :=
  ∑ v ∈ U ×ˢ V, goldbachG11RectangleWeight N v *
    (if ((N : ℤ)-(v.1 : ℤ)*v.2).natAbs.Prime then 1 else 0)

def goldbachG11RectangleSiftedMass (N : ℕ) (U V P : Finset ℕ) : ℝ :=
  weightedSequenceSifted (U ×ˢ V) (fun v : ℕ × ℕ => ((N : ℤ)-(v.1 : ℤ)*v.2).natAbs)
    (goldbachG11RectangleWeight N) P

/-- Includes zero and all outputs below the real cutoff; no injectivity is presumed. -/
def goldbachG11RectangleSmallMass (N : ℕ) (U V : Finset ℕ) (z : ℝ) : ℝ :=
  ∑ v ∈ U ×ˢ V, goldbachG11RectangleWeight N v *
    (if (((N : ℤ)-(v.1 : ℤ)*v.2).natAbs : ℝ) < z then 1 else 0)

/-- Actual prime-output fibres embed into the overhanging rectangle by positivity. -/
theorem goldbachG11RectangleMotherCount_le_primeMass (N : ℕ) (ε : ℝ)
    (U V : Finset ℕ) :
    goldbachG11RectangleMotherCount N ε U V ≤ goldbachG11RectanglePrimeMass N U V := by
  unfold goldbachG11RectangleMotherCount goldbachG11RectanglePrimeMass
  rw [sum_product]
  apply sum_le_sum
  intro m _hm
  let F := (goldbachG11ProductFirstPrimeFiber N ε ((N : ℝ)^(4/53 : ℝ)) m).filter
    (fun p => p ∈ V)
  have hF : F ⊆ V := fun p hp => (mem_filter.mp hp).2
  have hrow : (F.card : ℝ) ≤ ∑ p ∈ V,
      (if p.Coprime N then primeSWBeta p else 0)*
        (if ((N : ℤ)-(m : ℤ)*p).natAbs.Prime then 1 else 0) := by
    calc
      _ = ∑ p ∈ F, (if p.Coprime N then primeSWBeta p else 0)*
          (if ((N : ℤ)-(m : ℤ)*p).natAbs.Prime then 1 else 0) := by
        have hcard : (F.card : ℝ) = ∑ _p ∈ F, (1 : ℝ) := by simp
        rw [hcard]
        apply sum_congr rfl
        intro p hpF
        obtain ⟨hp, hpN, _hz, _hmin, _hε, hprod, hout⟩ :=
          mem_goldbachG11ProductFirstPrimeFiber_iff.mp (mem_filter.mp hpF).1
        have hc := hp.coprime_iff_not_dvd.mpr hpN
        have ha : ((N : ℤ)-(m : ℤ)*p).natAbs.Prime := by
          rw [g9IntegerFibre_original N m p (by simpa [Nat.mul_comm] using hprod.le)]
          simpa [Nat.mul_comm] using hout
        simp [hc, primeSWBeta, hp, ha]
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg hF (fun p _hp _ => by
        dsimp [primeSWBeta]
        split_ifs <;> positivity)
  have h := mul_le_mul_of_nonneg_left hrow (show
      0 ≤ (goldbachG11ProductCoefficient N ((N : ℝ)^(4/53 : ℝ))
        ((N : ℝ)^(4/33 : ℝ)) m : ℝ) from Nat.cast_nonneg _)
  simpa only [mul_sum, goldbachG11RectangleWeight, mul_assoc] using h

/-- Prime outputs below the actual cutoff remain explicitly charged. -/
theorem goldbachG11RectanglePrimeMass_le_sifted_add_small (N : ℕ)
    (U V : Finset ℕ) (z : ℝ) :
    goldbachG11RectanglePrimeMass N U V ≤
      goldbachG11RectangleSiftedMass N U V (fouvryG9SievePrimes N z) +
        goldbachG11RectangleSmallMass N U V z := by
  unfold goldbachG11RectanglePrimeMass goldbachG11RectangleSiftedMass
    goldbachG11RectangleSmallMass weightedSequenceSifted
  rw [← sum_add_distrib]
  apply sum_le_sum
  intro v _hv
  have h := mul_le_mul_of_nonneg_left
    (fouvryG9PrimeOutput_indicator N ((N : ℤ)-(v.1 : ℤ)*v.2).natAbs z)
    (goldbachG11RectangleWeight_nonneg N v)
  simpa only [mul_add, mul_ite, mul_one, mul_zero] using h

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig