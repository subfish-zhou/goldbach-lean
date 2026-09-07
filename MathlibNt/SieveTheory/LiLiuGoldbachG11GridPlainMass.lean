import MathlibNt.SieveTheory.LiLiuGoldbachG11OrdinaryGridPaid
import MathlibNt.SieveTheory.LiLiuGoldbachG11AnalyticDensity

open Finset
open scoped BigOperators Classical
open Wu2004MeanValue
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
open MathlibNt.SieveTheory.LiLiuPrereqWF
noncomputable section
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- Exact conversion, with the same half-open natural endpoints and no PNT error. -/
theorem goldbachG11PrimeInterval_mass {L U : ℝ} (hLU : L ≤ U) :
    (∑ p ∈ primeSWInterval L U,primeSWBeta p) = realPrimeCount U-realPrimeCount L := by
  change (∑ p ∈ Ioc ⌊L⌋₊ ⌊U⌋₊,if p.Prime then (1 : ℝ) else 0) =
    (∑ p ∈ range (⌊U⌋₊+1),if p.Prime then (1 : ℝ) else 0)-
    (∑ p ∈ range (⌊L⌋₊+1),if p.Prime then (1 : ℝ) else 0)
  rw [Finset.Ioc_eq_Ico]
  exact sum_Ico_eq_sub _ (Nat.succ_le_succ (Nat.floor_le_floor hLU))

def goldbachG11GridPlainMass (N : ℕ) (ε ρ : ℝ) (k : ℕ × ℕ) : ℝ :=
  ∑ v ∈ goldbachG11GridLong N ε ρ k ×ˢ goldbachG11GridShort N ρ k,
    goldbachG11AllPrimeWeight N v

/-- The ordinary pi-center is precisely a finite all-prime rectangle main
term with progression argument m (not m*p). -/
theorem goldbachG11OrdinaryDensityMain_eq_pairs {N : ℕ} {ε ρ δ θ : ℝ}
    (hρ : 1 < ρ) (hρu : ρ ≤ 5/4) (hbig : 4 ≤ (N : ℝ)^(4/53 : ℝ))
    (S : Finset (ℕ × ℕ)) (hS : S ⊆ goldbachG11GridUsed N ε ρ)
    (P : (ℕ × ℕ) → Finset ℕ) (z : (ℕ × ℕ) → ℝ) :
    goldbachG11OrdinaryDensityMain N ε ρ δ θ S P z =
      ∑ k ∈ S, ∑ v ∈ goldbachG11GridLong N ε ρ k ×ˢ goldbachG11GridShort N ρ k,
        goldbachG11AllPrimeWeight N v*externalDensity true (P k)
          (externalInternalLevel (goldbachG11OrdinaryLevel N δ) θ) θ (z k) (progressionDensity v.1) := by
  apply sum_congr rfl
  intro k hk
  have hLU : goldbachG11GridProfileLo N ρ k ≤ goldbachG11GridProfileHi ρ k :=
    (goldbachG11GridPrimeInterval hρ hρu hbig k (hS hk)).lower_le_upper
  rw [← goldbachG11PrimeInterval_mass hLU,sum_product]
  simp only [goldbachG11AllPrimeWeight,mul_sum,sum_mul]
  rfl

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig