import MathlibNt.SieveTheory.LiLiuGoldbachG11AllPrimeRectangle
import MathlibNt.SieveTheory.LiLiuGoldbachG11OrdinaryAPWindow
import MathlibNt.SieveTheory.LiLiuGoldbachG11OrdinaryGridSource

open Finset
open scoped BigOperators Classical
open Wu2004MeanValue AnalyticNumberTheory.Sieve
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
open MathlibNt.SieveTheory.LiLiuPrereqWF
noncomputable section
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- The ordinary source's literal pi-centered main term. Only the long
coefficient is filtered by coprimality with d; no short-prime gate is invented. -/
def goldbachG11OrdinaryCenter (N : ℕ) (S : Finset ℕ) (L U : ℝ) (d : ℕ) : ℝ :=
  ∑ m ∈ S, if m.Coprime d then
    (goldbachG11ProductCoefficient N ((N : ℝ)^(4/53 : ℝ))
      ((N : ℝ)^(4/33 : ℝ)) m : ℝ)*((realPrimeCount U-realPrimeCount L)/(d.totient : ℝ)) else 0

/-- Exact actual divisibility count minus the original prime-count main term
is the two-prefix residual. Inverse residues, zero and negative overhang survive. -/
theorem goldbachG11OrdinaryDivCount_centered (N d : ℕ) (S : Finset ℕ) (L U : ℝ)
    (hS : ∀ m ∈ S, 0 < m) (hL : 0 ≤ L) (hLU : L ≤ U) (hNd : N.Coprime d) :
    weightedDivCount (S ×ˢ primeSWInterval L U)
      (fun v : ℕ × ℕ => ((N : ℤ)-(v.1 : ℤ)*v.2).natAbs) (goldbachG11AllPrimeWeight N) d -
      goldbachG11OrdinaryCenter N S L U d =
    primeCenteredAPSum S
      (fun m => (goldbachG11ProductCoefficient N ((N : ℝ)^(4/53 : ℝ))
        ((N : ℝ)^(4/33 : ℝ)) m : ℝ)) (fun _ => U) d N -
    primeCenteredAPSum S
      (fun m => (goldbachG11ProductCoefficient N ((N : ℝ)^(4/53 : ℝ))
        ((N : ℝ)^(4/33 : ℝ)) m : ℝ)) (fun _ => L) d N := by
  have hU := hL.trans hLU
  have hsum : weightedDivCount (S ×ˢ primeSWInterval L U)
      (fun v : ℕ × ℕ => ((N : ℤ)-(v.1 : ℤ)*v.2).natAbs) (goldbachG11AllPrimeWeight N) d =
      ∑ m ∈ S, (goldbachG11ProductCoefficient N ((N : ℝ)^(4/53 : ℝ))
        ((N : ℝ)^(4/33 : ℝ)) m : ℝ)*((goldbachG11OrdinaryAPWindow N m L U d).card : ℝ) := by
    unfold weightedDivCount
    rw [sum_product]
    apply sum_congr rfl
    intro m _
    rw [← goldbachG11OrdinaryAPWindow_row]
    simp only [goldbachG11AllPrimeWeight,mul_sum,mul_ite,mul_one,mul_zero]
  rw [hsum,primeCenteredAPSum_eq_inverse _ _ _ _ _ hS (fun _ _ => hU),
    primeCenteredAPSum_eq_inverse _ _ _ _ _ hS (fun _ _ => hL)]
  unfold goldbachG11OrdinaryCenter
  rw [← sum_sub_distrib,← sum_sub_distrib]
  apply sum_congr rfl
  intro m hm
  by_cases hmd : m.Coprime d
  · simp only [if_pos hmd]
    rw [goldbachG11OrdinaryAPWindow_card_inverse N m d (hS m hm) hL hLU hmd]
    ring
  · simp only [if_neg hmd,goldbachG11OrdinaryAPWindow_empty_of_not_coprime N m d L U hNd hmd,
      card_empty,Nat.cast_zero,mul_zero,sub_zero]

/-- Specialize the exact identity to the same occupied G11 grid consumed by
ordinary distribution; there is no conditional count or residue adapter left. -/
theorem goldbachG11OrdinaryGrid_centered_eq {N : ℕ} {ε ρ : ℝ}
    (hρ : 1 < ρ) (hρu : ρ ≤ 5/4) (hbig : 4 ≤ (N : ℝ)^(4/53 : ℝ))
    {k : ℕ × ℕ} (hk : k ∈ goldbachG11GridUsed N ε ρ) (d : ℕ) (hNd : N.Coprime d) :
    weightedDivCount (goldbachG11GridLong N ε ρ k ×ˢ goldbachG11GridShort N ρ k)
      (fun v : ℕ × ℕ => ((N : ℤ)-(v.1 : ℤ)*v.2).natAbs) (goldbachG11AllPrimeWeight N) d -
      goldbachG11OrdinaryCenter N (goldbachG11GridLong N ε ρ k)
        (goldbachG11GridProfileLo N ρ k) (goldbachG11GridProfileHi ρ k) d =
      goldbachG11OrdinaryRectangleResidual N ε ρ k d N := by
  let z := goldbachG11GridPrimeInterval hρ hρu hbig k hk
  have hL : 0 ≤ goldbachG11GridProfileLo N ρ k :=
    (zero_le_one.trans z.one_le_scale).trans z.scale_le_lower
  have hLU : goldbachG11GridProfileLo N ρ k ≤ goldbachG11GridProfileHi ρ k := z.lower_le_upper
  have hS : ∀ m ∈ goldbachG11GridLong N ε ρ k, 0 < m := by
    intro m hm
    exact (goldbachG11ProductSupport_data (mem_filter.mp (mem_filter.mp hm).1).1).1
  simpa only [goldbachG11GridShort_eq_profiles,goldbachG11OrdinaryRectangleResidual] using
    goldbachG11OrdinaryDivCount_centered N d (goldbachG11GridLong N ε ρ k)
      (goldbachG11GridProfileLo N ρ k) (goldbachG11GridProfileHi ρ k) hS hL hLU hNd

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig