import MathlibNt.SieveTheory.LiLiuGoldbachG12AuthorWeightedTransport

open scoped BigOperators
open Classical Finset LiLiuPrereqBuchstab
noncomputable section
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

theorem goldbachG12WeightedSource_eq_good_add_bad (N : ℕ) (ε : ℝ) (w : ℕ → ℝ) :
    goldbachG12WeightedSource N ε w =
      goldbachG12WeightedGood N ε w + goldbachG12WeightedBad N ε w := by
  unfold goldbachG12WeightedSource goldbachG12WeightedGood goldbachG12WeightedBad
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro m _
  rw [← mul_add]
  congr 1
  simpa only [add_comm] using
    (sum_filter_add_sum_filter_not (goldbachG11LinkedPrimeWindow N ε m)
      (fun r => r ∣ N) w).symm

/-- Only the exceptional prime-divisor part is replaced by a constant weight. -/
theorem goldbachG12WeightedBad_le {N : ℕ} (hN : 4 ≤ N) (ε C : ℝ)
    (hC : 0 ≤ C) (w : ℕ → ℝ) (hw : ∀ r, w r ≤ C) :
    goldbachG12WeightedBad N ε w ≤ C * (21 * N / (N : ℝ)^(4/53 : ℝ)) := by
  calc
    _ ≤ C * goldbachG12MainMassBad N ε := by
      unfold goldbachG12WeightedBad goldbachG12MainMassBad
      rw [mul_sum]
      apply sum_le_sum
      intro m _
      calc
        _ ≤ goldbachG12NormalizedCoefficient N m *
            ∑ _r ∈ (goldbachG11LinkedPrimeWindow N ε m).filter (fun r => r ∣ N), C :=
          mul_le_mul_of_nonneg_left (sum_le_sum (fun r _ => hw r))
            (goldbachG12NormalizedCoefficient_bounds N m).1
        _ = _ := by simp only [sum_const, nsmul_eq_mul]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (goldbachG12MainMassBad_le hN ε) hC

theorem goldbachG12WeightedSource_le_fullRough {N : ℕ} (hN : 4 ≤ N)
    (ε C : ℝ) (hC : 0 ≤ C) (w : ℕ → ℝ)
    (hw : ∀ r, 0 ≤ w r) (hwC : ∀ r, w r ≤ C) :
    400 * goldbachG12WeightedSource N ε w ≤ goldbachG12WeightedRough N w +
      (8400 * C) * N / (N : ℝ)^(4/53 : ℝ) := by
  rw [goldbachG12WeightedSource_eq_good_add_bad, mul_add]
  apply add_le_add (goldbachG12WeightedGood_le_fullRough N ε w hw)
  calc
    _ ≤ 400 * (C * (21 * N / (N : ℝ)^(4/53 : ℝ))) :=
      mul_le_mul_of_nonneg_left (goldbachG12WeightedBad_le hN ε C hC w hwC) (by norm_num)
    _ = _ := by ring

def goldbachG12AuthorPrimeWeight (N r : ℕ) : ℝ :=
  goldbachG11AuthorWeight (Real.log (r : ℝ) / Real.log (N : ℝ))

/-- Author weight retained in the entire good mother; eight occurs only in the error. -/
theorem goldbachG12AuthorSource_le_fullRough {N : ℕ} (hN : 4 ≤ N) (ε : ℝ) :
    400 * goldbachG12WeightedSource N ε (goldbachG12AuthorPrimeWeight N) ≤
      goldbachG12WeightedRough N (goldbachG12AuthorPrimeWeight N) +
        67200 * N / (N : ℝ)^(4/53 : ℝ) := by
  convert goldbachG12WeightedSource_le_fullRough hN ε 8 (by norm_num)
    (goldbachG12AuthorPrimeWeight N) (fun _ => goldbachG11AuthorWeight_nonneg _)
    (fun _ => goldbachG12AuthorWeight_le_eight _) using 1
  norm_num

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
