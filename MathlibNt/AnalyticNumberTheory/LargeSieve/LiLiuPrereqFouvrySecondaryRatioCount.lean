import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvrySecondaryGcdMean
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryDivisorMean

/-!
# Counting the secondary frequency-sieve ratio relation

For fixed positive `s`, the equation `h'*s=h*s'` forces `s'` to be a
multiple of `s/gcd(s,h)` and determines `h'` uniquely. In a dyadic `s`
block this pays only `2*gcd(s,h)` partners, not an independent frequency
and sieve-variable box. The resulting collision count is logarithmic.
-/

noncomputable section
open Classical Finset

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

def secondaryRatioPartners (H S h s : ℕ) : Finset (ℕ × ℕ) :=
  (Ioc 0 H ×ˢ Ioc 0 S).filter (fun p => p.1 * s = h * p.2)

theorem secondaryRatio_reduced_dvd {h s h' s' : ℕ} (hs : 0 < s)
    (he : h' * s = h * s') : s / s.gcd h ∣ s' := by
  have hg : 0 < s.gcd h := Nat.gcd_pos_of_pos_left h hs
  have hd : s ∣ h * s' := by rw [← he]; exact dvd_mul_left _ _
  have hd' : s ∣ s.gcd h * s' := by
    simpa only [gcd_eq_nat_gcd] using dvd_gcd_mul_of_dvd_mul hd
  have hsdecomp : s.gcd h * (s / s.gcd h) = s := by
    rw [mul_comm, Nat.div_mul_cancel (Nat.gcd_dvd_left s h)]
  have he' : s.gcd h * (s / s.gcd h) ∣ s.gcd h * s' := by
    rwa [hsdecomp]
  exact (Nat.mul_dvd_mul_iff_left hg).mp he'

theorem secondaryRatioPartners_card_le {h s : ℕ} (hs : 0 < s) (H S : ℕ) :
    (secondaryRatioPartners H S h s).card ≤ S / (s / s.gcd h) := by
  calc
    _ ≤ ((Ioc 0 S).filter (fun t => s / s.gcd h ∣ t)).card := by
      apply card_le_card_of_injOn Prod.snd
      · intro p hp
        obtain ⟨hp, he⟩ := mem_filter.mp hp
        exact mem_filter.mpr ⟨(mem_product.mp hp).2, secondaryRatio_reduced_dvd hs he⟩
      · intro p hp q hq he
        apply Prod.ext _ he
        apply Nat.mul_right_cancel hs
        exact (mem_filter.mp hp).2.trans
          ((congrArg (h * ·) he).trans (mem_filter.mp hq).2.symm)
    _ = _ := Nat.Ioc_filter_dvd_card_eq_div _ _

theorem secondaryRatioPartners_card_le_twice_gcd
    {h s B : ℕ} (hB : 0 < B) (hs : B ≤ s) (H : ℕ) :
    (secondaryRatioPartners H (2 * B) h s).card ≤ 2 * s.gcd h := by
  have hspos := hB.trans_le hs
  have hg : 0 < s.gcd h := Nat.gcd_pos_of_pos_left h hspos
  have hstep : 0 < s / s.gcd h := Nat.div_pos (Nat.gcd_le_left h hspos) hg
  apply (secondaryRatioPartners_card_le hspos H (2 * B)).trans
  apply le_of_mul_le_mul_right (a := s / s.gcd h) _ hstep
  calc
    (2 * B / (s / s.gcd h)) * (s / s.gcd h) ≤ 2 * B := Nat.div_mul_le_self _ _
    _ ≤ 2 * s := Nat.mul_le_mul_left _ hs
    _ = (2 * s.gcd h) * (s / s.gcd h) := by
      rw [mul_assoc, mul_comm (s.gcd h), Nat.div_mul_cancel (Nat.gcd_dvd_left s h)]

theorem sum_pair_gcd_le_log (H S : ℕ) :
    (∑ h ∈ Ioc 0 H, ∑ s ∈ Ioc 0 S, (s.gcd h : ℝ)) ≤
      (H : ℝ) * S * (1 + Real.log H) := by
  calc
    _ ≤ ∑ h ∈ Ioc 0 H, (S : ℝ) * h.divisors.card := by
      apply sum_le_sum
      intro h hh
      exact_mod_cast (show (∑ s ∈ Ioc 0 S, s.gcd h) ≤ S * h.divisors.card from by
        simpa only [Nat.gcd_comm] using sum_gcd_le (mem_Ioc.mp hh).1.ne' S)
    _ = (S : ℝ) * ∑ h ∈ Ioc 0 H, (fouvryTau 2 h : ℝ) := by
      simp only [fouvryTau_two, mul_sum]
    _ ≤ (S : ℝ) * (H * (1 + Real.log H)) :=
      mul_le_mul_of_nonneg_left (by simpa using sum_fouvryTau_le 1 H) (by positivity)
    _ = _ := by ring

/-- Summing over a dyadic first denominator costs only `H*B*log H`.
The partner box has upper endpoints `H,2B`; arbitrary subboxes only decrease
this nonnegative count. No comparison between `H*B` and a beta scale is used. -/
theorem secondaryRatioPartners_dyadic_sum_le {B : ℕ} (hB : 0 < B) (H : ℕ) :
    (∑ h ∈ Ioc 0 H, ∑ s ∈ Ico B (2 * B),
      ((secondaryRatioPartners H (2 * B) h s).card : ℝ)) ≤
        4 * H * B * (1 + Real.log H) := by
  calc
    _ ≤ ∑ h ∈ Ioc 0 H, ∑ s ∈ Ico B (2 * B), 2 * (s.gcd h : ℝ) := by
      apply sum_le_sum
      intro h _
      apply sum_le_sum
      intro s hs
      exact_mod_cast secondaryRatioPartners_card_le_twice_gcd hB (mem_Ico.mp hs).1 H
    _ = 2 * ∑ h ∈ Ioc 0 H, ∑ s ∈ Ico B (2 * B), (s.gcd h : ℝ) := by
      simp only [mul_sum]
    _ ≤ 2 * ∑ h ∈ Ioc 0 H, ∑ s ∈ Ioc 0 (2 * B), (s.gcd h : ℝ) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply sum_le_sum
      intro h _
      apply sum_le_sum_of_subset_of_nonneg
      · intro s hs
        exact mem_Ioc.mpr ⟨hB.trans_le (mem_Ico.mp hs).1, (mem_Ico.mp hs).2.le⟩
      · intro s _ _
        positivity
    _ ≤ 2 * ((H : ℝ) * (2 * B : ℕ) * (1 + Real.log H)) :=
      mul_le_mul_of_nonneg_left (sum_pair_gcd_le_log H (2 * B)) (by norm_num)
    _ = _ := by push_cast; ring

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
