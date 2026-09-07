import MathlibNt.SieveTheory.LiLiuGoldbachG11LinkedWindow
import MathlibNt.Wu2004MeanValue.RealEndpoints

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
open Wu2004MeanValue AnalyticNumberTheory.Sieve

/-- Actual prime-r window with the coupled product congruence, before sieving the output. -/
noncomputable def goldbachG11LinkedAPWindow (N : ℕ) (ε : ℝ) (m d b : ℕ) : Finset ℕ :=
  (goldbachG11LinkedPrimeWindow N ε m).filter (fun r => m*r ≡ b [MOD d])

theorem goldbachG11LinkedAPWindow_eq_sdiff {N m : ℕ} {ε : ℝ} (d b : ℕ)
    (hN : 2 ≤ N) (hm : m ∈ goldbachG11EffectiveProductSupport N ε) :
    goldbachG11LinkedAPWindow N ε m d b =
      scaledPrimeSet ((m : ℝ)*goldbachG11PiLiHi N m) d b m \
        scaledPrimeSet ((m : ℝ)*goldbachG11PiLiLo N ε m) d b m := by
  classical
  have hs := (Finset.mem_filter.mp hm).1
  have hm0 := (goldbachG11ProductSupport_data hs).1
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
  obtain ⟨hzlo, hlh, hhiN⟩ := goldbachG11PiLiEndpoints_bounds hN hm
  have hlo0 : 0 ≤ goldbachG11PiLiLo N ε m :=
    (Real.rpow_nonneg (Nat.cast_nonneg N) _).trans hzlo
  have hhi0 := hlo0.trans hlh
  ext r
  simp only [goldbachG11LinkedAPWindow, goldbachG11LinkedPrimeWindow,
    Finset.mem_filter, Finset.mem_range, Finset.mem_sdiff,
    mem_scaledPrimeSet (mul_nonneg hmR.le hhi0) hm0,
    mem_scaledPrimeSet (mul_nonneg hmR.le hlo0) hm0]
  constructor
  · rintro ⟨⟨_, hp, hl, hh⟩, hc⟩
    refine ⟨⟨hp, mul_le_mul_of_nonneg_left hh hmR.le, hc⟩, ?_⟩
    rintro ⟨_, hbad, _⟩
    have := mul_lt_mul_of_pos_left hl hmR
    linarith
  · rintro ⟨⟨hp, hh, hc⟩, hnlo⟩
    have hlprod : (m : ℝ)*goldbachG11PiLiLo N ε m < (m : ℝ)*r := by
      by_contra h
      exact hnlo ⟨hp, le_of_not_gt h, hc⟩
    have hl : goldbachG11PiLiLo N ε m < (r : ℝ) := by nlinarith
    have hhr : (r : ℝ) ≤ goldbachG11PiLiHi N m := by nlinarith
    have hrm : (r : ℝ)*(m : ℝ) ≤ N := (le_div_iff₀ hmR).mp (hhr.trans hhiN)
    have hrmN : r*m ≤ N := by exact_mod_cast hrm
    have hrN : r ≤ N := by
      nlinarith [Nat.mul_le_mul_left r (show 1 ≤ m by omega)]
    exact ⟨⟨Nat.lt_succ_of_le hrN, hp, hl, hhr⟩, hc⟩

/-- Exact count difference, retaining the closed high endpoint and inverse residue. -/
theorem goldbachG11LinkedAPWindow_card_eq_inverse {N m : ℕ} {ε : ℝ} (d b : ℕ)
    (hN : 2 ≤ N) (hm : m ∈ goldbachG11EffectiveProductSupport N ε)
    (hmd : m.Coprime d) :
    ((goldbachG11LinkedAPWindow N ε m d b).card : ℝ) =
      (primesInAP ⌊goldbachG11PiLiHi N m⌋₊ d (natInvMod d m*b % d) : ℝ) -
        primesInAP ⌊goldbachG11PiLiLo N ε m⌋₊ d (natInvMod d m*b % d) := by
  have hs := (Finset.mem_filter.mp hm).1
  have hm0 := (goldbachG11ProductSupport_data hs).1
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
  obtain ⟨hzlo, hlh, _⟩ := goldbachG11PiLiEndpoints_bounds hN hm
  have hlo0 : 0 ≤ goldbachG11PiLiLo N ε m :=
    (Real.rpow_nonneg (Nat.cast_nonneg N) _).trans hzlo
  have hhi0 := hlo0.trans hlh
  have hsub : scaledPrimeSet ((m : ℝ)*goldbachG11PiLiLo N ε m) d b m ⊆
      scaledPrimeSet ((m : ℝ)*goldbachG11PiLiHi N m) d b m := by
    intro r hr
    rw [mem_scaledPrimeSet (mul_nonneg hmR.le hlo0) hm0] at hr
    rw [mem_scaledPrimeSet (mul_nonneg hmR.le hhi0) hm0]
    exact ⟨hr.1, hr.2.1.trans (mul_le_mul_of_nonneg_left hlh hmR.le), hr.2.2⟩
  rw [goldbachG11LinkedAPWindow_eq_sdiff d b hN hm,
    Finset.card_sdiff_of_subset hsub, Nat.cast_sub (Finset.card_le_card hsub)]
  change (scaledPrimeCount _ d b m : ℝ) - scaledPrimeCount _ d b m = _
  rw [scaledPrimeCount_eq_inverse _ d b m (mul_nonneg hmR.le hhi0) hm0 hmd,
    scaledPrimeCount_eq_inverse _ d b m (mul_nonneg hmR.le hlo0) hm0 hmd]
  simp only [mul_div_cancel_left₀ _ (ne_of_gt hmR)]

theorem goldbachG11LinkedPrimeWindow_product_le {N m r : ℕ} {ε : ℝ}
    (hm : m ∈ goldbachG11EffectiveProductSupport N ε)
    (hr : r ∈ goldbachG11LinkedPrimeWindow N ε m) : r*m ≤ N := by
  have hs := (Finset.mem_filter.mp hm).1
  have hmR : (0 : ℝ) < m := by
    exact_mod_cast (goldbachG11ProductSupport_data hs).1
  have hhi := (Finset.mem_filter.mp hr).2.2.2
  have hn := (le_div_iff₀ hmR).mp ((min_le_right _ _).trans' hhi)
  exact_mod_cast hn

/-- On the geometric mother, the actual output is positive, not truncated to zero. -/
theorem goldbachG11LinkedPrimeWindow_output_pos {N m r : ℕ} {ε : ℝ}
    (hm : m ∈ goldbachG11EffectiveProductSupport N ε)
    (hr : r ∈ goldbachG11LinkedPrimeWindow N ε m) : 0 < N-r*m := by
  have hs := (Finset.mem_filter.mp hm).1
  exact Nat.sub_pos_of_lt ((goldbachG11_product_upper_cutoff_iff hs r).mpr
    (goldbachG11LinkedPrimeWindow_product_le hm hr))

/-- The progression counted by the source is literally divisibility of the output. -/
theorem goldbachG11LinkedAPWindow_eq_output_dvd {N m : ℕ} {ε : ℝ} (d : ℕ)
    (hm : m ∈ goldbachG11EffectiveProductSupport N ε) :
    goldbachG11LinkedAPWindow N ε m d N =
      (goldbachG11LinkedPrimeWindow N ε m).filter (fun r => d ∣ N-r*m) := by
  classical
  ext r
  simp only [goldbachG11LinkedAPWindow, Finset.mem_filter]
  apply and_congr_right
  intro hr
  rw [Nat.mul_comm m r, Nat.modEq_iff_dvd'
    (goldbachG11LinkedPrimeWindow_product_le hm hr)]

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig