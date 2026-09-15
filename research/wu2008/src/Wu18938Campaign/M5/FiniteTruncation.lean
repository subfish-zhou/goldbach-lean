import MathlibNt.Wu2008DoubleSieve.SourceCarriers
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

noncomputable section

namespace Wu18938Campaign.M5.FiniteTruncation

open Real Filter Finset Wu2008DoubleSieve
open scoped Classical Topology

def width (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

def window (N : ℕ) (l u : ℝ) : Finset ℕ :=
  primeWindow N ((N : ℝ) ^ l) ((N : ℝ) ^ u)

def pairCount (N : ℕ) (κ l u v w : ℝ) : ℤ :=
  ∑ q ∈ window N v w, ∑ p ∈ window N l u,
    sourceSieveCountLE N (p * q) N ((N : ℝ) ^ κ)

theorem width_pos (n : ℕ) : 0 < width n := by
  unfold width
  positivity

theorem width_tendsto : Tendsto width atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

theorem window_upper_mono {N : ℕ} {l u v : ℝ}
    (hN : 1 ≤ N) (huv : u ≤ v) : window N l u ⊆ window N l v := by
  intro p hp
  obtain ⟨hp, hc, hl, hu⟩ := mem_primeWindow.mp hp
  exact mem_primeWindow.mpr ⟨hp, hc, hl, hu.trans_le
    (rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) huv)⟩

theorem pairCount_upper_mono {N : ℕ} {κ l u v w w' : ℝ}
    (hN : 1 ≤ N) (hww' : w ≤ w') :
    pairCount N κ l u v w ≤ pairCount N κ l u v w' := by
  apply sum_le_sum_of_subset_of_nonneg (window_upper_mono hN hww')
  intro q _ _
  exact sum_nonneg (fun _ _ => Int.natCast_nonneg _)

theorem window_eventually_exact {N : ℕ} (hN : 1 ≤ N) (l w : ℝ) :
    ∀ᶠ n : ℕ in atTop, window N l (w - width n) = window N l w := by
  have hpow : Tendsto (fun n => (N : ℝ) ^ (w - width n)) atTop
      (𝓝 ((N : ℝ) ^ w)) := by
    have hcont : Continuous (fun t : ℝ => (N : ℝ) ^ t) :=
      Real.continuous_const_rpow (by exact_mod_cast (show N ≠ 0 by omega))
    simpa only [sub_zero] using hcont.continuousAt.tendsto.comp
      (tendsto_const_nhds.sub width_tendsto)
  have hp : ∀ p ∈ window N l w,
      ∀ᶠ n : ℕ in atTop, p ∈ window N l (w - width n) := by
    intro p hp
    obtain ⟨hp, hc, hl, hw⟩ := mem_primeWindow.mp hp
    filter_upwards [hpow.eventually (gt_mem_nhds hw)] with n hn
    exact mem_primeWindow.mpr ⟨hp, hc, hl, hn⟩
  filter_upwards [(eventually_all_finset (window N l w)).mpr hp] with n hn
  exact Subset.antisymm (window_upper_mono hN (sub_le_self _ (width_pos n).le)) hn

theorem pairCount_eventually_exact {N : ℕ} (hN : 1 ≤ N) (κ l u v w : ℝ) :
    ∀ᶠ n : ℕ in atTop,
      pairCount N κ l u v (w - width n) = pairCount N κ l u v w := by
  filter_upwards [window_eventually_exact hN v w] with n hn
  simp only [pairCount, hn]

theorem strict_corner_count {N : ℕ} {κ l u v w : ℝ}
    (hN : 1 ≤ N) (hcorner : 2 * u + w = (1 / 2 : ℝ)) :
    (∀ n : ℕ, 2 * u + (w - width n) < (1 / 2 : ℝ) ∧
      pairCount N κ l u v (w - width n) ≤ pairCount N κ l u v w) ∧
    ∀ᶠ n : ℕ in atTop,
      pairCount N κ l u v (w - width n) = pairCount N κ l u v w := by
  refine ⟨?_, pairCount_eventually_exact hN κ l u v w⟩
  intro n
  exact ⟨by linarith [width_pos n],
    pairCount_upper_mono hN (sub_le_self _ (width_pos n).le)⟩

theorem original_ab_strict_count {N : ℕ} (hN : 1 ≤ N) :
    ∀ᶠ n : ℕ in atTop,
      2 * (25 / 206 : ℝ) + (1 / 2 - 2 * (25 / 206) - width n) < 1 / 2 ∧
      2 * (3 * (100 / 1327 : ℝ) / 2) +
        (1 / 2 - 3 * (100 / 1327) - width n) < 1 / 2 ∧
      pairCount N (100 / 1327) (100 / 1327) (25 / 206)
          (25 / 206) (1 / 2 - 2 * (25 / 206) - width n) +
        pairCount N (100 / 1327) (100 / 1327) (3 * (100 / 1327) / 2)
          (1 / 2 - 2 * (25 / 206)) (1 / 2 - 3 * (100 / 1327) - width n) =
      pairCount N (100 / 1327) (100 / 1327) (25 / 206)
          (25 / 206) (1 / 2 - 2 * (25 / 206)) +
        pairCount N (100 / 1327) (100 / 1327) (3 * (100 / 1327) / 2)
          (1 / 2 - 2 * (25 / 206)) (1 / 2 - 3 * (100 / 1327)) := by
  have ha := strict_corner_count (κ := (100 / 1327 : ℝ)) (l := (100 / 1327 : ℝ))
    (u := (25 / 206 : ℝ)) (v := (25 / 206 : ℝ)) (w := 1 / 2 - 2 * (25 / 206 : ℝ))
    hN (by ring)
  have hb := strict_corner_count (κ := (100 / 1327 : ℝ)) (l := (100 / 1327 : ℝ))
    (u := 3 * (100 / 1327 : ℝ) / 2) (v := 1 / 2 - 2 * (25 / 206 : ℝ))
    (w := 1 / 2 - 3 * (100 / 1327 : ℝ)) hN (by ring)
  filter_upwards [ha.2, hb.2] with n han hbn
  exact ⟨(ha.1 n).1, (hb.1 n).1, by rw [han, hbn]⟩

end Wu18938Campaign.M5.FiniteTruncation
