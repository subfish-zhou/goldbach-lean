import WR2SixthCountCarriers

noncomputable section

namespace Wu18938Campaign.M5

open Real Filter Finset WuPaper.R2SixthCount
open scoped Classical Topology

def cornerWidth (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

def cornerCountA (N n : ℕ) : ℤ :=
  rectangleCount N alpha beta beta (aCeiling - cornerWidth n)

def cornerCountB (N n : ℕ) : ℤ :=
  rectangleCount N alpha bCut aCeiling (sigma - cornerWidth n)

theorem cornerWidth_pos (n : ℕ) : 0 < cornerWidth n := by
  unfold cornerWidth
  positivity

theorem cornerWidth_tendsto : Tendsto cornerWidth atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

theorem corner_strict (n : ℕ) :
    2 * beta + (aCeiling - cornerWidth n) < (1 / 2 : ℝ) ∧
      2 * bCut + (sigma - cornerWidth n) < (1 / 2 : ℝ) := by
  have h := strict_corner_equalities
  have hp := cornerWidth_pos n
  constructor <;> linarith

theorem corner_common_slack {n : ℕ} {δ : ℝ} (hδ : δ ≤ cornerWidth n) :
    2 * beta + (aCeiling - cornerWidth n) ≤ (1 / 2 : ℝ) - δ ∧
      2 * bCut + (sigma - cornerWidth n) ≤ (1 / 2 : ℝ) - δ := by
  have h := strict_corner_equalities
  constructor <;> linarith

theorem window_upper_mono {N : ℕ} {l u v : ℝ}
    (hN : 1 ≤ N) (huv : u ≤ v) : window N l u ⊆ window N l v := by
  intro p hp
  obtain ⟨hp, hc, hl, hu⟩ := mem_window.mp hp
  exact mem_window.mpr ⟨hp, hc, hl, hu.trans_le
    (rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) huv)⟩

theorem rectangle_upper_mono {N : ℕ} {l u v w w' : ℝ}
    (hN : 1 ≤ N) (hww' : w ≤ w') :
    rectangleCount N l u v w ≤ rectangleCount N l u v w' := by
  apply sum_le_sum_of_subset_of_nonneg (window_upper_mono hN hww')
  intro q _ _
  exact sum_nonneg (fun p _ => Int.natCast_nonneg _)

theorem corner_counts_le {N : ℕ} (hN : 1 ≤ N) (n : ℕ) :
    cornerCountA N n ≤ countA N ∧ cornerCountB N n ≤ countB N := by
  constructor <;> apply rectangle_upper_mono hN <;>
    exact sub_le_self _ (cornerWidth_pos n).le

theorem corner_counts_le_upsilon6 {N : ℕ} (hN : 1 ≤ N) (n : ℕ) :
    cornerCountA N n + cornerCountB N n ≤ upsilon6 N :=
  (add_le_add (corner_counts_le hN n).1 (corner_counts_le hN n).2).trans
    (original_ab_le_upsilon6 hN)

theorem window_corner_eventually_eq {N : ℕ} (hN : 1 ≤ N) (l w : ℝ) :
    ∀ᶠ n : ℕ in atTop, window N l (w - cornerWidth n) = window N l w := by
  have hpow : Tendsto (fun n => (N : ℝ) ^ (w - cornerWidth n)) atTop
      (𝓝 ((N : ℝ) ^ w)) := by
    have hcont : Continuous (fun t : ℝ => (N : ℝ) ^ t) :=
      Real.continuous_const_rpow (by exact_mod_cast (show N ≠ 0 by omega))
    simpa only [sub_zero] using hcont.continuousAt.tendsto.comp
      (tendsto_const_nhds.sub cornerWidth_tendsto)
  have hp : ∀ p ∈ window N l w,
      ∀ᶠ n : ℕ in atTop, p ∈ window N l (w - cornerWidth n) := by
    intro p hp
    obtain ⟨hp, hc, hl, hw⟩ := mem_window.mp hp
    filter_upwards [hpow.eventually (gt_mem_nhds hw)] with n hn
    exact mem_window.mpr ⟨hp, hc, hl, hn⟩
  filter_upwards [(eventually_all_finset (window N l w)).mpr hp] with n hn
  exact Subset.antisymm
    (window_upper_mono hN (sub_le_self _ (cornerWidth_pos n).le)) hn

theorem corner_counts_eventually_exact {N : ℕ} (hN : 1 ≤ N) :
    ∀ᶠ n : ℕ in atTop,
      cornerCountA N n = countA N ∧ cornerCountB N n = countB N := by
  filter_upwards [window_corner_eventually_eq hN beta aCeiling,
    window_corner_eventually_eq hN aCeiling sigma] with n ha hb
  constructor
  · simp only [cornerCountA, countA, rectangleCount, ha]
  · simp only [cornerCountB, countB, rectangleCount, hb]

theorem upsilon6_eventually_strict_decomposition {N : ℕ} (hN : 1 ≤ N) :
    ∀ᶠ n : ℕ in atTop,
      2 * beta + (aCeiling - cornerWidth n) < (1 / 2 : ℝ) ∧
      2 * bCut + (sigma - cornerWidth n) < (1 / 2 : ℝ) ∧
      upsilon6 N = cornerCountA N n + cornerCountB N n + countC N := by
  filter_upwards [corner_counts_eventually_exact hN] with n hn
  exact ⟨(corner_strict n).1, (corner_strict n).2, by
    rw [hn.1, hn.2, upsilon6_exact_three_blocks hN]⟩

end Wu18938Campaign.M5
