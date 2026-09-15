import Wu18938Campaign.M5.StrictCorner
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Data.Nat.Prime.Basic

noncomputable section

namespace Wu18938Campaign.M5.LiteralCount

open Real Filter Finset
open scoped Classical Topology

-- These are the unfolded frozen prime-window and closed unscaled count definitions.
def window (N : ℕ) (l u : ℝ) : Finset ℕ :=
  (range ⌈(N : ℝ) ^ u⌉₊).filter
    (fun p => p.Prime ∧ p.Coprime N ∧ (N : ℝ) ^ l ≤ (p : ℝ))

def atom (N d : ℕ) : ℤ :=
  ((range (N + 1)).filter (fun r => r.Prime ∧ d ∣ N - r ∧
    ∀ q : ℕ, q.Prime → q.Coprime N → (q : ℝ) ≤ (N : ℝ) ^ (100 / 1327 : ℝ) →
      ¬q ∣ N - r)).card

def pairCount (N : ℕ) (l u v w : ℝ) : ℤ :=
  ∑ q ∈ window N v w, ∑ p ∈ window N l u, atom N (p * q)

def width (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

def countA (N : ℕ) (η : ℝ) : ℤ :=
  pairCount N (100 / 1327) (25 / 206) (25 / 206) (1 / 2 - 2 * (25 / 206) - η)

def countB (N : ℕ) (η : ℝ) : ℤ :=
  pairCount N (100 / 1327) (3 * (100 / 1327) / 2)
    (1 / 2 - 2 * (25 / 206)) (1 / 2 - 3 * (100 / 1327) - η)

def upsilon6 (N : ℕ) : ℤ :=
  pairCount N (100 / 1327) (25 / 206) (25 / 206) (1 / 2 - 3 * (100 / 1327))

theorem mem_window {N p : ℕ} {l u : ℝ} :
    p ∈ window N l u ↔ p.Prime ∧ p.Coprime N ∧
      (N : ℝ) ^ l ≤ (p : ℝ) ∧ (p : ℝ) < (N : ℝ) ^ u := by
  simp only [window, mem_filter, mem_range, Nat.lt_ceil]
  tauto

theorem window_upper_mono {N : ℕ} {l u v : ℝ}
    (hN : 1 ≤ N) (huv : u ≤ v) : window N l u ⊆ window N l v := by
  intro p hp
  obtain ⟨hp, hc, hl, hu⟩ := mem_window.mp hp
  exact mem_window.mpr ⟨hp, hc, hl, hu.trans_le
    (rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) huv)⟩

theorem atom_nonneg (N d : ℕ) : 0 ≤ atom N d := Int.natCast_nonneg _

theorem pairCount_upper_mono {N : ℕ} {l u v w w' : ℝ}
    (hN : 1 ≤ N) (hww' : w ≤ w') :
    pairCount N l u v w ≤ pairCount N l u v w' := by
  apply sum_le_sum_of_subset_of_nonneg (window_upper_mono hN hww')
  intro q _ _
  exact sum_nonneg (fun p _ => atom_nonneg N (p * q))

theorem pairCount_first_upper_mono {N : ℕ} {l u u' v w : ℝ}
    (hN : 1 ≤ N) (huu' : u ≤ u') :
    pairCount N l u v w ≤ pairCount N l u' v w := by
  apply sum_le_sum
  intro q _
  exact sum_le_sum_of_subset_of_nonneg (window_upper_mono hN huu')
    (fun p _ _ => atom_nonneg N (p * q))

theorem window_sum_split {N : ℕ} {l m u : ℝ}
    (hN : 1 ≤ N) (hlm : l ≤ m) (hmu : m ≤ u) (f : ℕ → ℤ) :
    (∑ p ∈ window N l u, f p) =
      (∑ p ∈ window N l m, f p) + ∑ p ∈ window N m u, f p := by
  have hs : (window N l u).filter (fun p : ℕ => (p : ℝ) < (N : ℝ) ^ m) = window N l m := by
    ext p
    simp only [mem_filter, mem_window]
    have hpow := rpow_le_rpow_of_exponent_le
      (show (1 : ℝ) ≤ (N : ℝ) by exact_mod_cast hN) hmu
    constructor
    · rintro ⟨⟨hp, hc, hl, _⟩, hm⟩
      exact ⟨hp, hc, hl, hm⟩
    · rintro ⟨hp, hc, hl, hm⟩
      exact ⟨⟨hp, hc, hl, hm.trans_le hpow⟩, hm⟩
  have ht : (window N l u).filter (fun p : ℕ => ¬(p : ℝ) < (N : ℝ) ^ m) = window N m u := by
    ext p
    simp only [mem_filter, mem_window, not_lt]
    have hpow := rpow_le_rpow_of_exponent_le
      (show (1 : ℝ) ≤ (N : ℝ) by exact_mod_cast hN) hlm
    constructor
    · rintro ⟨⟨hp, hc, _, hu⟩, hm⟩
      exact ⟨hp, hc, hm, hu⟩
    · rintro ⟨hp, hc, hm, hu⟩
      exact ⟨⟨hp, hc, hpow.trans hm, hu⟩, hm⟩
  rw [← hs, ← ht]
  exact (sum_filter_add_sum_filter_not _ _ _).symm

theorem original_ab_le_upsilon6 {N : ℕ} (hN : 1 ≤ N) :
    countA N 0 + countB N 0 ≤ upsilon6 N := by
  have hb := pairCount_first_upper_mono
    (l := (100 / 1327 : ℝ)) (u := 3 * (100 / 1327 : ℝ) / 2)
    (u' := (25 / 206 : ℝ)) (v := 1 / 2 - 2 * (25 / 206 : ℝ))
    (w := 1 / 2 - 3 * (100 / 1327 : ℝ)) hN (by norm_num)
  unfold upsilon6 pairCount
  rw [window_sum_split (m := 1 / 2 - 2 * (25 / 206 : ℝ)) hN
    (by norm_num) (by norm_num)]
  simpa only [countA, countB, pairCount, sub_zero] using
    add_le_add (le_refl (pairCount N (100 / 1327) (25 / 206)
      (25 / 206) (1 / 2 - 2 * (25 / 206)))) hb

theorem original_trimmed_le {N : ℕ} (hN : 1 ≤ N) {η : ℝ} (hη : 0 ≤ η) :
    countA N η + countB N η ≤ upsilon6 N := by
  have ha : countA N η ≤ countA N 0 := by
    simpa only [countA, sub_zero] using
      pairCount_upper_mono (l := (100 / 1327 : ℝ)) (u := (25 / 206 : ℝ))
        (v := (25 / 206 : ℝ)) hN (sub_le_self (1 / 2 - 2 * (25 / 206 : ℝ)) hη)
  have hb : countB N η ≤ countB N 0 := by
    simpa only [countB, sub_zero] using
      pairCount_upper_mono (l := (100 / 1327 : ℝ)) (u := 3 * (100 / 1327 : ℝ) / 2)
        (v := 1 / 2 - 2 * (25 / 206 : ℝ)) hN
        (sub_le_self (1 / 2 - 3 * (100 / 1327 : ℝ)) hη)
  exact (add_le_add ha hb).trans (original_ab_le_upsilon6 hN)

theorem width_pos (n : ℕ) : 0 < width n := by
  unfold width
  positivity

theorem width_tendsto : Tendsto width atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

theorem window_eventually_exact {N : ℕ} (hN : 1 ≤ N) (l w : ℝ) :
    ∀ᶠ n : ℕ in atTop, window N l (w - width n) = window N l w := by
  have hpow : Tendsto (fun n => (N : ℝ) ^ (w - width n)) atTop
      (𝓝 ((N : ℝ) ^ w)) := by
    have hcont : Continuous (fun t : ℝ => (N : ℝ) ^ t) :=
      Real.continuous_const_rpow (by exact_mod_cast (show N ≠ 0 by omega))
    simpa only [sub_zero, Function.comp_def] using hcont.continuousAt.tendsto.comp
      (tendsto_const_nhds.sub width_tendsto)
  have hp : ∀ p ∈ window N l w,
      ∀ᶠ n : ℕ in atTop, p ∈ window N l (w - width n) := by
    intro p hp
    obtain ⟨hp, hc, hl, hw⟩ := mem_window.mp hp
    filter_upwards [hpow.eventually (lt_mem_nhds hw)] with n hn
    exact mem_window.mpr ⟨hp, hc, hl, hn⟩
  filter_upwards [(eventually_all_finset (window N l w)).mpr hp] with n hn
  exact Subset.antisymm (window_upper_mono hN (sub_le_self _ (width_pos n).le)) hn

theorem original_ab_eventually_exact {N : ℕ} (hN : 1 ≤ N) :
    ∀ᶠ n : ℕ in atTop,
      countA N (width n) = countA N 0 ∧ countB N (width n) = countB N 0 := by
  filter_upwards [window_eventually_exact hN (25 / 206) (1 / 2 - 2 * (25 / 206)),
    window_eventually_exact hN (1 / 2 - 2 * (25 / 206)) (1 / 2 - 3 * (100 / 1327))]
    with n ha hb
  constructor
  · simp only [countA, pairCount, sub_zero, ha]
  · simp only [countB, pairCount, sub_zero, hb]

theorem original_strict_count_consumer {N : ℕ} (hN : 1 ≤ N) (n : ℕ) :
    2 * (25 / 206 : ℝ) + (1 / 2 - 2 * (25 / 206) - width n) < 1 / 2 ∧
      2 * (3 * (100 / 1327 : ℝ) / 2) +
        (1 / 2 - 3 * (100 / 1327) - width n) < 1 / 2 ∧
      countA N (width n) + countB N (width n) ≤ upsilon6 N := by
  have hs := StrictCorner.original_strict_slack (δ := width n) (width_pos n) le_rfl
  exact ⟨hs.1, hs.2.1, original_trimmed_le hN (width_pos n).le⟩

end Wu18938Campaign.M5.LiteralCount
