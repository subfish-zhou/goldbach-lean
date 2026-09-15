import WSrcSixthGainWeights
import FiniteNodeCertificate

noncomputable section

namespace Wu18938Campaign.M3.Confirmed.TableBounds

open Real Set MeasureTheory QuarterTrim
open WuSource.SrcSixthGain

def ratio (upper : Bool) (s : ℝ) : ℝ :=
  if upper then
    ((1 / 2 - alpha * s) - alpha) * ((1 / 2 - alpha * s) - beta) / (alpha * beta)
  else beta * ((1 / 2 - alpha * s) - alpha) /
    (alpha * ((1 / 2 - alpha * s) - beta))

def denom (s : ℝ) : ℝ := s * (1 - 2 * alpha * s)
def vertex : ℝ := 1 / (4 * alpha)

def denomMax (a b : ℝ) : ℝ :=
  max (denom a) (max (denom b) (if a ≤ vertex ∧ vertex ≤ b then denom vertex else 0))

def logLower (x : ℝ) : ℝ :=
  2 * ∑ i ∈ Finset.range 12, ((x - 1) / (x + 1)) ^ (2 * i + 1) / (2 * i + 1 : ℝ)

theorem logLower_le {x : ℝ} (hx : 1 ≤ x) : logLower x ≤ log x := by
  have hx1 : 0 < x + 1 := by linarith
  have ht0 : 0 ≤ (x - 1) / (x + 1) := div_nonneg (by linarith) hx1.le
  have ht1 : (x - 1) / (x + 1) < 1 := (div_lt_one hx1).mpr (by linarith)
  have he : (1 + (x - 1) / (x + 1)) / (1 - (x - 1) / (x + 1)) = x := by
    field_simp
    ring
  have h := Real.sum_range_le_log_div ht0 ht1 12
  rw [he] at h
  unfold logLower
  linarith only [h]

theorem denom_pos {s : ℝ} (hs : s ∈ Icc 2 endpoint) : 0 < denom s := by
  have hb := scalar_bounds hs
  have ha := alpha_pos
  have hβ : 0 < beta := by norm_num [beta]
  unfold denom
  apply mul_pos (by linarith [hs.1])
  linarith [hb.1]

theorem denom_le_max {a b s : ℝ} (hs : s ∈ Icc a b) : denom s ≤ denomMax a b := by
  have hv : vertex = (1327 / 400 : ℝ) := by norm_num [vertex, alpha]
  unfold denomMax
  by_cases hav : a ≤ vertex
  · by_cases hvb : vertex ≤ b
    · rw [if_pos ⟨hav, hvb⟩]
      apply le_trans (b := denom vertex) _ (le_max_right _ _ |>.trans (le_max_right _ _))
      rw [hv]
      norm_num [denom, alpha]
      rw [hv] at hav hvb
      nlinarith [sq_nonneg (s - (1327 / 400 : ℝ))]
    · apply le_trans (b := denom b) _ ((le_max_left _ _).trans (le_max_right _ _))
      rw [hv] at hvb
      norm_num [denom, alpha]
      nlinarith [mul_nonneg (sub_nonneg.mpr hs.2)
        (show 0 ≤ (1327 : ℝ) - 200 * (s + b) by linarith [hs.2])]
  · apply le_trans (b := denom a) _ (le_max_left _ _)
    rw [hv] at hav
    norm_num [denom, alpha]
    nlinarith [mul_nonneg (sub_nonneg.mpr hs.1)
      (show 0 ≤ 200 * (s + a) - (1327 : ℝ) by linarith [hs.1])]

theorem ratio_pos {upper : Bool} {s : ℝ} (hs : s ∈ Icc 2 endpoint) :
    0 < ratio upper s := by
  have hb := (scalar_bounds hs).1
  have ha := alpha_pos
  have hβ : 0 < beta := by norm_num [beta]
  have h1 : 0 < (1 / 2 : ℝ) - alpha * s - alpha := by linarith
  have h2 : 0 < (1 / 2 : ℝ) - alpha * s - beta := by linarith
  unfold ratio
  cases upper <;> simp only [Bool.false_eq_true, if_false, if_true] <;>
    apply div_pos <;> positivity

theorem ratio_lower_mono {a s : ℝ} (ha : a ∈ Icc 2 endpoint)
    (hs : s ∈ Icc 2 endpoint) (has : a ≤ s) : ratio false a ≤ ratio false s := by
  have hα := alpha_pos
  have hβ : alpha < beta := by norm_num [alpha, beta]
  have hb := (scalar_bounds hs).1
  have hab := (scalar_bounds ha).1
  have h1 : 0 < alpha * ((1 / 2 : ℝ) - alpha * a - beta) :=
    mul_pos hα (by linarith)
  have h2 : 0 < alpha * ((1 / 2 : ℝ) - alpha * s - beta) :=
    mul_pos hα (by linarith)
  unfold ratio
  simp only [Bool.false_eq_true, if_false]
  apply (div_le_div_iff₀ h1 h2).mpr
  norm_num [alpha, beta] at *
  nlinarith

theorem ratio_upper_antitone {s b : ℝ} (hs : s ∈ Icc 2 endpoint)
    (hb : b ∈ Icc 2 endpoint) (hsb : s ≤ b) : ratio true b ≤ ratio true s := by
  have hα := alpha_pos
  have hβ : 0 < beta := by norm_num [beta]
  have hbd := (scalar_bounds hb).1
  have hsd := (scalar_bounds hs).1
  have h1 : 0 ≤ (1 / 2 : ℝ) - alpha * b - beta := by linarith
  have h2 : 0 ≤ (1 / 2 : ℝ) - alpha * s - alpha := by linarith only [hsd, hβ]
  unfold ratio
  simp only [if_true]
  apply div_le_div_of_nonneg_right _ (mul_nonneg hα.le hβ.le)
  exact mul_le_mul (by nlinarith) (by nlinarith) h1 h2

theorem density_ratio {upper : Bool} {s : ℝ}
    (hbranch : if upper then split ≤ s else s ≤ split) :
    density s = log (ratio upper s) / denom s := by
  cases upper
  · rw [density_lower hbranch]
    unfold lowerKernel ratio denom
    simp only [Bool.false_eq_true, if_false]
    congr 2
    rw [show beta * (1 - 2 * alpha - 2 * alpha * s) =
        2 * (beta * (1 / 2 - alpha * s - alpha)) by ring,
      show alpha * (1 - 2 * beta - 2 * alpha * s) =
        2 * (alpha * (1 / 2 - alpha * s - beta)) by ring]
    exact mul_div_mul_left _ _ (by norm_num : (2 : ℝ) ≠ 0)
  · rw [density_upper hbranch]
    unfold upperKernel ratio denom
    simp only [if_true]
    congr 2
    norm_num [alpha, beta]
    ring

theorem panel_lower {upper : Bool} {a b l : ℝ}
    (ha : 2 ≤ a) (hab : a ≤ b) (hb : b ≤ endpoint)
    (hbranch : if upper then split ≤ a else b ≤ split)
    (hl0 : 0 ≤ l)
    (hr : 1 ≤ ratio upper (if upper then b else a))
    (hl : l ≤ logLower (ratio upper (if upper then b else a))) :
    (b - a) * l / denomMax a b ≤ ∫ s in a..b, density s := by
  have hdom (s : ℝ) (hs : s ∈ Icc a b) : s ∈ Icc 2 endpoint :=
    ⟨ha.trans hs.1, hs.2.trans hb⟩
  have hi : IntervalIntegrable density volume a b := by
    apply density_integrable.mono_set
    rw [uIcc_of_le scalar_interval, uIcc_of_le hab]
    exact Icc_subset_Icc ha hb
  have hpoint (s : ℝ) (hs : s ∈ Icc a b) : l / denomMax a b ≤ density s := by
    have hds := denom_pos (hdom s hs)
    have hdm := denom_le_max hs
    have hrat : ratio upper (if upper then b else a) ≤ ratio upper s := by
      cases upper
      · exact ratio_lower_mono ⟨ha, hab.trans hb⟩ (hdom s hs) hs.1
      · exact ratio_upper_antitone (hdom s hs) ⟨ha.trans hab, hb⟩ hs.2
    have hlog : l ≤ log (ratio upper s) :=
      (hl.trans (logLower_le hr)).trans
        (log_le_log (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hr) hrat)
    rw [density_ratio (upper := upper) (by
      cases upper <;> simp only [Bool.false_eq_true, if_false, if_true] at hbranch ⊢
      · exact hs.2.trans hbranch
      · exact hbranch.trans hs.1)]
    exact (div_le_div_of_nonneg_left hl0 hds hdm).trans
      (div_le_div_of_nonneg_right hlog hds.le)
  have h := intervalIntegral.integral_mono_on hab
    (intervalIntegrable_const (c := l / denomMax a b)) hi hpoint
  simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_div_assoc] using h

theorem integral_grid_sum (a b : ℝ) (n : ℕ) (hn : n ≠ 0)
    (ha : 2 ≤ a) (hab : a ≤ b) (hb : b ≤ endpoint) :
    (∑ j ∈ Finset.range n,
      ∫ s in (a + (b-a)*(j:ℝ)/n)..(a + (b-a)*((j+1:ℕ):ℝ)/n), density s) =
      ∫ s in a..b, density s := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have grid (j : ℕ) (hj : j ≤ n) :
      a + (b-a)*(j:ℝ)/n ∈ Icc 2 endpoint := by
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have hjn : (j:ℝ) ≤ n := by exact_mod_cast hj
    have h0 := mul_nonneg (sub_nonneg.mpr hab) (div_nonneg hj0 hn0.le)
    have h1 := mul_le_mul_of_nonneg_left ((div_le_one hn0).mpr hjn)
      (sub_nonneg.mpr hab)
    rw [mul_div_assoc]
    constructor <;> nlinarith
  have hi : ∀ j < n, IntervalIntegrable density volume
      (a + (b-a)*(j:ℝ)/n) (a + (b-a)*((j+1:ℕ):ℝ)/n) := by
    intro j hj
    apply density_integrable.mono_set
    rw [uIcc_of_le scalar_interval]
    exact uIcc_subset_Icc (grid j hj.le) (grid (j+1) hj)
  have h := intervalIntegral.sum_integral_adjacent_intervals hi
  simpa [mul_div_assoc, hn0.ne'] using h

end Wu18938Campaign.M3.Confirmed.TableBounds
