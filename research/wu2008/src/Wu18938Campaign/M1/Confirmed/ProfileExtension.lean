import Wu18938Campaign.M1.Confirmed.ProfileBuchstab
import Wu18938Campaign.M1.Confirmed.ClassicalLowerBounded
import NodeActual

noncomputable section

namespace Wu18938Campaign.M1.Confirmed.FiniteProfile

open Wu2008DoubleSieve Rebox Real MeasureTheory NodeExtension
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne
open scoped Classical Interval

def upperInput (H : ℝ → ℝ) (v : ℝ) : ℝ := 1 - H (max 1 (min v 3))

theorem upperInput_bounds {H : ℝ → ℝ}
    (hb : ∀ v ∈ Set.Icc (1 : ℝ) 3, 0 ≤ H v ∧ H v ≤ 1) (v : ℝ) :
    0 ≤ upperInput H v ∧ upperInput H v ≤ 1 := by
  have hh := hb (max 1 (min v 3))
    ⟨le_max_left _ _,max_le (by norm_num) (min_le_right _ _)⟩
  dsimp [upperInput]
  constructor <;> linarith

theorem upperInput_mono {H : ℝ → ℝ} (hH : Antitone H) : Monotone (upperInput H) := by
  intro a b hab
  exact sub_le_sub_left (hH (max_le_max le_rfl (min_le_min hab le_rfl))) 1

def lowerExtension (H : ℝ → ℝ) (c v : ℝ) : ℝ :=
  if v < 2 then 0 else log 3 + c - profileIntegral (upperInput H) (min v 4) 4

theorem input_integrable {H : ℝ → ℝ} (hH : Antitone H) {a b : ℝ}
    (ha : 1 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun v => upperInput H v / v) volume a b := by
  simpa only [div_eq_mul_inv,one_div,one_mul] using
    ((upperInput_mono hH).intervalIntegrable (μ := volume)).mul_continuousOn
      (reciprocal_continuous (by linarith) hab)

theorem input_integral_bounds {H : ℝ → ℝ} (hH : Antitone H)
    (hb : ∀ v ∈ Set.Icc (1 : ℝ) 3, 0 ≤ H v ∧ H v ≤ 1)
    {s : ℝ} (hs : 2 ≤ s) (hs4 : s ≤ 4) :
    0 ≤ profileIntegral (upperInput H) s 4 ∧
      profileIntegral (upperInput H) s 4 ≤ log 3 := by
  have hab : s - 1 ≤ (4 : ℝ) - 1 := by linarith
  have hi := input_integrable hH (by linarith : 1 ≤ s - 1) hab
  have hk := (reciprocal_continuous (by linarith : 0 < s - 1) hab).intervalIntegrable (μ := volume)
  refine ⟨intervalIntegral.integral_nonneg hab (fun v hv =>
    div_nonneg (upperInput_bounds hb v).1 (by linarith [hv.1])),?_⟩
  have hm := intervalIntegral.integral_mono_on hab hi hk (fun v hv =>
    div_le_div_of_nonneg_right (upperInput_bounds hb v).2 (by linarith [hv.1]))
  rw [integral_one_div_of_pos (by linarith : 0 < s - 1) (by norm_num : (0 : ℝ) < 4 - 1)] at hm
  have heq : log ((4 - 1) / (s - 1)) = log 3 - log (s - 1) := by
    norm_num only [show (4 : ℝ) - 1 = 3 by norm_num]
    exact log_div (by norm_num) (by linarith)
  rw [heq] at hm
  exact hm.trans (by linarith [log_nonneg (by linarith : 1 ≤ s - 1)])

theorem lowerExtension_bounds {H : ℝ → ℝ} (hH : Antitone H)
    (hb : ∀ v ∈ Set.Icc (1 : ℝ) 3, 0 ≤ H v ∧ H v ≤ 1)
    {c : ℝ} (hc : 0 ≤ c) (v : ℝ) :
    0 ≤ lowerExtension H c v ∧ lowerExtension H c v ≤ log 3 + c := by
  unfold lowerExtension
  split_ifs with hv
  · exact ⟨le_rfl,add_nonneg (log_nonneg (by norm_num)) hc⟩
  · have hi := input_integral_bounds hH hb
      (le_min (not_lt.mp hv) (by norm_num)) (min_le_right v 4)
    constructor <;> linarith

theorem lowerExtension_mono {H : ℝ → ℝ} (hH : Antitone H)
    (hb : ∀ v ∈ Set.Icc (1 : ℝ) 3, 0 ≤ H v ∧ H v ≤ 1)
    {c : ℝ} (hc : 0 ≤ c) : Monotone (lowerExtension H c) := by
  intro a b hab
  by_cases ha : a < 2
  · rw [lowerExtension,if_pos ha]
    exact (lowerExtension_bounds hH hb hc b).1
  have hb2 : ¬ b < 2 := by linarith
  rw [lowerExtension,if_neg ha,lowerExtension,if_neg hb2]
  have ha1 : 1 ≤ min a 4 - 1 := by have hh := le_min (not_lt.mp ha) (by norm_num : (2 : ℝ) ≤ 4); linarith
  have hab' : min a 4 - 1 ≤ min b 4 - 1 := sub_le_sub_right (min_le_min hab le_rfl) 1
  have hb3 : min b 4 - 1 ≤ (4 : ℝ) - 1 := sub_le_sub_right (min_le_right b 4) 1
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (input_integrable hH ha1 hab')
    (input_integrable hH (ha1.trans hab') hb3)
  have hn : 0 ≤ ∫ v in (min a 4 - 1)..(min b 4 - 1), upperInput H v / v :=
    intervalIntegral.integral_nonneg hab' (fun v hv =>
      div_nonneg (upperInput_bounds hb v).1 (by linarith [hv.1]))
  dsimp [profileIntegral]
  linarith only [hsplit,hn]

theorem lowerExtension_eq {H : ℝ → ℝ} (hH : Antitone H)
    {c v : ℝ} (hv : 2 ≤ v) (hv4 : v ≤ 4) :
    lowerExtension H c v =
      wuLowerCoefficient v + c + ∫ t in (v - 1)..3, H t / t := by
  have hab : v - 1 ≤ (3 : ℝ) := by linarith
  have hHdiv := profile_subinterval (profile_div_integrable hH.intervalIntegrable)
    (by linarith : 1 ≤ v - 1) hab
  have hrec := (reciprocal_continuous (by linarith : 0 < v - 1) hab).intervalIntegrable (μ := volume)
  have heq : profileIntegral (upperInput H) v 4 =
      log 3 - log (v - 1) - ∫ t in (v - 1)..3, H t / t := by
    unfold profileIntegral
    norm_num only [show (4 : ℝ) - 1 = 3 by norm_num]
    calc
      _ = ∫ t in (v - 1)..3, 1 / t - H t / t := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [Set.uIcc_of_le hab] at ht
        dsimp only [upperInput]
        rw [min_eq_left ht.2,max_eq_right (by linarith [ht.1] : 1 ≤ t)]
        ring
      _ = _ := by
        rw [intervalIntegral.integral_sub hrec hHdiv,
          integral_one_div_of_pos (by linarith : 0 < v - 1) (by norm_num : (0 : ℝ) < 3),
          log_div (by norm_num : (3 : ℝ) ≠ 0) (by linarith : v - 1 ≠ 0)]
  rw [lowerExtension,if_neg (not_lt.mpr hv),min_eq_left hv4,heq]
  have ha : wuLowerCoefficient v = log (v - 1) := jr1965f_normalized_firstInterval hv hv4
  rw [ha]
  ring

def upperExtension (H : ℝ → ℝ) (c v : ℝ) : ℝ :=
  wuUpperCoefficient 5 - profileIntegral (lowerExtension H c) (max 3 (min v 5)) 5

theorem lowerExtension_integrable {H : ℝ → ℝ} (hH : Antitone H)
    (hb : ∀ v ∈ Set.Icc (1 : ℝ) 3, 0 ≤ H v ∧ H v ≤ 1)
    {c : ℝ} (hc : 0 ≤ c) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun v => lowerExtension H c v / v) volume a b := by
  simpa only [div_eq_mul_inv,one_div,one_mul] using
    ((lowerExtension_mono hH hb hc).intervalIntegrable (μ := volume)).mul_continuousOn (reciprocal_continuous ha hab)

theorem upperExtension_mono {H : ℝ → ℝ} (hH : Antitone H)
    (hb : ∀ v ∈ Set.Icc (1 : ℝ) 3, 0 ≤ H v ∧ H v ≤ 1)
    {c : ℝ} (hc : 0 ≤ c) : Monotone (upperExtension H c) := by
  intro a b hab
  let x := max 3 (min a 5)
  let y := max 3 (min b 5)
  have hx : 3 ≤ x := le_max_left _ _
  have hxy : x ≤ y := max_le_max le_rfl (min_le_min hab le_rfl)
  have hy : y ≤ 5 := max_le (by norm_num) (min_le_right _ _)
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (lowerExtension_integrable hH hb hc (by linarith : 0 < x - 1) (by linarith : x - 1 ≤ y - 1))
    (lowerExtension_integrable hH hb hc (by linarith : 0 < y - 1) (by linarith : y - 1 ≤ (5 : ℝ) - 1))
  have hn : 0 ≤ ∫ v in (x - 1)..(y - 1), lowerExtension H c v / v :=
    intervalIntegral.integral_nonneg (by linarith) (fun v hv =>
      div_nonneg (lowerExtension_bounds hH hb hc v).1 (by linarith [hv.1]))
  change wuUpperCoefficient 5 - (∫ v in (x - 1)..(5 - 1), lowerExtension H c v / v) ≤
    wuUpperCoefficient 5 - (∫ v in (y - 1)..(5 - 1), lowerExtension H c v / v)
  linarith only [hsplit,hn]

theorem upperExtension_eq {H : ℝ → ℝ} (hH : Antitone H)
    {c v : ℝ} (hv : 3 ≤ v) (hv5 : v ≤ 5) :
    upperExtension H c v = wuUpperCoefficient v -
      (c * log (4 / (v - 1)) +
        ∫ t in (v - 2)..3, H t / t * log ((t + 1) / (v - 1))) := by
  have hHdiv := profile_subinterval (profile_div_integrable hH.intervalIntegrable)
    (by linarith : 1 ≤ v - 2) (by linarith : v - 2 ≤ 3)
  have hg := shifted_tail (by linarith : 0 < (v - 2) + 1)
    (by linarith : v - 2 ≤ 3) hHdiv c
  have hnorm : v - 2 + 1 = v - 1 := by ring
  norm_num only [hnorm,show (3 : ℝ) + 1 = 4 by norm_num] at hg
  have ha := wuLowerCoefficient_div_intervalIntegrable (by linarith : 0 < v - 1)
    (by linarith : v - 1 ≤ 4)
  have heq : profileIntegral (lowerExtension H c) v 5 =
      (∫ x in (v - 1)..4, wuLowerCoefficient x / x) +
      (∫ x in (v - 1)..4, (c + ∫ t in (x - 1)..3, H t / t) / x) := by
    rw [← intervalIntegral.integral_add ha hg.1]
    unfold profileIntegral
    norm_num only [show (5 : ℝ) - 1 = 4 by norm_num]
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le (by linarith : v - 1 ≤ 4)] at hx
    dsimp only
    rw [lowerExtension_eq hH (by linarith [hx.1]) hx.2]
    ring
  have hclass := wuUpperCoefficient_sub_eq_integral (by linarith : 2 ≤ v) hv5
  norm_num only [show (5 : ℝ) - 1 = 4 by norm_num] at hclass
  rw [upperExtension,min_eq_left hv5,max_eq_right hv,heq,hg.2]
  linarith only [hclass]

end Wu18938Campaign.M1.Confirmed.FiniteProfile
