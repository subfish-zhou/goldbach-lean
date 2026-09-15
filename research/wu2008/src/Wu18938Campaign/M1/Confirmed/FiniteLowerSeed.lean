import Wu18938Campaign.M1.Confirmed.BuchstabTransfer
import Wu18938Campaign.M1.Confirmed.FiniteSeed

noncomputable section

namespace Wu18938Campaign.M1.Confirmed.Rebox

open Wu2008DoubleSieve Finset Real Filter MeasureTheory
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne
open scoped Classical Topology Interval

theorem seed_reciprocal_bounds {s : ℝ} (hs : 3 ≤ s) (hs7 : s ≤ 7 / 2) :
    (1 / 26 : ℝ) ≤ ∫ u in (s - 1)..(13 / 5), 1 / u ∧
      (∫ u in (s - 1)..(13 / 5), 1 / u) ≤ 1 := by
  have hab : s - 1 ≤ (13 / 5 : ℝ) := by linarith
  have hi : IntervalIntegrable (fun u : ℝ => 1 / u) volume (s - 1) (13 / 5) := by
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_const.div continuousOn_id
    intro u hu
    rw [Set.uIcc_of_le hab] at hu
    change u ≠ 0
    linarith [hu.1]
  have hlo := intervalIntegral.integral_mono_on hab
    (intervalIntegrable_const (c := (5 / 13 : ℝ))) hi (fun u hu => by
      apply (le_div_iff₀ (by linarith [hu.1] : 0 < u)).mpr
      linarith [hu.2])
  have hhi := intervalIntegral.integral_mono_on hab hi
    (intervalIntegrable_const (c := (1 : ℝ))) (fun u hu => by
      apply (div_le_iff₀ (by linarith [hu.1] : 0 < u)).mpr
      linarith [hu.1])
  rw [intervalIntegral.integral_const,smul_eq_mul] at hlo hhi
  constructor <;> linarith

theorem lower_seed_cancellation {s c : ℝ} (hs : 3 ≤ s) (hs7 : s ≤ 7 / 2) :
    (∫ u in (s - 1)..((18 / 5 : ℝ) - 1), c / u) =
      c * (wuLowerCoefficient (18 / 5) - wuLowerCoefficient s) ∧
      (1 / 26 : ℝ) ≤ wuLowerCoefficient (18 / 5) - wuLowerCoefficient s ∧
      wuLowerCoefficient (18 / 5) - wuLowerCoefficient s ≤ 1 := by
  have hrec := wuLowerCoefficient_sub_eq_integral (show 2 ≤ s by linarith)
    (show s ≤ (18 / 5 : ℝ) by linarith)
  have hid : wuLowerCoefficient (18 / 5) - wuLowerCoefficient s =
      ∫ u in (s - 1)..(13 / 5 : ℝ), 1 / u := by
    rw [hrec,show (18 / 5 : ℝ) - 1 = 13 / 5 by norm_num]
    apply intervalIntegral.integral_congr
    intro u hu
    rw [Set.uIcc_of_le (by linarith : s - 1 ≤ (13 / 5 : ℝ))] at hu
    have hA : wuUpperCoefficient u = 1 :=
      jr1965F_normalized_initial (by linarith [hu.1]) (by linarith [hu.2])
    dsimp only
    rw [hA]
  have hb := seed_reciprocal_bounds hs hs7
  refine ⟨?_,by simpa only [hid] using hb.1,by simpa only [hid] using hb.2⟩
  rw [hid,show (18 / 5 : ℝ) - 1 = 13 / 5 by norm_num,← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro u _
  dsimp only
  ring

theorem seed_lower (m : ℕ) {η δ ε : ℝ}
    (hη : 0 < η) (hδ : 0 < δ) (hδhi : δ ≤ 1 / 100) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      ∀ s : ℝ, 3 ≤ s → s ≤ 7 / 2 →
      (wuLowerCoefficient s + HighSixPhase7.seed / 26 - ε) *
        boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) ≤
        wuBoxPhi N δ (convolutionWuWindows N Δ V) s := by
  let τ := min 1 (ε / 3)
  have hτ : 0 < τ := lt_min (by norm_num) (by positivity)
  have hτ1 : τ ≤ 1 := min_le_left _ _
  have hτε : 3 * τ ≤ ε := by have := min_le_right 1 (ε / 3); dsimp [τ]; linarith
  obtain ⟨T0,hT04,h0⟩ := lower_node_update m hη hδ hτ
  obtain ⟨T1,_,h1⟩ := seed_upper (m + 1) (show 0 < η / 20 by positivity) hδ hδhi hτ
  obtain ⟨T2,_,h2⟩ := roughBox_lower_leaf m hη hδ hτ
  refine ⟨max T0 (max T1 T2),hT04.trans (le_max_left _ _),?_⟩
  intro N hN heven i Δ V hb s hs hs7
  let c := 1 - HighSixPhase7.seed + τ
  have hc0 : 0 ≤ c := by dsimp [c,HighSixPhase7.seed]; linarith only [hτ]
  have hc11 : c ≤ 11 := by dsimp [c,HighSixPhase7.seed]; linarith only [hτ1]
  have hcross := h0 N (by omega) heven i Δ V hb (fun _ => c) (13 / 5)
    (fun _ _ _ _ _ => le_rfl) (fun _ _ => ⟨hc0,hc11⟩)
    (fun k U hU v hv hvhi => h1 N (by omega) heven k Δ U hU v hv hvhi)
    s (18 / 5) (by linarith) (by linarith) (by norm_num) (by norm_num)
  have hbase := h2 N (by omega) heven i Δ V hb (18 / 5) (by norm_num) (by norm_num)
  obtain ⟨hid,hlo,hhi⟩ := lower_seed_cancellation (c := c) hs hs7
  rw [hid] at hcross
  have hgain := mul_le_mul_of_nonneg_left hlo HighSixPhase7.seed_pos.le
  have herr := mul_le_mul_of_nonneg_left hhi hτ.le
  have hcoef : wuLowerCoefficient s + HighSixPhase7.seed / 26 - ε ≤
      (wuLowerCoefficient (18 / 5) - τ) -
        (c * (wuLowerCoefficient (18 / 5) - wuLowerCoefficient s) + τ) := by
    dsimp [c]
    nlinarith only [hgain,herr,hτε]
  have hpaid := mul_le_mul_of_nonneg_right hcoef (theta_nonneg hb (by omega) hη hδ)
  nlinarith only [hcross,hbase,hpaid]

end Wu18938Campaign.M1.Confirmed.Rebox
