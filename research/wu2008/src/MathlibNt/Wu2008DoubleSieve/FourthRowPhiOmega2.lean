import MathlibNt.Wu2008DoubleSieve.Omega2Lower
import MathlibNt.Wu2008DoubleSieve.FirstFunctionalGainIntegrals
import MathlibNt.Wu2008DoubleSieve.Omega2CanonicalIntegral

/-!
# Actual limiting Phi/Omega2 block in the fourth row

Only the already proved finite-threshold count estimate and ordered gain
limits are consumed here. No count, mass, integrability, or limit premise is
added to the public count contracts. Delta is fixed throughout.
-/

namespace Wu2008DoubleSieve
namespace FourthRowPhiOmega2

open Set Real MeasureTheory Filter
open scoped Interval Topology

/-- The literal final lower-coefficient integral, with the old actual gain. -/
noncomputable def J (δ s t : ℝ) : ℝ :=
  ∫ u in (1 - 1 / s)..(1 - 1 / t),
    (wuLowerCoefficient (t * u) + wuImprovementLimit false δ (t * u)) /
      (u * (1 - u))

/-- Positivity of the actual kernel on the entire closed integration interval. -/
theorem weight_pos {s t u : ℝ}
    (hs : 2 ≤ s) (hst : s ≤ t) (ht : 3 ≤ t) (ht5 : t ≤ 5)
    (hu : u ∈ uIcc (1 - 1 / s) (1 - 1 / t)) : 0 < u * (1 - u) := by
  have h := omega2_integral_domain hs hst ht ht5 hu
  exact mul_pos (by linarith [h.1]) (by linarith [h.2.1])

/-- Actual final integrability, derived from the two mature summand producers. -/
theorem limit_intervalIntegrable {δ s t : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2)
    (hs : 2 ≤ s) (hst : s ≤ t) (ht : 3 ≤ t) (ht5 : t ≤ 5) :
    IntervalIntegrable (fun u =>
      (wuLowerCoefficient (t * u) + wuImprovementLimit false δ (t * u)) /
        (u * (1 - u))) volume (1 - 1 / s) (1 - 1 / t) := by
  simpa only [add_div] using
    (firstFunctionalGain_coefficient_intervalIntegrable hs hst ht ht5).add
      (firstFunctionalGain_limit_intervalIntegrable hδ hδhi hs hst ht ht5)

/-- Final gain is dominated by any positive fixed depth after integration. -/
theorem limit_integral_le_fixedDepth (k : ℕ) {δ s t : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2)
    (hs : 2 ≤ s) (hst : s ≤ t) (ht : 3 ≤ t) (ht5 : t ≤ 5) :
    (∫ u in (1 - 1 / s)..(1 - 1 / t),
      wuImprovementLimit false δ (t * u) / (u * (1 - u))) ≤
    ∫ u in (1 - 1 / s)..(1 - 1 / t),
      wuImprovementAtInfinity false (k + 1) δ (t * u) / (u * (1 - u)) := by
  have hab : 1 - 1 / s ≤ 1 - 1 / t :=
    sub_le_sub_left (one_div_le_one_div_of_le (by linarith) hst) 1
  apply intervalIntegral.integral_mono_on hab
    (firstFunctionalGain_limit_intervalIntegrable hδ hδhi hs hst ht ht5)
    (firstFunctionalGain_fixedDepth_intervalIntegrable (k + 1) (by omega)
      hδ hδhi hs hst ht ht5)
  intro u hu
  have hu' : u ∈ uIcc (1 - 1 / s) (1 - 1 / t) := by
    rwa [uIcc_of_le hab]
  have hd := (omega2_integral_domain hs hst ht ht5 hu').2.2
  exact div_le_div_of_nonneg_right
    (wuImprovementLimit_le_fixed_depth false k hδ hδhi hd.1 hd.2)
    (weight_pos hs hst ht ht5 hu').le

/-- A fixed threshold eventually realizes the final integral from below.
Only the inner threshold limit is needed: fixed depth dominates final depth. -/
theorem finite_integral_eventually_ge (k : ℕ) {δ s t ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2)
    (hs : 2 ≤ s) (hst : s ≤ t) (ht : 3 ≤ t) (ht5 : t ≤ 5) (hε : 0 < ε) :
    ∀ᶠ N0 : ℕ in atTop,
      J δ s t - ε ≤ ∫ u in (1 - 1 / s)..(1 - 1 / t),
        (wuLowerCoefficient (t * u) + wuImprovementAt false (k + 1) δ (t * u) N0) /
          (u * (1 - u)) := by
  have hconv := firstFunctionalGain_integral_threshold_limit (k + 1) (by omega)
    hδ hδhi hs hst ht ht5
  have hnear := hconv.eventually (lt_mem_nhds (sub_lt_self _ hε))
  filter_upwards [hnear, firstFunctionalGain_eventually_intervalIntegrable
    (k + 1) (by omega) hδ hδhi hs hst ht ht5] with N0 hN0 hi
  have hc := firstFunctionalGain_coefficient_intervalIntegrable hs hst ht ht5
  have hf := firstFunctionalGain_limit_intervalIntegrable hδ hδhi hs hst ht ht5
  have hle := limit_integral_le_fixedDepth k hδ hδhi hs hst ht ht5
  simp only [J, add_div, intervalIntegral.integral_add hc hi,
    intervalIntegral.integral_add hc hf]
  linarith

/-- General fixed-parameter actual Omega2 lower bound, uniform over old boxes.
The threshold is chosen before N and before every source-box parameter. -/
theorem omega2_actual_limit_lower (k : ℕ) (hk : 1 ≤ k) {δ s t ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10)
    (hs : 2 ≤ s) (hst : s ≤ t) (ht : 3 ≤ t) (ht5 : t ≤ 5) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
        (J δ s t - ε) * boxTheta N ((N : ℝ) ^ (1 / 2 - δ))
          (convolutionWuWindows N Δ V) ≤
        wuOmega2Sum N δ s t (convolutionWuWindows N Δ V) := by
  have hδhalf : δ < 1 / 2 := by linarith
  obtain ⟨D, hD4, hD⟩ := wu04_52 k hδ hδhi (show 0 < ε / 2 by positivity)
  obtain ⟨M, hM⟩ := eventually_atTop.mp (finite_integral_eventually_ge k hδ hδhalf
    hs hst ht ht5 (show 0 < ε / 2 by positivity))
  obtain ⟨P, _, _, hP⟩ := wuImprovement_base_exists false k hk hδ hδhalf
    (show (1 : ℝ) ≤ 2 by norm_num) (show (2 : ℝ) ≤ 10 by norm_num)
  let T := max (max D M) P
  have hDT : D ≤ T := (le_max_left D M).trans (le_max_left _ _)
  have hMT : M ≤ T := (le_max_right D M).trans (le_max_left _ _)
  refine ⟨T, hD4.trans hDT, ?_⟩
  intro N hN he i Δ V hb
  have hmass := (hP N ((le_max_right _ _).trans hN) i Δ V hb).le
  have hc := hM T hMT
  have hcount := hD T hDT N hN he i Δ V hb s t hs hst ht ht5
  exact (mul_le_mul_of_nonneg_right (by linarith : J δ s t - ε ≤
    (∫ u in (1 - 1 / s)..(1 - 1 / t),
      (wuLowerCoefficient (t * u) + wuImprovementAt false (k + 1) δ (t * u) T) /
        (u * (1 - u))) - ε / 2) hmass).trans hcount

/-- Actual upper Phi estimate using depth exactly k, not an unproved change
of source family. The predecessor is legitimate because k is positive. -/
theorem phi_actual_limit_upper (k : ℕ) (hk : 1 ≤ k) {δ s ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hs : 1 ≤ s) (hs10 : s ≤ 10) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
        wuBoxPhi N δ (convolutionWuWindows N Δ V) s ≤
          (wuUpperCoefficient s - wuImprovementLimit true δ s + ε) *
            boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  have hm := wuImprovementLimit_sub_mem true (k - 1) hδ hδhi hs hs10 hε
  have hdepth : k - 1 + 1 = k := by omega
  rw [hdepth] at hm
  obtain ⟨M, hM⟩ := hm
  refine ⟨max 4 M, le_max_left _ _, ?_⟩
  intro N hN he i Δ V hb
  have hc := hM N ((le_max_right _ _).trans hN)
    ((le_max_left _ _).trans hN) he i Δ V hb
  simpa only [wuImprovementComparison, if_true, sub_sub_eq_add_sub,
    sub_add_eq_add_sub] using hc

/-- Literal logarithmic form; the canonical range is proved, not assumed
as a count or transport contract. -/
theorem J_eq_log {δ s t : ℝ}
    (hs : 2 ≤ s) (hst : s ≤ t) (ht5 : t ≤ 5) (hratio : 2 ≤ t - t / s) :
    J δ s t = ∫ u in (1 - 1 / s)..(1 - 1 / t),
      (log (t * u - 1) + wuImprovementLimit false δ (t * u)) / (u * (1 - u)) := by
  apply intervalIntegral.integral_congr
  intro u hu
  have h := omega2_canonical_parameter_mem hs hst ht5 hratio hu
  have ha : wuLowerCoefficient (t * u) = log (t * u - 1) :=
    jr1965f_normalized_firstInterval h.1 h.2
  simp only [ha]

end FourthRowPhiOmega2
end Wu2008DoubleSieve
