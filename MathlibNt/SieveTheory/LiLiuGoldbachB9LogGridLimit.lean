import MathlibNt.Analysis.IntegralExcessCover
import MathlibNt.SieveTheory.LiLiuGoldbachB9LogGridRegion

open Finset MeasureTheory Set
open scoped ENNReal BigOperators Interval

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

noncomputable section

set_option maxHeartbeats 800000

open MathlibNt.SieveTheory.LiuWeight
open PrimeReciprocalLogRectangle

/-- The actual C10 integral for B9, without the sieve factor eight. -/
def goldbachB9MainIntegral : ℝ :=
  ∫ u in (4 / 53 : ℝ)..(1 / 3),
    ∫ v in (1 / 3 : ℝ)..((1 - u) / 2), 1 / (u * v * (1 - u - v))

def goldbachB9LogGridUpperIntegrand (n : ℕ) (x : ℝ × ℝ) : ℝ :=
  ∑ q ∈ goldbachB9LogGridCells n,
    (1 / (1 - goldbachB9AlphaGridPoint n (q.1 + 1) -
      goldbachB9BetaGridPoint n (q.2 + 1))) *
      (goldbachB9LogGridCell n q).indicator liuLogDensity x

theorem goldbachB9LogIntegrand_eq (u v : ℝ) :
    liuLogIntegrand (u, v) = 1 / (u * v * (1 - u - v)) := by
  simp only [liuLogIntegrand, liuLogKernel, liuLogDensity, one_div, mul_inv]
  ring

theorem goldbachB9LogDensity_bounds {x : ℝ × ℝ}
    (hx : x ∈ goldbachB9LogAmbientBox) :
    0 ≤ liuLogDensity x ∧ liuLogDensity x ≤ 80 := by
  have hprod : (1 / 80 : ℝ) ≤ x.1 * x.2 := by
    calc
      (1 / 80 : ℝ) = (1 / 20 : ℝ) * (1 / 4 : ℝ) := by norm_num
      _ ≤ x.1 * x.2 := mul_le_mul hx.1.1 hx.2.1 (by norm_num) (by linarith [hx.1.1])
  change 0 ≤ 1 / (x.1 * x.2) ∧ 1 / (x.1 * x.2) ≤ 80
  constructor
  · exact one_div_nonneg.mpr (by linarith)
  · rw [div_le_iff₀ (by linarith : 0 < x.1 * x.2)]
    linarith

theorem goldbachB9LogKernel_bounds {x : ℝ × ℝ}
    (hx : x ∈ goldbachB9LogAmbientBox) :
    0 ≤ liuLogKernel x ∧ liuLogKernel x ≤ 6 := by
  have hg := goldbachB9LogAmbientBox_gap hx
  change 0 ≤ 1 / (1 - x.1 - x.2) ∧ 1 / (1 - x.1 - x.2) ≤ 6
  constructor
  · exact one_div_nonneg.mpr (by linarith)
  · rw [div_le_iff₀ (by linarith : 0 < 1 - x.1 - x.2)]
    linarith

theorem goldbachB9LogIntegrand_bounds {x : ℝ × ℝ}
    (hx : x ∈ goldbachB9LogAmbientBox) :
    0 ≤ liuLogIntegrand x ∧ liuLogIntegrand x ≤ 480 := by
  have hd := goldbachB9LogDensity_bounds hx
  have hk := goldbachB9LogKernel_bounds hx
  exact ⟨mul_nonneg hk.1 hd.1,
    (mul_le_mul hk.2 hd.2 hd.1 (by norm_num)).trans (by norm_num)⟩

theorem continuousOn_goldbachB9LogDensity :
    ContinuousOn liuLogDensity goldbachB9LogAmbientBox := by
  unfold liuLogDensity
  apply ContinuousOn.div continuousOn_const
    (continuous_fst.continuousOn.mul continuous_snd.continuousOn)
  intro x hx
  exact mul_ne_zero (by linarith [hx.1.1]) (by linarith [hx.2.1])

theorem continuousOn_goldbachB9LogKernel :
    ContinuousOn liuLogKernel goldbachB9LogAmbientBox := by
  unfold liuLogKernel
  apply ContinuousOn.div continuousOn_const
    ((continuousOn_const.sub continuous_fst.continuousOn).sub continuous_snd.continuousOn)
  intro x hx
  have hg := goldbachB9LogAmbientBox_gap hx
  change 1 - x.1 - x.2 ≠ 0
  linarith

theorem continuousOn_goldbachB9LogIntegrand :
    ContinuousOn liuLogIntegrand goldbachB9LogAmbientBox :=
  continuousOn_goldbachB9LogKernel.mul continuousOn_goldbachB9LogDensity

theorem continuousOn_goldbachB9MainInner {u : ℝ} (hu : u ∈ Icc (4 / 53 : ℝ) (1 / 3)) :
    ContinuousOn (fun v : ℝ => 1 / (u * v * (1 - u - v)))
      (Icc (1 / 3) ((1 - u) / 2)) := by
  have h : ContinuousOn (fun v : ℝ => liuLogIntegrand (u, v))
      (Icc (1 / 3) ((1 - u) / 2)) := by
    apply continuousOn_goldbachB9LogIntegrand.comp
      (continuous_const.prodMk continuous_id).continuousOn
    intro v hv
    change (u, v) ∈ goldbachB9LogAmbientBox
    exact ⟨⟨by linarith [hu.1], hu.2⟩,
      ⟨by linarith [hv.1], by linarith [hu.1, hv.2]⟩⟩
  simpa only [goldbachB9LogIntegrand_eq] using h

theorem intervalIntegrable_goldbachB9MainInner
    {u : ℝ} (hu : u ∈ Icc (4 / 53 : ℝ) (1 / 3)) :
    IntervalIntegrable (fun v : ℝ => 1 / (u * v * (1 - u - v)))
      volume (1 / 3) ((1 - u) / 2) :=
  ContinuousOn.intervalIntegrable_of_Icc (by linarith [hu.2])
    (continuousOn_goldbachB9MainInner hu)

theorem integrableOn_goldbachB9LogDensity {s : Set (ℝ × ℝ)}
    (hs : MeasurableSet s) (hsub : s ⊆ goldbachB9LogAmbientBox) :
    IntegrableOn liuLogDensity s := by
  apply ContinuousOn.integrableOn_of_subset_isCompact continuousOn_goldbachB9LogDensity
    isCompact_goldbachB9LogAmbientBox hs hsub
  exact (lt_of_le_of_lt (measure_mono hsub)
    isCompact_goldbachB9LogAmbientBox.measure_lt_top).ne

theorem integrableOn_goldbachB9LogIntegrand {s : Set (ℝ × ℝ)}
    (hs : MeasurableSet s) (hsub : s ⊆ goldbachB9LogAmbientBox) :
    IntegrableOn liuLogIntegrand s := by
  apply ContinuousOn.integrableOn_of_subset_isCompact
    continuousOn_goldbachB9LogIntegrand
    isCompact_goldbachB9LogAmbientBox hs hsub
  exact (lt_of_le_of_lt (measure_mono hsub)
    isCompact_goldbachB9LogAmbientBox.measure_lt_top).ne

theorem integrable_goldbachB9SourceIndicator :
    Integrable (goldbachB9LogSourceRegion.indicator liuLogIntegrand) :=
  integrable_indicator_of_integrableOn measurableSet_goldbachB9LogSourceRegion
    (integrableOn_goldbachB9LogIntegrand measurableSet_goldbachB9LogSourceRegion
      goldbachB9LogSourceRegion_subset_ambientBox)

theorem goldbachB9MainIntegral_eq_iteratedSetIntegral :
    goldbachB9MainIntegral =
      ∫ u in Ioc (4 / 53 : ℝ) (1 / 3),
        ∫ v in Ioc (1 / 3) ((1 - u) / 2), liuLogIntegrand (u, v) := by
  unfold goldbachB9MainIntegral
  rw [intervalIntegral.integral_of_le (by norm_num : (4 / 53 : ℝ) ≤ 1 / 3)]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro u hu
  change (∫ v in (1 / 3 : ℝ)..((1 - u) / 2), 1 / (u * v * (1 - u - v))) =
    ∫ v in Ioc (1 / 3) ((1 - u) / 2), liuLogIntegrand (u, v)
  rw [intervalIntegral.integral_of_le (by linarith [hu.2] : (1 / 3 : ℝ) ≤ (1 - u) / 2)]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro v _
  exact (goldbachB9LogIntegrand_eq u v).symm

theorem goldbachB9SourceIndicator_integral_section (u : ℝ) :
    (∫ v, goldbachB9LogSourceRegion.indicator liuLogIntegrand (u, v)) =
      (Ioc (4 / 53 : ℝ) (1 / 3)).indicator
        (fun u => ∫ v in Ioc (1 / 3) ((1 - u) / 2), liuLogIntegrand (u, v)) u := by
  by_cases hu : u ∈ Ioc (4 / 53 : ℝ) (1 / 3)
  · rw [indicator_of_mem hu, ← integral_indicator measurableSet_Ioc]
    apply integral_congr_ae
    filter_upwards with v
    have hmem : (u, v) ∈ goldbachB9LogSourceRegion ↔ v ∈ Ioc (1 / 3) ((1 - u) / 2) :=
      and_iff_right hu
    change goldbachB9LogSourceRegion.indicator liuLogIntegrand (u, v) =
      (Ioc (1 / 3) ((1 - u) / 2)).indicator (fun v => liuLogIntegrand (u, v)) v
    by_cases hv : v ∈ Ioc (1 / 3) ((1 - u) / 2)
    · rw [indicator_of_mem (hmem.mpr hv), indicator_of_mem hv]
    · rw [indicator_of_notMem (fun h => hv (hmem.mp h)), indicator_of_notMem hv]
  · rw [indicator_of_notMem hu]
    apply integral_eq_zero_of_ae
    filter_upwards with v
    exact indicator_of_notMem (fun h => hu h.1) _

theorem intervalIntegrable_goldbachB9MainOuter :
    IntervalIntegrable
      (fun u : ℝ => ∫ v in (1 / 3 : ℝ)..((1 - u) / 2), 1 / (u * v * (1 - u - v)))
      volume (4 / 53) (1 / 3) := by
  have hF := integrable_goldbachB9SourceIndicator
  rw [Measure.volume_eq_prod ℝ ℝ] at hF
  have hi := hF.integral_prod_left
  have hIndicator : Integrable ((Ioc (4 / 53 : ℝ) (1 / 3)).indicator
      (fun u => ∫ v in Ioc (1 / 3) ((1 - u) / 2), liuLogIntegrand (u, v))) := by
    apply hi.congr
    filter_upwards with u
    exact goldbachB9SourceIndicator_integral_section u
  have hOn := (integrable_indicator_iff measurableSet_Ioc).mp hIndicator
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le
    (by norm_num : (4 / 53 : ℝ) ≤ 1 / 3)).mpr
  apply hOn.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
  rw [intervalIntegral.integral_of_le (by linarith [hu.2] : (1 / 3 : ℝ) ≤ (1 - u) / 2)]
  simp only [goldbachB9LogIntegrand_eq]

/-- Fubini is applied to an integrable indicator, not to an unspecified integral. -/
theorem goldbachB9MainIntegral_eq_setIntegral :
    goldbachB9MainIntegral = ∫ x in goldbachB9LogSourceRegion, liuLogIntegrand x := by
  rw [goldbachB9MainIntegral_eq_iteratedSetIntegral]
  let F := goldbachB9LogSourceRegion.indicator liuLogIntegrand
  have hF : Integrable F := integrable_goldbachB9SourceIndicator
  have hFubini : (∫ z, F z) = ∫ u, ∫ v, F (u, v) := by
    rw [Measure.volume_eq_prod ℝ ℝ] at hF ⊢
    exact integral_prod F hF
  calc
    _ = ∫ u, (Ioc (4 / 53 : ℝ) (1 / 3)).indicator
        (fun u => ∫ v in Ioc (1 / 3) ((1 - u) / 2), liuLogIntegrand (u, v)) u := by
      rw [integral_indicator measurableSet_Ioc]
    _ = ∫ u, ∫ v, F (u, v) := by
      apply integral_congr_ae
      filter_upwards with u
      exact (goldbachB9SourceIndicator_integral_section u).symm
    _ = ∫ z, F z := hFubini.symm
    _ = _ := integral_indicator measurableSet_goldbachB9LogSourceRegion

theorem goldbachB9MainIntegral_nonneg : 0 ≤ goldbachB9MainIntegral := by
  rw [goldbachB9MainIntegral_eq_setIntegral]
  apply setIntegral_nonneg measurableSet_goldbachB9LogSourceRegion
  intro x hx
  exact (goldbachB9LogIntegrand_bounds (goldbachB9LogSourceRegion_subset_ambientBox hx)).1

theorem integrable_goldbachB9LogGridUpperIntegrand (n : ℕ) (hn : 0 < n) :
    Integrable (goldbachB9LogGridUpperIntegrand n) := by
  classical
  exact integrable_finsetSum _ fun q _ =>
    (integrable_indicator_of_integrableOn (measurableSet_goldbachB9LogGridCell n q)
      (integrableOn_goldbachB9LogDensity (measurableSet_goldbachB9LogGridCell n q)
        (goldbachB9LogGridCell_subset_ambientBox hn q))).const_mul _

/-- The selected-cell sum retains its actual logarithmic rectangle masses. -/
theorem goldbachB9LogGridUpperSum_eq_integral (n : ℕ) (hn : 0 < n) :
    goldbachB9LogGridUpperSum n = ∫ x, goldbachB9LogGridUpperIntegrand n x := by
  classical
  unfold goldbachB9LogGridUpperSum goldbachB9LogGridUpperIntegrand
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro q _
    rw [integral_const_mul, integral_indicator (measurableSet_goldbachB9LogGridCell n q)]
    rw [logarithmicRectangleMass_eq_setIntegral
      (goldbachB9AlphaGridPoint_pos n q.1) (goldbachB9AlphaGridPoint_lt_succ hn)
      (goldbachB9BetaGridPoint_pos n q.2) (goldbachB9BetaGridPoint_lt_succ hn)]
    rfl
  · intro q _
    exact (integrable_indicator_of_integrableOn (measurableSet_goldbachB9LogGridCell n q)
      (integrableOn_goldbachB9LogDensity (measurableSet_goldbachB9LogGridCell n q)
        (goldbachB9LogGridCell_subset_ambientBox hn q))).const_mul _

theorem goldbachB9LogGridUpperIntegrand_eq_of_mem {n : ℕ} (hn : 0 < n)
    {q : Fin n × Fin n} (hq : q ∈ goldbachB9LogGridCells n)
    {x : ℝ × ℝ} (hx : x ∈ goldbachB9LogGridCell n q) :
    goldbachB9LogGridUpperIntegrand n x =
      (1 / (1 - goldbachB9AlphaGridPoint n (q.1 + 1) -
        goldbachB9BetaGridPoint n (q.2 + 1))) * liuLogDensity x := by
  classical
  unfold goldbachB9LogGridUpperIntegrand
  rw [Finset.sum_eq_single q]
  · rw [indicator_of_mem hx]
  · intro r _ hrq
    have hnot : x ∉ goldbachB9LogGridCell n r := fun hxr =>
      Set.disjoint_left.mp
        (goldbachB9LogGridCell_pairwiseDisjoint hn (mem_univ q) (mem_univ r) hrq.symm)
        hx hxr
    rw [indicator_of_notMem hnot, mul_zero]
  · exact fun h => (h hq).elim

theorem goldbachB9LogGridUpperIntegrand_eq_zero {n : ℕ} {x : ℝ × ℝ}
    (hx : x ∉ goldbachB9LogGridRegion n) : goldbachB9LogGridUpperIntegrand n x = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro q hq
  have hnot : x ∉ goldbachB9LogGridCell n q :=
    fun h => hx (Set.mem_iUnion₂.mpr ⟨q, hq, h⟩)
  rw [indicator_of_notMem hnot, mul_zero]

private theorem b9CornerKernel_le_six {n : ℕ} (hn : 0 < n) (q : Fin n × Fin n) :
    1 / (1 - goldbachB9AlphaGridPoint n (q.1 + 1) -
      goldbachB9BetaGridPoint n (q.2 + 1)) ≤ 6 := by
  have hg := goldbachB9LogGridCell_cornerGap_ge hn q
  rw [div_le_iff₀ (goldbachB9LogGridCell_cornerGap_pos hn q)]
  linarith

theorem goldbachB9LogGridUpperIntegrand_le {n : ℕ} (hn : 0 < n)
    {x : ℝ × ℝ} (hx : x ∈ goldbachB9LogGridRegion n) :
    goldbachB9LogGridUpperIntegrand n x ≤ 480 := by
  obtain ⟨q, hq, hxq⟩ := Set.mem_iUnion₂.mp hx
  rw [goldbachB9LogGridUpperIntegrand_eq_of_mem hn hq hxq]
  have hd := goldbachB9LogDensity_bounds (goldbachB9LogGridCell_subset_ambientBox hn q hxq)
  exact (mul_le_mul (b9CornerKernel_le_six hn q) hd.2 hd.1 (by norm_num)).trans
    (by norm_num)

theorem goldbachB9LogGrid_kernel_variation_step {n : ℕ} (hn : 0 < n)
    (q : Fin n × Fin n) {x : ℝ × ℝ} (hx : x ∈ goldbachB9LogGridCell n q) :
    0 ≤ 1 / (1 - goldbachB9AlphaGridPoint n (q.1 + 1) -
      goldbachB9BetaGridPoint n (q.2 + 1)) - liuLogKernel x ∧
    1 / (1 - goldbachB9AlphaGridPoint n (q.1 + 1) -
      goldbachB9BetaGridPoint n (q.2 + 1)) - liuLogKernel x ≤
        36 * (goldbachB9AlphaGridStep n + goldbachB9BetaGridStep n) := by
  let c := 1 - goldbachB9AlphaGridPoint n (q.1 + 1) -
    goldbachB9BetaGridPoint n (q.2 + 1)
  let d := 1 - x.1 - x.2
  have hc : (1 / 6 : ℝ) ≤ c := goldbachB9LogGridCell_cornerGap_ge hn q
  have hcd : c ≤ d := by dsimp [c, d]; linarith [hx.1.2, hx.2.2]
  have hd : (1 / 6 : ℝ) ≤ d := hc.trans hcd
  have hcpos : 0 < c := by linarith
  have hdpos : 0 < d := by linarith
  have hdelta : d - c ≤ goldbachB9AlphaGridStep n + goldbachB9BetaGridStep n := by
    dsimp [c, d]
    rw [goldbachB9AlphaGridPoint_succ, goldbachB9BetaGridPoint_succ]
    linarith [hx.1.1, hx.2.1]
  have hprod : (1 / 36 : ℝ) ≤ c * d := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hc) (sub_nonneg.mpr hd)]
  have hformula : 1 / c - liuLogKernel x = (d - c) / (c * d) := by
    change 1 / c - 1 / d = (d - c) / (c * d)
    field_simp [hcpos.ne', hdpos.ne']
  change 0 ≤ 1 / c - liuLogKernel x ∧ 1 / c - liuLogKernel x ≤
    36 * (goldbachB9AlphaGridStep n + goldbachB9BetaGridStep n)
  rw [hformula]
  constructor
  · exact div_nonneg (sub_nonneg.mpr hcd) (mul_pos hcpos hdpos).le
  · have hinv : 1 / (c * d) ≤ 36 := by
      simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 36) hprod
    calc
      (d - c) / (c * d) = (d - c) * (1 / (c * d)) := by ring
      _ ≤ (goldbachB9AlphaGridStep n + goldbachB9BetaGridStep n) * 36 :=
        mul_le_mul hdelta hinv (one_div_pos.mpr (mul_pos hcpos hdpos)).le
          (add_nonneg (goldbachB9AlphaGridStep_pos hn).le (goldbachB9BetaGridStep_pos hn).le)
      _ = _ := mul_comm _ _

theorem goldbachB9LogGrid_kernel_error (n : ℕ) :
    36 * (goldbachB9AlphaGridStep n + goldbachB9BetaGridStep n) =
      96 / (5 * (n : ℝ)) ∧ 96 / (5 * (n : ℝ)) ≤ 20 / (n : ℝ) := by
  constructor
  · unfold goldbachB9AlphaGridStep goldbachB9BetaGridStep
      goldbachB9AlphaGridWidth goldbachB9BetaGridWidth
    ring
  · have h : (96 / 5 : ℝ) ≤ 20 := by norm_num
    simpa only [div_div] using div_le_div_of_nonneg_right h (Nat.cast_nonneg n)

theorem goldbachB9LogGrid_kernel_variation {n : ℕ} (hn : 0 < n)
    (q : Fin n × Fin n) {x : ℝ × ℝ} (hx : x ∈ goldbachB9LogGridCell n q) :
    0 ≤ 1 / (1 - goldbachB9AlphaGridPoint n (q.1 + 1) -
      goldbachB9BetaGridPoint n (q.2 + 1)) - liuLogKernel x ∧
    1 / (1 - goldbachB9AlphaGridPoint n (q.1 + 1) -
      goldbachB9BetaGridPoint n (q.2 + 1)) - liuLogKernel x ≤ 20 / (n : ℝ) := by
  have h := goldbachB9LogGrid_kernel_variation_step hn q hx
  have he := goldbachB9LogGrid_kernel_error n
  rw [he.1] at h
  exact ⟨h.1, h.2.trans he.2⟩

theorem goldbachB9LogGridUpperIntegrand_le_integrand_add {n : ℕ} (hn : 0 < n)
    {x : ℝ × ℝ} (hx : x ∈ goldbachB9LogGridRegion n) :
    goldbachB9LogGridUpperIntegrand n x ≤ liuLogIntegrand x + 1600 / (n : ℝ) := by
  obtain ⟨q, hq, hxq⟩ := Set.mem_iUnion₂.mp hx
  rw [goldbachB9LogGridUpperIntegrand_eq_of_mem hn hq hxq]
  have hd := goldbachB9LogDensity_bounds (goldbachB9LogGridCell_subset_ambientBox hn q hxq)
  have hk := goldbachB9LogGrid_kernel_variation hn q hxq
  have hmul := mul_le_mul hk.2 hd.2 hd.1 (by positivity : 0 ≤ 20 / (n : ℝ))
  have heq : (20 / (n : ℝ)) * 80 = 1600 / (n : ℝ) := by ring
  rw [heq] at hmul
  unfold liuLogIntegrand
  nlinarith

private def b9UnitBox : Set (ℝ × ℝ) := Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1

private theorem volume_b9UnitBox :
    volume (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) = 1 := by
  rw [Measure.volume_eq_prod ℝ ℝ, Measure.prod_prod]
  norm_num [Real.volume_Icc]

theorem goldbachB9LogGridErrorConstant_pos : (0 : ℝ) < 10000 := by norm_num

/-- One-sided structural error for every positive mesh size, not an assumed limit. -/
theorem goldbachB9LogGridUpperSum_sub_mainIntegral_le (n : ℕ) (hn : 0 < n) :
    goldbachB9LogGridUpperSum n - goldbachB9MainIntegral ≤ 10000 / (n : ℝ) := by
  classical
  let E : Fin 3 → Set (ℝ × ℝ) :=
    ![goldbachB9LeftStrip n, goldbachB9BottomStrip n, goldbachB9ObliqueStrip n]
  have hEm : ∀ i, MeasurableSet (E i) := by
    intro i
    fin_cases i
    · exact measurableSet_goldbachB9LeftStrip n
    · exact measurableSet_goldbachB9BottomStrip n
    · exact measurableSet_goldbachB9ObliqueStrip n
  have hEf : ∀ i, volume (E i) ≠ ∞ := by
    intro i
    fin_cases i <;> simp [E, volume_goldbachB9LeftStrip,
      volume_goldbachB9BottomStrip, volume_goldbachB9ObliqueStrip]
  have hAf : volume b9UnitBox ≠ ∞ := by
    change volume (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) ≠ ∞
    rw [volume_b9UnitBox]
    norm_num
  have h := MathlibNt.Analysis.IntegralExcessCover.integral_sub_setIntegral_le_of_excess_cover
    volume (goldbachB9LogGridRegion n) goldbachB9LogSourceRegion b9UnitBox E
    (goldbachB9LogGridUpperIntegrand n) liuLogIntegrand (1600 / (n : ℝ)) 480
    (integrable_goldbachB9LogGridUpperIntegrand n hn)
    (integrableOn_goldbachB9LogIntegrand measurableSet_goldbachB9LogSourceRegion
      goldbachB9LogSourceRegion_subset_ambientBox)
    measurableSet_goldbachB9LogSourceRegion (measurableSet_Icc.prod measurableSet_Icc)
    hAf hEm hEf (by positivity) (by norm_num)
    (fun x hx => (goldbachB9LogIntegrand_bounds
      (goldbachB9LogSourceRegion_subset_ambientBox hx)).1)
    (fun _ hx => goldbachB9LogGridUpperIntegrand_eq_zero hx)
    (by
      intro x hx
      have hb := goldbachB9LogGridRegion_subset_ambientBox hn hx.1
      exact ⟨⟨by linarith [hb.1.1], by linarith [hb.1.2]⟩,
        ⟨by linarith [hb.2.1], by linarith [hb.2.2]⟩⟩)
    (fun _ hx => goldbachB9LogGridUpperIntegrand_le_integrand_add hn hx.1)
    (by
      intro x hx
      rcases goldbachB9LogGridRegion_excess_subset hn hx with (hl | hd) | ho
      · exact ⟨0, hl⟩
      · exact ⟨1, hd⟩
      · exact ⟨2, ho⟩)
    (fun _ hx => goldbachB9LogGridUpperIntegrand_le hn hx.1)
  rw [← goldbachB9LogGridUpperSum_eq_integral n hn,
    ← goldbachB9MainIntegral_eq_setIntegral, Fin.sum_univ_three] at h
  dsimp [E, b9UnitBox] at h
  simp only [Measure.real_def, volume_b9UnitBox, volume_goldbachB9LeftStrip,
    volume_goldbachB9BottomStrip, volume_goldbachB9ObliqueStrip,
    ENNReal.toReal_one, one_mul] at h
  rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ (17 / 240 : ℝ) / n),
    ENNReal.toReal_ofReal (by positivity : 0 ≤ (41 / 636 : ℝ) / n),
    ENNReal.toReal_ofReal (by positivity : 0 ≤ (1927 / 19080 : ℝ) / n)] at h
  refine h.trans ?_
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  field_simp [hnreal.ne']
  norm_num

theorem exists_goldbachB9LogGridUpperSum_le_mainIntegral_add
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ n : ℕ, 0 < n ∧ goldbachB9LogGridUpperSum n ≤ goldbachB9MainIntegral + δ := by
  obtain ⟨n, hn⟩ := exists_nat_gt ((10000 : ℝ) / δ)
  have hnp : (0 : ℝ) < n := (div_pos (by norm_num) hδ).trans hn
  have hnNat : 0 < n := by exact_mod_cast hnp
  have herr : (10000 : ℝ) / n ≤ δ := by
    apply (div_le_iff₀ hnp).mpr
    have h := (div_lt_iff₀ hδ).mp hn
    nlinarith
  refine ⟨n, hnNat, ?_⟩
  linarith [goldbachB9LogGridUpperSum_sub_mainIntegral_le n hnNat]

/-- First choose n from the tolerance, then take the fixed-n prime-size limit. -/
theorem goldbachB9PairLogKernel_le_mainIntegral_eventually
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      goldbachB9PairLogKernel N ≤ goldbachB9MainIntegral + δ := by
  obtain ⟨n, hn, hmesh⟩ :=
    exists_goldbachB9LogGridUpperSum_le_mainIntegral_add (δ / 2) (by positivity)
  obtain ⟨N₀, hN₀, hfixed⟩ :=
    goldbachB9PairLogKernel_le_gridUpperSum_eventually n hn (δ / 2) (by positivity)
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN
  linarith [hfixed N hN]

/-- The terminal statement displays the actual double integral explicitly. -/
theorem goldbachB9PairLogKernel_le_doubleIntegral_eventually
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      goldbachB9PairLogKernel N ≤
        (∫ u in (4 / 53 : ℝ)..(1 / 3),
          ∫ v in (1 / 3 : ℝ)..((1 - u) / 2), 1 / (u * v * (1 - u - v))) + δ :=
  goldbachB9PairLogKernel_le_mainIntegral_eventually δ hδ

end

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig