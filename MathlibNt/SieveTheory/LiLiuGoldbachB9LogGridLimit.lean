import MathlibNt.Analysis.LogGridEstimates
import MathlibNt.Analysis.MovingIntervalIntegral
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
  exact continuousOn_goldbachB9LogDensity.integrableOn_of_subset_isCompact isCompact_goldbachB9LogAmbientBox hs hsub
    (ne_top_of_le_ne_top isCompact_goldbachB9LogAmbientBox.measure_ne_top (measure_mono hsub))

theorem integrableOn_goldbachB9LogIntegrand {s : Set (ℝ × ℝ)}
    (hs : MeasurableSet s) (hsub : s ⊆ goldbachB9LogAmbientBox) :
    IntegrableOn liuLogIntegrand s := by
  exact continuousOn_goldbachB9LogIntegrand.integrableOn_of_subset_isCompact isCompact_goldbachB9LogAmbientBox hs hsub
    (ne_top_of_le_ne_top isCompact_goldbachB9LogAmbientBox.measure_ne_top (measure_mono hsub))

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
  exact MathlibNt.Analysis.integral_indicator_moving_Ioc_section
    (Ioc (4 / 53 : ℝ) (1 / 3)) (fun _ => (1 / 3 : ℝ))
    (fun u => (1 - u) / 2) liuLogIntegrand u

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
  exact (MathlibNt.Analysis.setIntegral_moving_Ioc_eq_iterated
    (Ioc (4 / 53 : ℝ) (1 / 3)) (fun _ => (1 / 3 : ℝ)) (fun u => (1 - u) / 2)
    liuLogIntegrand measurableSet_Ioc measurableSet_goldbachB9LogSourceRegion
    (integrableOn_goldbachB9LogIntegrand measurableSet_goldbachB9LogSourceRegion
      goldbachB9LogSourceRegion_subset_ambientBox)).symm

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
  unfold goldbachB9LogGridUpperIntegrand
  exact MathlibNt.Analysis.LogGridEstimates.weighted_sum_eq_of_mem _ _ _ _
    (goldbachB9LogGridCell_pairwiseDisjoint hn) hq hx

theorem goldbachB9LogGridUpperIntegrand_eq_zero {n : ℕ} {x : ℝ × ℝ}
    (hx : x ∉ goldbachB9LogGridRegion n) : goldbachB9LogGridUpperIntegrand n x = 0 := by
  unfold goldbachB9LogGridUpperIntegrand
  exact MathlibNt.Analysis.LogGridEstimates.weighted_sum_zero _ _ _ _ hx

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
  simp only [goldbachB9LogGridCell, goldbachB9AlphaGridPoint_succ, goldbachB9BetaGridPoint_succ] at hx
  simp only [goldbachB9AlphaGridPoint_succ, goldbachB9BetaGridPoint_succ, liuLogKernel]
  apply MathlibNt.Analysis.LogGridEstimates.cell_reciprocal_variation hx
    (l := 1 / 6) (by norm_num) ?_ (by have := goldbachB9AlphaGridStep_pos hn; have := goldbachB9BetaGridStep_pos hn; positivity) ?_
  · have h := goldbachB9LogGridCell_cornerGap_ge hn q
    rw [goldbachB9AlphaGridPoint_succ, goldbachB9BetaGridPoint_succ] at h
    linarith
  · ring_nf
    exact le_rfl

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
  have h := MathlibNt.Analysis.LogGridEstimates.integral_sub_le_three_strips
    (goldbachB9LogGridRegion n) goldbachB9LogSourceRegion
    (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1)
    (goldbachB9LeftStrip n) (goldbachB9BottomStrip n) (goldbachB9ObliqueStrip n)
    (goldbachB9LogGridUpperIntegrand n) liuLogIntegrand (1600 / (n : ℝ)) 480
    ((17 / 240 : ℝ) / n) ((41 / 636 : ℝ) / n) ((1927 / 19080 : ℝ) / n)
    (integrable_goldbachB9LogGridUpperIntegrand n hn)
    (integrableOn_goldbachB9LogIntegrand measurableSet_goldbachB9LogSourceRegion
      goldbachB9LogSourceRegion_subset_ambientBox)
    measurableSet_goldbachB9LogSourceRegion (measurableSet_Icc.prod measurableSet_Icc)
    volume_b9UnitBox
    (measurableSet_goldbachB9LeftStrip n) (measurableSet_goldbachB9BottomStrip n)
    (measurableSet_goldbachB9ObliqueStrip n)
    (volume_goldbachB9LeftStrip n) (volume_goldbachB9BottomStrip n)
    (volume_goldbachB9ObliqueStrip n)
    (by positivity) (by positivity) (by positivity) (by positivity) (by norm_num)
    (fun _ hx => (goldbachB9LogIntegrand_bounds
      (goldbachB9LogSourceRegion_subset_ambientBox hx)).1)
    (fun _ hx => goldbachB9LogGridUpperIntegrand_eq_zero hx)
    (by
      intro x hx
      have hb := goldbachB9LogGridRegion_subset_ambientBox hn hx.1
      exact ⟨⟨by linarith [hb.1.1], by linarith [hb.1.2]⟩,
        ⟨by linarith [hb.2.1], by linarith [hb.2.2]⟩⟩)
    (fun _ hx => goldbachB9LogGridUpperIntegrand_le_integrand_add hn hx.1)
    (goldbachB9LogGridRegion_excess_subset hn) (fun _ hx => goldbachB9LogGridUpperIntegrand_le hn hx.1)
  rw [← goldbachB9LogGridUpperSum_eq_integral n hn, ← goldbachB9MainIntegral_eq_setIntegral] at h
  refine h.trans ?_
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  field_simp
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