import MathlibNt.SieveTheory.LiLiuGoldbachB8LogGridRegion
import MathlibNt.SieveTheory.LiuPrimePairLogGridLimit

open Finset MeasureTheory Set
open scoped BigOperators Interval

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

noncomputable section

set_option maxHeartbeats 800000

open MathlibNt.SieveTheory.LiuWeight
open PrimeReciprocalLogRectangle

/-- The actual two-dimensional B8 main integral, without the sieve factor eight. -/
def goldbachB8MainIntegral : ℝ :=
  ∫ u in (3 / 11 : ℝ)..(1 / 3),
    ∫ v in u..((1 - u) / 2), 1 / (u * v * (1 - u - v))

def goldbachB8LogGridUpperIntegrand (n : ℕ) (x : ℝ × ℝ) : ℝ :=
  ∑ q ∈ goldbachB8LogGridCells n,
    (1 / (1 - goldbachB8AlphaGridPoint n (q.1 + 1) -
      goldbachB8BetaGridPoint n (q.2 + 1))) *
      (goldbachB8LogGridCell n q).indicator liuLogDensity x

theorem goldbachB8LogIntegrand_eq (u v : ℝ) :
    liuLogIntegrand (u, v) = 1 / (u * v * (1 - u - v)) := by
  simp only [liuLogIntegrand, liuLogKernel, liuLogDensity, one_div, mul_inv]
  ring

theorem goldbachB8LogDensity_bounds {x : ℝ × ℝ}
    (hx : x ∈ goldbachB8LogAmbientBox) :
    0 ≤ liuLogDensity x ∧ liuLogDensity x ≤ 16 := by
  have hprod : (1 / 16 : ℝ) ≤ x.1 * x.2 := by
    calc
      (1 / 16 : ℝ) = (1 / 4 : ℝ) * (1 / 4 : ℝ) := by norm_num
      _ ≤ x.1 * x.2 := mul_le_mul hx.1.1 hx.2.1 (by norm_num) (by linarith [hx.1.1])
  change 0 ≤ 1 / (x.1 * x.2) ∧ 1 / (x.1 * x.2) ≤ 16
  constructor
  · exact one_div_nonneg.mpr (by linarith)
  · rw [div_le_iff₀ (by linarith : 0 < x.1 * x.2)]
    linarith

theorem goldbachB8LogKernel_bounds {x : ℝ × ℝ}
    (hx : x ∈ goldbachB8LogAmbientBox) :
    0 ≤ liuLogKernel x ∧ liuLogKernel x ≤ 4 := by
  have hg := goldbachB8LogAmbientBox_gap hx
  change 0 ≤ 1 / (1 - x.1 - x.2) ∧ 1 / (1 - x.1 - x.2) ≤ 4
  constructor
  · exact one_div_nonneg.mpr (by linarith)
  · rw [div_le_iff₀ (by linarith : 0 < 1 - x.1 - x.2)]
    linarith

theorem goldbachB8LogIntegrand_bounds {x : ℝ × ℝ}
    (hx : x ∈ goldbachB8LogAmbientBox) :
    0 ≤ liuLogIntegrand x ∧ liuLogIntegrand x ≤ 64 := by
  have hd := goldbachB8LogDensity_bounds hx
  have hk := goldbachB8LogKernel_bounds hx
  exact ⟨mul_nonneg hk.1 hd.1,
    (mul_le_mul hk.2 hd.2 hd.1 (by norm_num)).trans (by norm_num)⟩

private theorem continuousOn_b8Density :
    ContinuousOn liuLogDensity goldbachB8LogAmbientBox := by
  unfold liuLogDensity
  apply ContinuousOn.div continuousOn_const
    (continuous_fst.continuousOn.mul continuous_snd.continuousOn)
  intro x hx
  exact mul_ne_zero (by linarith [hx.1.1]) (by linarith [hx.2.1])

private theorem continuousOn_b8Kernel :
    ContinuousOn liuLogKernel goldbachB8LogAmbientBox := by
  unfold liuLogKernel
  apply ContinuousOn.div continuousOn_const
    ((continuousOn_const.sub continuous_fst.continuousOn).sub continuous_snd.continuousOn)
  intro x hx
  have hg := goldbachB8LogAmbientBox_gap hx
  change 1 - x.1 - x.2 ≠ 0
  linarith

private theorem integrableOn_b8Density {s : Set (ℝ × ℝ)}
    (hs : MeasurableSet s) (hsub : s ⊆ goldbachB8LogAmbientBox) :
    IntegrableOn liuLogDensity s := by
  apply ContinuousOn.integrableOn_of_subset_isCompact continuousOn_b8Density
    isCompact_goldbachB8LogAmbientBox hs hsub
  exact (lt_of_le_of_lt (measure_mono hsub)
    isCompact_goldbachB8LogAmbientBox.measure_lt_top).ne

theorem integrableOn_goldbachB8LogIntegrand {s : Set (ℝ × ℝ)}
    (hs : MeasurableSet s) (hsub : s ⊆ goldbachB8LogAmbientBox) :
    IntegrableOn liuLogIntegrand s := by
  apply ContinuousOn.integrableOn_of_subset_isCompact
    (continuousOn_b8Kernel.mul continuousOn_b8Density)
    isCompact_goldbachB8LogAmbientBox hs hsub
  exact (lt_of_le_of_lt (measure_mono hsub)
    isCompact_goldbachB8LogAmbientBox.measure_lt_top).ne

theorem integrable_goldbachB8SourceIndicator :
    Integrable (goldbachB8LogSourceRegion.indicator liuLogIntegrand) :=
  integrable_indicator_of_integrableOn measurableSet_goldbachB8LogSourceRegion
    (integrableOn_goldbachB8LogIntegrand measurableSet_goldbachB8LogSourceRegion
      goldbachB8LogSourceRegion_subset_ambientBox)

private theorem goldbachB8MainIntegral_eq_iteratedSetIntegral :
    goldbachB8MainIntegral =
      ∫ u in Ioc (3 / 11 : ℝ) (1 / 3),
        ∫ v in Ioc u ((1 - u) / 2), liuLogIntegrand (u, v) := by
  unfold goldbachB8MainIntegral
  rw [intervalIntegral.integral_of_le (by norm_num : (3 / 11 : ℝ) ≤ 1 / 3)]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro u hu
  change (∫ v in u..((1 - u) / 2), 1 / (u * v * (1 - u - v))) =
    ∫ v in Ioc u ((1 - u) / 2), liuLogIntegrand (u, v)
  rw [intervalIntegral.integral_of_le (by linarith [hu.2] : u ≤ (1 - u) / 2)]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro v _
  exact (goldbachB8LogIntegrand_eq u v).symm

/-- Fubini identifies the continuous half-open triangle with the stated double integral. -/
theorem goldbachB8MainIntegral_eq_setIntegral :
    goldbachB8MainIntegral = ∫ x in goldbachB8LogSourceRegion, liuLogIntegrand x := by
  rw [goldbachB8MainIntegral_eq_iteratedSetIntegral]
  let F := goldbachB8LogSourceRegion.indicator liuLogIntegrand
  have hF : Integrable F := integrable_goldbachB8SourceIndicator
  have hinner (u : ℝ) :
      (∫ v, F (u, v)) =
        (Ioc (3 / 11 : ℝ) (1 / 3)).indicator
          (fun u => ∫ v in Ioc u ((1 - u) / 2), liuLogIntegrand (u, v)) u := by
    by_cases hu : u ∈ Ioc (3 / 11 : ℝ) (1 / 3)
    · rw [indicator_of_mem hu, ← integral_indicator measurableSet_Ioc]
      apply integral_congr_ae
      filter_upwards with v
      have hmem : (u, v) ∈ goldbachB8LogSourceRegion ↔ v ∈ Ioc u ((1 - u) / 2) :=
        and_iff_right hu
      change goldbachB8LogSourceRegion.indicator liuLogIntegrand (u, v) =
        (Ioc u ((1 - u) / 2)).indicator (fun v => liuLogIntegrand (u, v)) v
      by_cases hv : v ∈ Ioc u ((1 - u) / 2)
      · rw [indicator_of_mem (hmem.mpr hv), indicator_of_mem hv]
      · rw [indicator_of_notMem (fun h => hv (hmem.mp h)), indicator_of_notMem hv]
    · rw [indicator_of_notMem hu]
      apply integral_eq_zero_of_ae
      filter_upwards with v
      exact indicator_of_notMem (fun h => hu h.1) _
  have hFubini : (∫ z, F z) = ∫ u, ∫ v, F (u, v) := by
    rw [Measure.volume_eq_prod ℝ ℝ] at hF ⊢
    exact integral_prod F hF
  calc
    _ = ∫ u, (Ioc (3 / 11 : ℝ) (1 / 3)).indicator
        (fun u => ∫ v in Ioc u ((1 - u) / 2), liuLogIntegrand (u, v)) u := by
      rw [integral_indicator measurableSet_Ioc]
    _ = ∫ u, ∫ v, F (u, v) := by
      apply integral_congr_ae
      filter_upwards with u
      exact (hinner u).symm
    _ = ∫ z, F z := hFubini.symm
    _ = _ := integral_indicator measurableSet_goldbachB8LogSourceRegion

theorem goldbachB8MainIntegral_nonneg : 0 ≤ goldbachB8MainIntegral := by
  rw [goldbachB8MainIntegral_eq_setIntegral]
  apply setIntegral_nonneg measurableSet_goldbachB8LogSourceRegion
  intro x hx
  exact (goldbachB8LogIntegrand_bounds (goldbachB8LogSourceRegion_subset_ambientBox hx)).1

theorem integrable_goldbachB8LogGridUpperIntegrand (n : ℕ) (hn : 0 < n) :
    Integrable (goldbachB8LogGridUpperIntegrand n) := by
  classical
  exact integrable_finsetSum _ fun q _ =>
    (integrable_indicator_of_integrableOn (measurableSet_goldbachB8LogGridCell n q)
      (integrableOn_b8Density (measurableSet_goldbachB8LogGridCell n q)
        (goldbachB8LogGridCell_subset_ambientBox hn q))).const_mul _

/-- This is the production upper sum, with its original selected cells unchanged. -/
theorem goldbachB8LogGridUpperSum_eq_integral (n : ℕ) (hn : 0 < n) :
    goldbachB8LogGridUpperSum n = ∫ x, goldbachB8LogGridUpperIntegrand n x := by
  classical
  unfold goldbachB8LogGridUpperSum goldbachB8LogGridUpperIntegrand
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro q _
    rw [integral_const_mul, integral_indicator (measurableSet_goldbachB8LogGridCell n q)]
    rw [logarithmicRectangleMass_eq_setIntegral
      (goldbachB8AlphaGridPoint_pos n q.1) (goldbachB8AlphaGridPoint_lt_succ hn)
      (goldbachB8BetaGridPoint_pos n q.2) (goldbachB8BetaGridPoint_lt_succ hn)]
    rfl
  · intro q _
    exact (integrable_indicator_of_integrableOn (measurableSet_goldbachB8LogGridCell n q)
      (integrableOn_b8Density (measurableSet_goldbachB8LogGridCell n q)
        (goldbachB8LogGridCell_subset_ambientBox hn q))).const_mul _

private theorem b8UpperIntegrand_eq_of_mem {n : ℕ} (hn : 0 < n)
    {q : Fin n × Fin n} (hq : q ∈ goldbachB8LogGridCells n)
    {x : ℝ × ℝ} (hx : x ∈ goldbachB8LogGridCell n q) :
    goldbachB8LogGridUpperIntegrand n x =
      (1 / (1 - goldbachB8AlphaGridPoint n (q.1 + 1) -
        goldbachB8BetaGridPoint n (q.2 + 1))) * liuLogDensity x := by
  classical
  unfold goldbachB8LogGridUpperIntegrand
  rw [Finset.sum_eq_single q]
  · rw [indicator_of_mem hx]
  · intro r _ hrq
    have hnot : x ∉ goldbachB8LogGridCell n r := fun hxr =>
      Set.disjoint_left.mp
        (goldbachB8LogGridCell_pairwiseDisjoint hn (mem_univ q) (mem_univ r) hrq.symm)
        hx hxr
    rw [indicator_of_notMem hnot, mul_zero]
  · exact fun h => (h hq).elim

private theorem b8UpperIntegrand_eq_zero {n : ℕ} {x : ℝ × ℝ}
    (hx : x ∉ goldbachB8LogGridRegion n) : goldbachB8LogGridUpperIntegrand n x = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro q hq
  have hnot : x ∉ goldbachB8LogGridCell n q :=
    fun h => hx (Set.mem_iUnion₂.mpr ⟨q, hq, h⟩)
  rw [indicator_of_notMem hnot, mul_zero]

private theorem b8CornerKernel_le_four {n : ℕ} (hn : 0 < n) (q : Fin n × Fin n) :
    1 / (1 - goldbachB8AlphaGridPoint n (q.1 + 1) -
      goldbachB8BetaGridPoint n (q.2 + 1)) ≤ 4 := by
  have hg := goldbachB8LogGridCell_cornerGap_ge hn q
  rw [div_le_iff₀ (goldbachB8LogGridCell_cornerGap_pos hn q)]
  linarith

private theorem b8UpperIntegrand_le_sixtyFour {n : ℕ} (hn : 0 < n)
    {x : ℝ × ℝ} (hx : x ∈ goldbachB8LogGridRegion n) :
    goldbachB8LogGridUpperIntegrand n x ≤ 64 := by
  obtain ⟨q, hq, hxq⟩ := Set.mem_iUnion₂.mp hx
  rw [b8UpperIntegrand_eq_of_mem hn hq hxq]
  have hd := goldbachB8LogDensity_bounds (goldbachB8LogGridCell_subset_ambientBox hn q hxq)
  exact (mul_le_mul (b8CornerKernel_le_four hn q) hd.2 hd.1 (by norm_num)).trans
    (by norm_num)

/-- The reciprocal gap changes by at most `4/n` on every ambient cell. -/
theorem goldbachB8LogGrid_kernel_variation {n : ℕ} (hn : 0 < n)
    (q : Fin n × Fin n) {x : ℝ × ℝ} (hx : x ∈ goldbachB8LogGridCell n q) :
    0 ≤ 1 / (1 - goldbachB8AlphaGridPoint n (q.1 + 1) -
      goldbachB8BetaGridPoint n (q.2 + 1)) - liuLogKernel x ∧
    1 / (1 - goldbachB8AlphaGridPoint n (q.1 + 1) -
      goldbachB8BetaGridPoint n (q.2 + 1)) - liuLogKernel x ≤ 4 / (n : ℝ) := by
  let c := 1 - goldbachB8AlphaGridPoint n (q.1 + 1) -
    goldbachB8BetaGridPoint n (q.2 + 1)
  let d := 1 - x.1 - x.2
  have hc : (1 / 4 : ℝ) ≤ c := by
    have h := goldbachB8LogGridCell_cornerGap_ge hn q
    dsimp [c]
    linarith
  have hcd : c ≤ d := by dsimp [c, d]; linarith [hx.1.2, hx.2.2]
  have hd : (1 / 4 : ℝ) ≤ d := hc.trans hcd
  have hcpos : 0 < c := by linarith
  have hdpos : 0 < d := by linarith
  have hdelta : d - c ≤ goldbachB8AlphaGridStep n + goldbachB8BetaGridStep n := by
    dsimp [c, d]
    rw [goldbachB8AlphaGridPoint_succ, goldbachB8BetaGridPoint_succ]
    linarith [hx.1.1, hx.2.1]
  have hstep : goldbachB8AlphaGridStep n + goldbachB8BetaGridStep n =
      (13 / 66 : ℝ) / n := by
    unfold goldbachB8AlphaGridStep goldbachB8BetaGridStep
      goldbachB8AlphaGridWidth goldbachB8BetaGridWidth
    ring
  have hprod : (1 / 16 : ℝ) ≤ c * d := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hc) (sub_nonneg.mpr hd)]
  have hformula : 1 / c - liuLogKernel x = (d - c) / (c * d) := by
    change 1 / c - 1 / d = (d - c) / (c * d)
    field_simp [hcpos.ne', hdpos.ne']
  change 0 ≤ 1 / c - liuLogKernel x ∧ 1 / c - liuLogKernel x ≤ 4 / (n : ℝ)
  rw [hformula]
  constructor
  · exact div_nonneg (sub_nonneg.mpr hcd) (mul_pos hcpos hdpos).le
  · have hinv : 1 / (c * d) ≤ 16 := by
      simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 16) hprod
    calc
      (d - c) / (c * d) = (d - c) * (1 / (c * d)) := by ring
      _ ≤ (goldbachB8AlphaGridStep n + goldbachB8BetaGridStep n) * 16 :=
        mul_le_mul hdelta hinv (one_div_pos.mpr (mul_pos hcpos hdpos)).le
          (add_nonneg (goldbachB8AlphaGridStep_pos hn).le (goldbachB8BetaGridStep_pos hn).le)
      _ ≤ 4 / (n : ℝ) := by
        rw [hstep]
        have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
        field_simp [hnreal.ne']
        norm_num

private theorem b8UpperIntegrand_le_integrand_add {n : ℕ} (hn : 0 < n)
    {x : ℝ × ℝ} (hx : x ∈ goldbachB8LogGridRegion n) :
    goldbachB8LogGridUpperIntegrand n x ≤ liuLogIntegrand x + 64 / (n : ℝ) := by
  obtain ⟨q, hq, hxq⟩ := Set.mem_iUnion₂.mp hx
  rw [b8UpperIntegrand_eq_of_mem hn hq hxq]
  have hd := goldbachB8LogDensity_bounds (goldbachB8LogGridCell_subset_ambientBox hn q hxq)
  have hk := goldbachB8LogGrid_kernel_variation hn q hxq
  have hmul := mul_le_mul hk.2 hd.2 hd.1 (by positivity : 0 ≤ 4 / (n : ℝ))
  have heq : (4 / (n : ℝ)) * 16 = 64 / (n : ℝ) := by ring
  rw [heq] at hmul
  unfold liuLogIntegrand
  nlinarith

private def b8UnitBox : Set (ℝ × ℝ) := Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1

private theorem volume_b8UnitBox :
    volume (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) = 1 := by
  rw [Measure.volume_eq_prod ℝ ℝ, Measure.prod_prod]
  norm_num [Real.volume_Icc]

private theorem b8Indicator_nonneg {s : Set (ℝ × ℝ)} {f : ℝ × ℝ → ℝ}
    (h : ∀ x ∈ s, 0 ≤ f x) (x : ℝ × ℝ) : 0 ≤ s.indicator f x := by
  classical
  by_cases hx : x ∈ s
  · rw [indicator_of_mem hx]
    exact h x hx
  · rw [indicator_of_notMem hx]

private theorem b8UpperIntegrand_majorized {n : ℕ} (hn : 0 < n) (x : ℝ × ℝ) :
    goldbachB8LogGridUpperIntegrand n x ≤
      goldbachB8LogSourceRegion.indicator liuLogIntegrand x +
        b8UnitBox.indicator (fun _ => 64 / (n : ℝ)) x +
        (goldbachB8LeftStrip n).indicator (fun _ => (64 : ℝ)) x +
        (goldbachB8DiagonalStrip n).indicator (fun _ => (64 : ℝ)) x +
        (goldbachB8ObliqueStrip n).indicator (fun _ => (64 : ℝ)) x := by
  have hS := b8Indicator_nonneg (fun x hx =>
    (goldbachB8LogIntegrand_bounds (goldbachB8LogSourceRegion_subset_ambientBox hx)).1) x
  have hU := b8Indicator_nonneg
    (s := b8UnitBox) (f := fun _ => 64 / (n : ℝ)) (by intros; positivity) x
  have hL := b8Indicator_nonneg
    (s := goldbachB8LeftStrip n) (f := fun _ => (64 : ℝ)) (by intros; norm_num) x
  have hD := b8Indicator_nonneg
    (s := goldbachB8DiagonalStrip n) (f := fun _ => (64 : ℝ)) (by intros; norm_num) x
  have hO := b8Indicator_nonneg
    (s := goldbachB8ObliqueStrip n) (f := fun _ => (64 : ℝ)) (by intros; norm_num) x
  by_cases hg : x ∈ goldbachB8LogGridRegion n
  · by_cases hs : x ∈ goldbachB8LogSourceRegion
    · have hb := goldbachB8LogGridRegion_subset_ambientBox hn hg
      have hu : x ∈ b8UnitBox :=
        ⟨⟨by linarith [hb.1.1], by linarith [hb.1.2]⟩,
          ⟨by linarith [hb.2.1], by linarith [hb.2.2]⟩⟩
      rw [indicator_of_mem hs, indicator_of_mem hu]
      linarith [b8UpperIntegrand_le_integrand_add hn hg]
    · rw [indicator_of_notMem hs]
      have hb := b8UpperIntegrand_le_sixtyFour hn hg
      rcases goldbachB8LogGridRegion_excess_subset hn ⟨hg, hs⟩ with (hl | hd) | ho
      · rw [indicator_of_mem hl]
        linarith
      · rw [indicator_of_mem hd]
        linarith
      · rw [indicator_of_mem ho]
        linarith
  · rw [b8UpperIntegrand_eq_zero hg]
    linarith

theorem goldbachB8LogGridErrorConstant_pos : (0 : ℝ) < 1000 := by norm_num

/-- One-sided structural error for every positive mesh size, not an assumed limit. -/
theorem goldbachB8LogGridUpperSum_sub_mainIntegral_le (n : ℕ) (hn : 0 < n) :
    goldbachB8LogGridUpperSum n - goldbachB8MainIntegral ≤ 1000 / (n : ℝ) := by
  let fSource := goldbachB8LogSourceRegion.indicator liuLogIntegrand
  let fUnit := b8UnitBox.indicator (fun _ => 64 / (n : ℝ))
  let fLeft := (goldbachB8LeftStrip n).indicator (fun _ => (64 : ℝ))
  let fDiagonal := (goldbachB8DiagonalStrip n).indicator (fun _ => (64 : ℝ))
  let fOblique := (goldbachB8ObliqueStrip n).indicator (fun _ => (64 : ℝ))
  have hSource : Integrable fSource := integrable_goldbachB8SourceIndicator
  have hUnit : Integrable fUnit := by
    apply integrable_indicator_of_integrableOn (measurableSet_Icc.prod measurableSet_Icc)
    apply integrableOn_const
    · rw [volume_b8UnitBox]
      norm_num
    · finiteness
  have hLeft : Integrable fLeft := by
    apply integrable_indicator_of_integrableOn (measurableSet_goldbachB8LeftStrip n)
    apply integrableOn_const
    · rw [volume_goldbachB8LeftStrip]
      exact ENNReal.ofReal_ne_top
    · finiteness
  have hDiagonal : Integrable fDiagonal := by
    apply integrable_indicator_of_integrableOn (measurableSet_goldbachB8DiagonalStrip n)
    apply integrableOn_const
    · rw [volume_goldbachB8DiagonalStrip]
      exact ENNReal.ofReal_ne_top
    · finiteness
  have hOblique : Integrable fOblique := by
    apply integrable_indicator_of_integrableOn (measurableSet_goldbachB8ObliqueStrip n)
    apply integrableOn_const
    · rw [volume_goldbachB8ObliqueStrip]
      exact ENNReal.ofReal_ne_top
    · finiteness
  have hmono : (∫ x, goldbachB8LogGridUpperIntegrand n x) ≤
      ∫ x, (((fSource x + fUnit x) + fLeft x) + fDiagonal x) + fOblique x :=
    integral_mono (integrable_goldbachB8LogGridUpperIntegrand n hn)
      ((((hSource.add hUnit).add hLeft).add hDiagonal).add hOblique)
      (b8UpperIntegrand_majorized hn)
  rw [← goldbachB8LogGridUpperSum_eq_integral n hn] at hmono
  have hOuter := integral_add (((hSource.add hUnit).add hLeft).add hDiagonal) hOblique
  have hMid := integral_add ((hSource.add hUnit).add hLeft) hDiagonal
  have hInner := integral_add (hSource.add hUnit) hLeft
  have hFirst := integral_add hSource hUnit
  simp only [Pi.add_apply] at hOuter hMid hInner hFirst
  rw [hOuter, hMid, hInner, hFirst] at hmono
  dsimp [fSource, fUnit, fLeft, fDiagonal, fOblique, b8UnitBox] at hmono
  rw [integral_indicator measurableSet_goldbachB8LogSourceRegion,
    ← goldbachB8MainIntegral_eq_setIntegral,
    integral_indicator_const (64 / (n : ℝ)) (measurableSet_Icc.prod measurableSet_Icc),
    integral_indicator_const (64 : ℝ) (measurableSet_goldbachB8LeftStrip n),
    integral_indicator_const (64 : ℝ) (measurableSet_goldbachB8DiagonalStrip n),
    integral_indicator_const (64 : ℝ) (measurableSet_goldbachB8ObliqueStrip n),
    Measure.real_def, volume_b8UnitBox,
    Measure.real_def, volume_goldbachB8LeftStrip,
    Measure.real_def, volume_goldbachB8DiagonalStrip,
    Measure.real_def, volume_goldbachB8ObliqueStrip] at hmono
  simp only [ENNReal.toReal_one, smul_eq_mul] at hmono
  rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ (5 / 528 : ℝ) / n),
    ENNReal.toReal_ofReal (by positivity : 0 ≤ (13 / 1089 : ℝ) / n),
    ENNReal.toReal_ofReal (by positivity : 0 ≤ (41 / 4356 : ℝ) / n)] at hmono
  have herr : 64 / (n : ℝ) + (5 / 528 : ℝ) / n * 64 +
      (13 / 1089 : ℝ) / n * 64 + (41 / 4356 : ℝ) / n * 64 ≤ 1000 / (n : ℝ) := by
    have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
    field_simp [hnreal.ne']
    norm_num
  linarith

/-- Choose the mesh after the tolerance; no prime-size threshold is selected here. -/
theorem exists_goldbachB8LogGridUpperSum_le_mainIntegral_add
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ n : ℕ, 0 < n ∧ goldbachB8LogGridUpperSum n ≤ goldbachB8MainIntegral + δ := by
  obtain ⟨n, hn⟩ := exists_nat_gt ((1000 : ℝ) / δ)
  have hnp : (0 : ℝ) < n := (div_pos (by norm_num) hδ).trans hn
  have hnNat : 0 < n := by exact_mod_cast hnp
  have herr : (1000 : ℝ) / n ≤ δ := by
    apply (div_le_iff₀ hnp).mpr
    have h := (div_lt_iff₀ hδ).mp hn
    nlinarith
  refine ⟨n, hnNat, ?_⟩
  linarith [goldbachB8LogGridUpperSum_sub_mainIntegral_le n hnNat]

end

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig