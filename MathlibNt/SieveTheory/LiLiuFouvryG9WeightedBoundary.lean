import MathlibNt.SieveTheory.LiLiuFouvryG9RelaxedIntegralContinuous
import MathlibNt.SieveTheory.LiLiuGoldbachB9LogGridLimit

open MeasureTheory Set
open scoped BigOperators Interval
noncomputable section
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
open MathlibNt.SieveTheory.LiuWeight PrimeReciprocalLogRectangle
set_option maxHeartbeats 800000

def fouvryG9WeightedSource : Set (ℝ × ℝ) :=
  {x | x.1 ∈ Ioc (4/53) (1/10) ∧ x.2 ∈ Ioc (1/3) ((1-x.1)/2)}

def fouvryG9WeightedIntegrand (x : ℝ × ℝ) : ℝ :=
  1 / (x.1*x.2*(1-x.1-x.2)*(1-x.1))

def fouvryG9WeightedUpperIntegrand (n : ℕ) (h : ℝ) (x : ℝ × ℝ) : ℝ :=
  ∑ q ∈ fouvryG9RelaxedIntegralCells n h,
    fouvryG9RelaxedIntegralCorner n 0 q *
      (goldbachB9LogGridCell n q).indicator liuLogDensity x

theorem measurableSet_fouvryG9WeightedSource : MeasurableSet fouvryG9WeightedSource := by
  exact (measurableSet_Ioc.preimage measurable_fst).inter
    ((measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd (by fun_prop)))

theorem fouvryG9WeightedSource_subset_ambient :
    fouvryG9WeightedSource ⊆ goldbachB9LogAmbientBox := by
  intro x hx
  exact ⟨⟨by linarith [hx.1.1], by linarith [hx.1.2]⟩,
    ⟨by linarith [hx.2.1], by linarith [hx.1.1, hx.2.2]⟩⟩

theorem continuousOn_fouvryG9WeightedIntegrand :
    ContinuousOn fouvryG9WeightedIntegrand goldbachB9LogAmbientBox := by
  unfold fouvryG9WeightedIntegrand
  apply ContinuousOn.div continuousOn_const (by fun_prop)
  intro x hx
  have hg := goldbachB9LogAmbientBox_gap hx
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by linarith [hx.1.1])
    (by linarith [hx.2.1])) (by linarith)) (by linarith [hx.1.2])

theorem integrableOn_fouvryG9WeightedIntegrand {s : Set (ℝ × ℝ)}
    (hs : MeasurableSet s) (hsub : s ⊆ goldbachB9LogAmbientBox) :
    IntegrableOn fouvryG9WeightedIntegrand s := by
  apply ContinuousOn.integrableOn_of_subset_isCompact continuousOn_fouvryG9WeightedIntegrand
    isCompact_goldbachB9LogAmbientBox hs hsub
  exact (lt_of_le_of_lt (measure_mono hsub)
    isCompact_goldbachB9LogAmbientBox.measure_lt_top).ne

theorem integrable_fouvryG9WeightedSourceIndicator :
    Integrable (fouvryG9WeightedSource.indicator fouvryG9WeightedIntegrand) :=
  integrable_indicator_of_integrableOn measurableSet_fouvryG9WeightedSource
    (integrableOn_fouvryG9WeightedIntegrand measurableSet_fouvryG9WeightedSource
      fouvryG9WeightedSource_subset_ambient)

theorem fouvryG9RelaxedIntegralLow_eq_iteratedSetIntegral :
    fouvryG9RelaxedIntegralLow =
      ∫ u in Ioc (4 / 53 : ℝ) (1 / 10),
        ∫ v in Ioc (1 / 3) ((1 - u) / 2), fouvryG9WeightedIntegrand (u, v) := by
  unfold fouvryG9RelaxedIntegralLow
  rw [intervalIntegral.integral_of_le (by norm_num : (4 / 53 : ℝ) ≤ 1 / 10)]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro u hu
  change (∫ v in (1 / 3 : ℝ)..((1 - u) / 2), 1 / (u * v * (1 - u - v) * (1-u))) =
    ∫ v in Ioc (1 / 3) ((1 - u) / 2), fouvryG9WeightedIntegrand (u, v)
  rw [intervalIntegral.integral_of_le (by linarith [hu.2] : (1 / 3 : ℝ) ≤ (1 - u) / 2)]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro v _
  rfl

theorem fouvryG9WeightedSourceIndicator_integral_section (u : ℝ) :
    (∫ v, fouvryG9WeightedSource.indicator fouvryG9WeightedIntegrand (u, v)) =
      (Ioc (4 / 53 : ℝ) (1 / 10)).indicator
        (fun u => ∫ v in Ioc (1 / 3) ((1 - u) / 2), fouvryG9WeightedIntegrand (u, v)) u := by
  by_cases hu : u ∈ Ioc (4 / 53 : ℝ) (1 / 10)
  · rw [indicator_of_mem hu, ← integral_indicator measurableSet_Ioc]
    apply integral_congr_ae
    filter_upwards with v
    have hmem : (u, v) ∈ fouvryG9WeightedSource ↔ v ∈ Ioc (1 / 3) ((1 - u) / 2) :=
      and_iff_right hu
    change fouvryG9WeightedSource.indicator fouvryG9WeightedIntegrand (u, v) =
      (Ioc (1 / 3) ((1 - u) / 2)).indicator (fun v => fouvryG9WeightedIntegrand (u, v)) v
    by_cases hv : v ∈ Ioc (1 / 3) ((1 - u) / 2)
    · rw [indicator_of_mem (hmem.mpr hv), indicator_of_mem hv]
    · rw [indicator_of_notMem (fun h => hv (hmem.mp h)), indicator_of_notMem hv]
  · rw [indicator_of_notMem hu]
    apply integral_eq_zero_of_ae
    filter_upwards with v
    exact indicator_of_notMem (fun h => hu h.1) _

/-- Fubini is applied to an integrable indicator, not to an unspecified integral. -/
theorem fouvryG9RelaxedIntegralLow_eq_setIntegral :
    fouvryG9RelaxedIntegralLow = ∫ x in fouvryG9WeightedSource, fouvryG9WeightedIntegrand x := by
  rw [fouvryG9RelaxedIntegralLow_eq_iteratedSetIntegral]
  let F := fouvryG9WeightedSource.indicator fouvryG9WeightedIntegrand
  have hF : Integrable F := integrable_fouvryG9WeightedSourceIndicator
  have hFubini : (∫ z, F z) = ∫ u, ∫ v, F (u, v) := by
    rw [Measure.volume_eq_prod ℝ ℝ] at hF ⊢
    exact integral_prod F hF
  calc
    _ = ∫ u, (Ioc (4 / 53 : ℝ) (1 / 10)).indicator
        (fun u => ∫ v in Ioc (1 / 3) ((1 - u) / 2), fouvryG9WeightedIntegrand (u, v)) u := by
      rw [integral_indicator measurableSet_Ioc]
    _ = ∫ u, ∫ v, F (u, v) := by
      apply integral_congr_ae
      filter_upwards with u
      exact (fouvryG9WeightedSourceIndicator_integral_section u).symm
    _ = ∫ z, F z := hFubini.symm
    _ = _ := integral_indicator measurableSet_fouvryG9WeightedSource

theorem integrable_fouvryG9WeightedUpperIntegrand (n : ℕ) (hn : 0 < n) (h : ℝ) :
    Integrable (fouvryG9WeightedUpperIntegrand n h) := by
  classical
  exact integrable_finsetSum _ fun q _ =>
    (integrable_indicator_of_integrableOn (measurableSet_goldbachB9LogGridCell n q)
      (integrableOn_goldbachB9LogDensity (measurableSet_goldbachB9LogGridCell n q)
        (goldbachB9LogGridCell_subset_ambientBox hn q))).const_mul _

/-- The selected-cell sum retains its actual logarithmic rectangle masses. -/
theorem fouvryG9RelaxedIntegralUpperSum_eq_integral (n : ℕ) (hn : 0 < n) (h : ℝ) :
    fouvryG9RelaxedIntegralUpperSum n h 0 = ∫ x, fouvryG9WeightedUpperIntegrand n h x := by
  classical
  unfold fouvryG9RelaxedIntegralUpperSum fouvryG9WeightedUpperIntegrand
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


end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
