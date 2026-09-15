import OriginalBoundaryGrid
open MeasureTheory Set
open scoped BigOperators Interval
noncomputable section
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
open MathlibNt.SieveTheory.LiuWeight
open MathlibNt.SieveTheory.PrimeReciprocalLogRectangle
namespace OriginalU8.Weighted
variable {a : ℝ}
def source (a : ℝ) : Set (ℝ × ℝ) :=
  {x | x.1 ∈ Ioc a (1/10) ∧ x.2 ∈ Ioc (1/3) ((1-x.1)/2)}

def upperIntegrand (a : ℝ) (n : ℕ) (h : ℝ) (x : ℝ × ℝ) : ℝ :=
  ∑ q ∈ cells a n h,
    fouvryG9RelaxedIntegralCorner n 0 q *
      (goldbachB9LogGridCell n q).indicator liuLogDensity x

theorem measurableSet_source : MeasurableSet (source a) := by
  exact (measurableSet_Ioc.preimage measurable_fst).inter
    ((measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd (by fun_prop)))

theorem source_subset_ambient (ha : 1/20 ≤ a) :
    (source a) ⊆ goldbachB9LogAmbientBox := by
  intro x hx
  exact ⟨⟨by linarith [hx.1.1], by linarith [hx.1.2]⟩,
    ⟨by linarith [hx.2.1], by linarith [hx.1.1, hx.2.2]⟩⟩

theorem integrable_sourceIndicator (ha : 1/20 ≤ a) :
    Integrable ((source a).indicator fouvryG9WeightedIntegrand) :=
  integrable_indicator_of_integrableOn measurableSet_source
    (integrableOn_fouvryG9WeightedIntegrand measurableSet_source
      (source_subset_ambient ha))

theorem low_eq_iteratedSetIntegral (hab : a ≤ 1/10) :
    low a =
      ∫ u in Ioc a (1 / 10),
        ∫ v in Ioc (1 / 3) ((1 - u) / 2), fouvryG9WeightedIntegrand (u, v) := by
  unfold low
  rw [intervalIntegral.integral_of_le hab]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro u hu
  change (∫ v in (1 / 3 : ℝ)..((1 - u) / 2), 1 / (u * v * (1 - u - v) * (1-u))) =
    ∫ v in Ioc (1 / 3) ((1 - u) / 2), fouvryG9WeightedIntegrand (u, v)
  rw [intervalIntegral.integral_of_le (by linarith [hu.2] : (1 / 3 : ℝ) ≤ (1 - u) / 2)]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro v _
  rfl

theorem sourceIndicator_integral_section (u : ℝ) :
    (∫ v, (source a).indicator fouvryG9WeightedIntegrand (u, v)) =
      (Ioc a (1 / 10)).indicator
        (fun u => ∫ v in Ioc (1 / 3) ((1 - u) / 2), fouvryG9WeightedIntegrand (u, v)) u := by
  by_cases hu : u ∈ Ioc a (1 / 10)
  · rw [indicator_of_mem hu, ← integral_indicator measurableSet_Ioc]
    apply integral_congr_ae
    filter_upwards with v
    have hmem : (u, v) ∈ (source a) ↔ v ∈ Ioc (1 / 3) ((1 - u) / 2) :=
      and_iff_right hu
    change (source a).indicator fouvryG9WeightedIntegrand (u, v) =
      (Ioc (1 / 3) ((1 - u) / 2)).indicator (fun v => fouvryG9WeightedIntegrand (u, v)) v
    by_cases hv : v ∈ Ioc (1 / 3) ((1 - u) / 2)
    · rw [indicator_of_mem (hmem.mpr hv), indicator_of_mem hv]
    · rw [indicator_of_notMem (fun h => hv (hmem.mp h)), indicator_of_notMem hv]
  · rw [indicator_of_notMem hu]
    apply integral_eq_zero_of_ae
    filter_upwards with v
    exact indicator_of_notMem (fun h => hu h.1) _

/-- Fubini is applied to an integrable indicator, not to an unspecified integral. -/
theorem low_eq_setIntegral (ha : 1/20 ≤ a) (hab : a ≤ 1/10) :
    low a = ∫ x in (source a), fouvryG9WeightedIntegrand x := by
  rw [low_eq_iteratedSetIntegral hab]
  let F := (source a).indicator fouvryG9WeightedIntegrand
  have hF : Integrable F := integrable_sourceIndicator ha
  have hFubini : (∫ z, F z) = ∫ u, ∫ v, F (u, v) := by
    rw [Measure.volume_eq_prod ℝ ℝ] at hF ⊢
    exact integral_prod F hF
  calc
    _ = ∫ u, (Ioc a (1 / 10)).indicator
        (fun u => ∫ v in Ioc (1 / 3) ((1 - u) / 2), fouvryG9WeightedIntegrand (u, v)) u := by
      rw [integral_indicator measurableSet_Ioc]
    _ = ∫ u, ∫ v, F (u, v) := by
      apply integral_congr_ae
      filter_upwards with u
      exact (sourceIndicator_integral_section u).symm
    _ = ∫ z, F z := hFubini.symm
    _ = _ := integral_indicator measurableSet_source

theorem integrable_upperIntegrand (n : ℕ) (hn : 0 < n) (h : ℝ) :
    Integrable (upperIntegrand a n h) := by
  classical
  exact integrable_finsetSum _ fun q _ =>
    (integrable_indicator_of_integrableOn (measurableSet_goldbachB9LogGridCell n q)
      (integrableOn_goldbachB9LogDensity (measurableSet_goldbachB9LogGridCell n q)
        (goldbachB9LogGridCell_subset_ambientBox hn q))).const_mul _

/-- The selected-cell sum retains its actual logarithmic rectangle masses. -/
theorem upperSum_eq_integral (n : ℕ) (hn : 0 < n) (h : ℝ) :
    upperSum a n h 0 = ∫ x, upperIntegrand a n h x := by
  classical
  unfold upperSum upperIntegrand
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



end OriginalU8.Weighted
