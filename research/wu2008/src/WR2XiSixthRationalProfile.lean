import WR2XiSixthLogCell
import WR2XiSourceUpperRational

noncomputable section
namespace WuPaper.R2Xi.SixthContinuous
open Real Set MeasureTheory NodeExtension WuTarget.W01Continuous Finset
open SourceRational
open scoped Classical Interval

def rationalProfile (t : ℝ) : ℝ :=
  (Ioc 1 (rNode 2)).indicator (fun _ => upperLower 2) t+
    ∑ i ∈ Icc 3 29, (Ioc (rNode (i-1)) (rNode i)).indicator (fun _ => upperLower i) t

theorem rationalProfile_le (t : ℝ) : rationalProfile t ≤ upperProfile RationalCandidate.lowerH t := by
  unfold rationalProfile upperProfile
  apply add_le_add
  · by_cases ht : t ∈ Ioc 1 (rNode 2)
    · rw [indicator_of_mem ht,indicator_of_mem (Set.Ioc_subset_Icc_self ht)]
      exact le_rfl
    · rw [indicator_of_notMem ht]
      exact indicator_nonneg (fun _ _ => RationalCandidate.lowerH_nonneg 0) t
  · apply sum_le_sum
    intro i hi
    by_cases ht : t ∈ Ioc (rNode (i-1)) (rNode i)
    · rw [indicator_of_mem ht,indicator_of_mem ht]
      exact upperLower_le_extended (by have := (mem_Icc.mp hi).1; omega) (mem_Icc.mp hi).2
    · simp only [indicator_of_notMem ht,le_refl]

theorem rationalProfile_div_expansion (t : ℝ) : rationalProfile t/t =
    (Ioc 1 (rNode 2)).indicator (fun t => upperLower 2/t) t+
      ∑ i ∈ Icc 3 29, (Ioc (rNode (i-1)) (rNode i)).indicator (fun t => upperLower i/t) t := by
  simp only [rationalProfile,add_div,Finset.sum_div]
  congr 1
  · by_cases ht : t ∈ Ioc 1 (rNode 2) <;> simp [ht]
  · apply sum_congr rfl
    intro i _
    by_cases ht : t ∈ Ioc (rNode (i-1)) (rNode i) <;> simp [ht]

theorem reciprocal_indicator_integrable {a b q : ℝ} (ha : 0 < a) :
    Integrable ((Ioc a b).indicator (fun t : ℝ => q/t)) := by
  apply (integrable_indicator_iff measurableSet_Ioc).mpr
  apply IntegrableOn.mono_set _ Set.Ioc_subset_Icc_self
  apply ContinuousOn.integrableOn_Icc
  exact continuousOn_const.div continuousOn_id (fun t ht => (ha.trans_le ht.1).ne')

theorem rationalProfile_div_integrable : Integrable (fun t => rationalProfile t/t) := by
  simp_rw [rationalProfile_div_expansion]
  apply Integrable.add (reciprocal_indicator_integrable (by norm_num))
  apply integrable_finsetSum
  intro i _
  exact reciprocal_indicator_integrable (rNode_pos _)

def rationalH (s : ℝ) : ℝ := ∫ t in (s-1)..rNode 29, rationalProfile t/t

theorem rationalH_le {s : ℝ} (hs : 2 ≤ s) (hs4 : s ≤ 41/10) :
    rationalH s ≤ hContinuous RationalCandidate.lowerH s := by
  apply intervalIntegral.integral_mono_on (by norm_num [rNode]; linarith)
    rationalProfile_div_integrable.intervalIntegrable
    (upperProfile_div_integrable RationalCandidate.lowerH).intervalIntegrable
  intro t ht
  exact div_le_div_of_nonneg_right (rationalProfile_le t) (by linarith [ht.1])

end WuPaper.R2Xi.SixthContinuous
#print axioms WuPaper.R2Xi.SixthContinuous.rationalH_le
