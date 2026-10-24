import WR2ClassicalSixthReduction
import WRMapMSixthClassical

noncomputable section
namespace WuPaper.ClassicalSixthLog
open Real Set MeasureTheory QuarterTrim DirectFiniteF6 Wu08G6High
open Wu08G6TableGeometryRecovery Wu2008DoubleSieve WuSource.SrcSixthGain
open ClassicalLowerLog
open scoped Classical

private theorem endpoint_le_five : endpoint ≤ (5:ℝ) := by
  norm_num [endpoint,alpha,beta]

theorem log_integrable (S : Set (ℝ × ℝ)) (hm : MeasurableSet S)
    (hs : S ⊆ envelope) : Integrable (rawMasked S ClassicalLowerLog.profile) := by
  apply raw_integrable profile_continuous.measurable hm hs (K := 3) (by norm_num)
  intro v hv
  have hb := profile_bounds ((envelope_parameter hv).2.trans endpoint_le_five)
  rw [abs_of_nonneg hb.1]
  exact hb.2

theorem log_density_integral :
    ClassicalSixthReduction.published ClassicalLowerLog.profile =
      8*∫ s in (2:ℝ)..endpoint, density s * log (s-1) := by
  rw [ClassicalSixthReduction.published_density_integral _
    (log_integrable _ published_measurable
      (fun _ hv => (union_subset rectangleA_subset rectangleB_subset) (published_subset hv)))]
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le (by norm_num [endpoint,alpha,beta] : (2:ℝ) ≤ endpoint)] at hs
  dsimp only
  rw [profile_literal hs.1]

def clipped (s : ℝ) : ℝ := wuLowerCoefficient (truncatedSixthMassClip s)

theorem clipped_eq {s : ℝ} (hs : s ≤ 5) : clipped s = wuLowerCoefficient s := by
  by_cases h2 : s ≤ 2
  · exact (truncatedSixthZeroDelta_clip_zero h2).trans
      (truncatedSixthZeroDelta_coefficient_zero h2).symm
  · rw [clipped,truncatedSixthMass_clip_eq ⟨(lt_of_not_ge h2).le,hs⟩]

theorem lower_bounds {s : ℝ} (hs : s ≤ 5) :
    0 ≤ wuLowerCoefficient s ∧ wuLowerCoefficient s ≤ 7 := by
  have hp := profile_bounds hs
  have hn := hp.1.trans (profile_le_lower (hs.trans (by norm_num)))
  refine ⟨hn,?_⟩
  by_cases h2 : s ≤ 2
  · rw [truncatedSixthZeroDelta_coefficient_zero h2]
    norm_num
  · have hs2 : 2 ≤ s := (lt_of_not_ge h2).le
    by_cases h4 : s ≤ 4
    · rw [WuTarget.Wu08FifthSource.coefficient_initial hs2 h4]
      rw [profile_literal hs2] at hp
      linarith only [hp.2]
    · rw [Wu08OriginalFirstSteps.lower_middle (by linarith) (by linarith)]
      have hc := (ClassicalCWeighted.C_bounds (by linarith) (show s ≤ 6 by linarith)).2
      rw [profile_literal hs2] at hp
      linarith only [hp.2,hc]

theorem clipped_integrable (S : Set (ℝ × ℝ)) (hm : MeasurableSet S)
    (hs : S ⊆ envelope) : Integrable (rawMasked S clipped) := by
  apply raw_integrable truncatedSixthMass_clipped_classical_continuous.measurable hm hs
    (K := 7) (by norm_num)
  intro v hv
  change |clipped (u v.1 v.2)| ≤ 7
  rw [clipped_eq ((envelope_parameter hv).2.trans endpoint_le_five)]
  have hb := lower_bounds ((envelope_parameter hv).2.trans endpoint_le_five)
  rw [abs_of_nonneg hb.1]
  exact hb.2

end WuPaper.ClassicalSixthLog
#print axioms WuPaper.ClassicalSixthLog.log_density_integral
#print axioms WuPaper.ClassicalSixthLog.clipped_integrable
