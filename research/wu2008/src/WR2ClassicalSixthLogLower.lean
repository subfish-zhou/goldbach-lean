import WR2ClassicalSixthLog

noncomputable section
namespace WuPaper.ClassicalSixthLog
open Real Set MeasureTheory QuarterTrim DirectFiniteF6 Wu08G6High
open Wu08G6TableGeometryRecovery Wu2008DoubleSieve WuSource.SrcSixthGain
open ClassicalLowerLog
open scoped Classical

private theorem env_five {v : ℝ × ℝ} (hv : v ∈ envelope) : u v.1 v.2 ≤ 5 :=
  (envelope_parameter hv).2.trans (by norm_num [endpoint,alpha,beta])

private theorem clipped_bound (v : ℝ × ℝ) (hv : v ∈ envelope) :
    |clipped (u v.1 v.2)| ≤ 7 := by
  rw [clipped_eq (env_five hv),abs_of_nonneg (lower_bounds (env_five hv)).1]
  exact (lower_bounds (env_five hv)).2

theorem clipped_rectangle :
    4*(∫ v : ℝ × ℝ, rawMasked envelope clipped v) = Wu08TerminalAlignment.sixthMain := by
  have he := rectangle_integral truncatedSixthMass_clipped_classical_continuous.measurable
    (by norm_num : (0:ℝ) ≤ 7) clipped_bound envelope_bounds.1
    (by norm_num [alpha,beta] : beta ≤ 1/2-3*alpha) (Subset.rfl : envelope ⊆ envelope)
  change (∫ v : ℝ × ℝ, rawMasked envelope clipped v) =
    (∫ x in alpha..beta, ∫ y in beta..(1/2-3*alpha), kernel clipped x y) at he
  rw [he]
  rw [← RMapMSixth.c6_eq_existing_classical,RMapMSixth.c6_rectangle_transport]
  congr 1
  apply intervalIntegral.integral_congr
  intro x hx
  rw [uIcc_of_le envelope_bounds.1] at hx
  apply intervalIntegral.integral_congr
  intro y hy
  rw [uIcc_of_le (by norm_num [alpha,beta] : beta ≤ 1/2-3*alpha)] at hy
  unfold kernel
  rw [clipped_eq (env_five (v := (x,y)) ⟨hx,hy⟩)]

theorem log_lower :
    8*∫ s in (2:ℝ)..endpoint, density s * log (s-1) ≤ Wu08TerminalAlignment.sixthMain := by
  have hsub : publishedReducedDomain ⊆ envelope :=
    fun _ hv => (union_subset rectangleA_subset rectangleB_subset) (published_subset hv)
  have hp (v : ℝ × ℝ) : rawMasked publishedReducedDomain ClassicalLowerLog.profile v ≤
      rawMasked envelope clipped v := by
    simp only [rawMasked]
    by_cases hv : v ∈ envelope
    · have hd := (envelope_bounds.2.2.2.2.2.trans_le (envelope_denominator hv)).le
      rw [if_pos hv]
      by_cases hs : v ∈ publishedReducedDomain
      · rw [if_pos hs]
        unfold kernel
        rw [clipped_eq (env_five hv)]
        exact div_le_div_of_nonneg_right (profile_le_lower ((env_five hv).trans (by norm_num))) hd
      · rw [if_neg hs]
        unfold kernel
        rw [clipped_eq (env_five hv)]
        exact div_nonneg (lower_bounds (env_five hv)).1 hd
    · have hs : v ∉ publishedReducedDomain := fun hs => hv (hsub hs)
      simp [hv,hs]
  have h := integral_mono (log_integrable _ published_measurable hsub)
    (clipped_integrable _ (measurableSet_Icc.prod measurableSet_Icc) Subset.rfl) hp
  rw [← log_density_integral,← clipped_rectangle]
  exact mul_le_mul_of_nonneg_left h (by norm_num)

end WuPaper.ClassicalSixthLog
#print axioms WuPaper.ClassicalSixthLog.log_lower
