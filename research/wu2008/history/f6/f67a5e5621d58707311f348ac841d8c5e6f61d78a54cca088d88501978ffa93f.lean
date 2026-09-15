import SrcSixthGainRoot
import SrcSixthGainAnalyticConsumer

noncomputable section
namespace WuSource.SrcSixthGain.Analytic
open Real Wu2008DoubleSieve HighBoxRecovery
open scoped Classical

theorem high_source_cutoff_h_count {delta eps : ℝ}
    (hd : 0 < delta) (hdhi : delta ≤ 50*highEta) (heps : 0 < eps) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N → ∀ Delta x y : ℝ,
      1+log (N : ℝ)^(-4 : ℝ) ≤ Delta →
      Delta < 1+2*log (N : ℝ)^(-4 : ℝ) →
      truncatedSixthLowerRegion delta x y → 1/4 < y →
      (N : ℝ)^truncatedSixthLowerAlpha ≤ (N : ℝ)^x/Delta →
      (N : ℝ)^truncatedSixthLowerAlpha ≤ (N : ℝ)^y/Delta →
      (wuLowerCoefficient (truncatedSixthLowerS delta x y) +
        wuImprovementLimit false delta (truncatedSixthLowerS delta x y) -
        hRemainder delta (truncatedSixthLowerS delta x y) - eps) *
        boxTheta N ((N : ℝ)^(1/2-delta))
          (convolutionWuWindows N Delta ![(N : ℝ)^x,(N : ℝ)^y]) ≤
      ∑ b ∈ truncatedSixthLowerBoxPairs N Delta x y,
        (sieveCount N (b.1*b.2) N ((N : ℝ)^truncatedSixthLowerAlpha) : ℝ) := by
  obtain ⟨T,hT,hc⟩ := high_original_h_actual_box hd hdhi heps
  refine ⟨T,hT,?_⟩
  intro N hN he Delta x y hlo hhi hr hy hp hq
  have hs := high_triangle_source_parameter hd.le hr hy
  have hquot : 0 ≤ delta/QuarterTrim.alpha := div_nonneg hd.le QuarterTrim.alpha_pos.le
  exact hc N hN he Delta x y hlo hhi hr hy hp hq _ hs.1
    (by linarith [hs.2]) le_rfl

#check @source_box_iff_exact_boundary
#check @source_depth_cannot_remove_boundary
#check @high_triangle_source_parameter
#check @moving_boundary_partition
#check @boundary_strip_width
#check @high_density_integral
#check @first_three_high_weights
#check @fourth_high_weight
#check @later_high_weights_zero
#check @high_loss_four
#check @legal_weight_exact
#check @legalGain_original_weights
#check @legalGain_source_lower
#check @legal_sixth_lower
#check @legal_classical_sixth
#check @legal_ordinary_count
#check @retained_h_exact
#check @retained_h_nonneg
#check @remainder_zero_iff
#check @high_original_h_closed
#check @high_original_h_actual_box
#check @high_source_cutoff_h_count
#check @mixed_original_h_with_remainder
#check @exact_buchstab_h_gap

#print axioms source_box_iff_exact_boundary
#print axioms source_depth_cannot_remove_boundary
#print axioms high_triangle_source_parameter
#print axioms moving_boundary_partition
#print axioms boundary_strip_width
#print axioms high_density_integral
#print axioms first_three_high_weights
#print axioms fourth_high_weight
#print axioms later_high_weights_zero
#print axioms high_loss_four
#print axioms legal_weight_exact
#print axioms legal_weight_nonneg
#print axioms high_weight_nonneg
#print axioms high_weight_le_full
#print axioms legalGain_original_weights
#print axioms conservative_le_legalGain
#print axioms legalGain_source_lower
#print axioms legal_sixth_lower
#print axioms legal_classical_sixth
#print axioms legal_ordinary_count
#print axioms retained_h_exact
#print axioms retained_h_nonneg
#print axioms remainder_zero_iff
#print axioms high_original_h_closed
#print axioms high_original_h_actual_box
#print axioms high_source_cutoff_h_count
#print axioms mixed_original_h_with_remainder
#print axioms exact_buchstab_h_gap
end WuSource.SrcSixthGain.Analytic

open Lean Elab Command
run_cmd do
  let env ← getEnv
  for (name, info) in env.constants.toList do
    if name.toString.startsWith "WuSource.SrcSixthGain.Analytic." &&
        (name.toString.splitOn "._").length == 1 then
      logInfo m!"DECLARATION {name} : {info.type}"
