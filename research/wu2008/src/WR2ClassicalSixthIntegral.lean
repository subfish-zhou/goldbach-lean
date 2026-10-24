import WR2ClassicalSixthKernel

noncomputable section
namespace WuPaper.ClassicalSixthIntegral
open Real Set MeasureTheory
open QuarterTrim (alpha beta alpha_pos)
open WuSource.SrcSixthGain
open ClassicalSixthBranch
open ClassicalSixthKernel

private theorem literal_parameters (s : ℝ) :
    (1-2*alpha-2*alpha*s = 2*alpha*u s) ∧
    (1-2*beta-2*alpha*s = 2*alpha*v s) ∧ beta = alpha*r := by
  norm_num [alpha,beta,u,v,ClassicalSixthBranch.R,r]
  constructor <;> ring

private theorem weight_denominator {s : ℝ} (he : s ≤ endpoint) :
    ClassicalSixthWeight.R-s ≠ 0 := by
  norm_num [ClassicalSixthWeight.R,endpoint,alpha,beta] at he ⊢
  linarith

theorem lower_literal {s : ℝ} (hs : 2 ≤ s) (he : s ≤ split) :
    kernel lower s = density s*log (s-1) := by
  have hep : s ≤ endpoint := he.trans (by norm_num [split,endpoint,alpha,beta])
  have hv : v s ≠ 0 := by linarith [(geometry hep).2]
  have hp := literal_parameters s
  rw [density_lower he]
  unfold lowerKernel kernel ClassicalSixthKernel.inner logFactor lower
  rw [ClassicalSixthWeight.weight_literal (by linarith) (weight_denominator hep),hp.1,hp.2.1,hp.2.2]
  have ha : alpha ≠ 0 := alpha_pos.ne'
  have hq : alpha*r*(2*alpha*u s)/(alpha*(2*alpha*v s)) = r*u s/v s := by
    field_simp [ha,hv]
  rw [hq]
  ring

theorem upper_literal {s : ℝ} (hs : split ≤ s) (he : s ≤ endpoint) :
    kernel upper s = density s*log (s-1) := by
  have hs2 : 2 ≤ s := (by norm_num [split,alpha,beta] : (2:ℝ) ≤ split).trans hs
  have hr : r ≠ 0 := by norm_num [r]
  have hp := literal_parameters s
  rw [density_upper hs]
  unfold upperKernel kernel ClassicalSixthKernel.inner logFactor upper
  rw [ClassicalSixthWeight.weight_literal (by linarith) (weight_denominator he),hp.1,hp.2.1,hp.2.2]
  have ha : alpha ≠ 0 := alpha_pos.ne'
  have hq : (2*alpha*u s)*(2*alpha*v s)/(4*alpha*(alpha*r)) = u s*v s/r := by
    field_simp [ha,hr]
    ring
  rw [hq]
  ring

theorem source_integrable {a b : ℝ} (ha : 2 ≤ a) (hb : b ≤ endpoint) (hab : a ≤ b) :
    IntervalIntegrable (fun s => density s*log (s-1)) volume a b := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hab]
  apply (density_continuous.mono (fun s hs => ⟨ha.trans hs.1,hs.2.trans hb⟩)).mul
  exact fun s hs => (log_deriv (ha.trans hs.1)).continuousAt.continuousWithinAt

theorem sixth_lower :
    8*((∫ s in (2:ℝ)..split, kernel lower s)+
      (∫ s in split..endpoint, kernel upper s)) ≤ Wu08TerminalAlignment.sixthMain := by
  have h2 : (2:ℝ) ≤ split := by norm_num [split,alpha,beta]
  have he : split ≤ endpoint := by norm_num [split,endpoint,alpha,beta]
  have hi1 := source_integrable le_rfl he h2
  have hi2 := source_integrable h2 le_rfl he
  have hlo : (∫ s in (2:ℝ)..split, kernel lower s) =
      ∫ s in (2:ℝ)..split, density s*log (s-1) := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le h2] at hs
    exact lower_literal hs.1 hs.2
  have hhi : (∫ s in split..endpoint, kernel upper s) =
      ∫ s in split..endpoint, density s*log (s-1) := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le he] at hs
    exact upper_literal hs.1 hs.2
  rw [hlo,hhi,intervalIntegral.integral_add_adjacent_intervals hi1 hi2]
  exact ClassicalSixthLog.log_lower

end WuPaper.ClassicalSixthIntegral
#print axioms WuPaper.ClassicalSixthIntegral.sixth_lower
