import WR2SevenPublicationCount
import MathlibNt.Wu2008DoubleSieve.SharpLogRecurrence

noncomputable section
namespace WuPaper.R2Seven
open Wu2008DoubleSieve WuSource.SrcSingle Finset
open scoped Classical

def logArgument (j : Fin 7) : ℝ :=
  let a := if j.val = 0 then 1/(6*truncatedSixthLowerAlpha) else sourceNode (2+j.val)
  psiNode j*(1-2*truncatedSixthLowerAlpha*a)/(a*(1-2*truncatedSixthLowerAlpha*psiNode j))

theorem logArgument_ge_one (j : Fin 7) : 1 ≤ logArgument j := by
  fin_cases j <;> norm_num [logArgument, psiNode, sourceNode, truncatedSixthLowerAlpha]

def rationalGain : ℝ :=
  8*∑ j : Fin 7, SharpLogRecurrence.lowerLog (logArgument j)*psiPublication j

theorem rationalGain_le_paid : rationalGain ≤ psiSevenPaid := by
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 8)
  apply sum_le_sum
  intro j _
  apply mul_le_mul_of_nonneg_right _ (seven_publication_positive j).le
  exact SharpLogRecurrence.log_lower (logArgument_ge_one j)

def termLower : Fin 7 → ℝ := ![72378683/10000000000,73271890/10000000000,60969820/10000000000,47930254/10000000000,32970915/10000000000,17573147/10000000000,5199815/10000000000]

theorem termLower_paid (j : Fin 7) :
    termLower j ≤ 8*SharpLogRecurrence.lowerLog (logArgument j)*psiPublication j := by
  fin_cases j <;> norm_num [termLower, SharpLogRecurrence.lowerLog,
    logArgument, psiNode, sourceNode, truncatedSixthLowerAlpha, psiPublication,
    Fin.addCases, Fin.ext_iff, Wu04RemainingCore.publication, Wu04FirstCore.publication]

theorem rationalGain_lower : (31029/1000000 : ℝ) ≤ rationalGain := by
  have hs := sum_le_sum (fun j (_ : j ∈ univ) => termLower_paid j)
  have he : (∑ j : Fin 7, termLower j) ≥ (31029/1000000 : ℝ) := by
    norm_num [termLower, Fin.sum_univ_succ]
  unfold rationalGain
  simp only [mul_assoc, ← mul_sum] at hs
  exact he.trans hs

theorem seven_gain_lower : (31029/1000000 : ℝ) ≤ psiSevenPaid :=
  rationalGain_lower.trans rationalGain_le_paid

end WuPaper.R2Seven
#print axioms WuPaper.R2Seven.seven_gain_lower
