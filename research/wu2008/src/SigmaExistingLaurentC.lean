import SigmaExistingEndpoints
namespace SigmaExistingLogError
open Real OriginalSigmaStrength OriginalSigmaCubicRestoration
open Wu2008DoubleSieve SharpLogRecurrence JointLogTotalComparison
noncomputable section
def cWeight (t : ℝ) : ℝ := cCoeff t*V ((2*t+2)/(t+3))/t

theorem cWeight_laurent {t : ℝ} (ht : 0<t) :
    cWeight t=
      poleDensity (0) (-68564/70875) (2180434/2953125) (-26318/196875) t+
      (12164/13125)/(t+(0))^4+
      poleDensity (3) (-928/2835) (0) (0) t+
      poleDensity (5/3) (-286208/212625) (2584576/11390625) (-1212416/6834375) t := by
  have h0 : t≠0 := ht.ne'
  have h1 : t+(1)≠0 := by positivity
  have h2 : t+(2)≠0 := by positivity
  have h3 : t+(3)≠0 := by positivity
  have h4 : t+(5)≠0 := by positivity
  have h5 : t+(5/3)≠0 := by positivity
  have h6 : 2*t+2≠0 := by positivity
  have h7 : 3*t+5≠0 := by positivity
  unfold cWeight cCoeff cb ca uc V lowerLog upperLog poleDensity
  field_simp
  ring

end
end SigmaExistingLogError
