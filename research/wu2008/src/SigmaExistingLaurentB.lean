import SigmaExistingEndpoints
namespace SigmaExistingLogError
open Real OriginalSigmaStrength OriginalSigmaCubicRestoration
open Wu2008DoubleSieve SharpLogRecurrence JointLogTotalComparison
noncomputable section
def bWeight (t : ℝ) : ℝ := bCoeff t*enhanced ((t+1)/2)/t

theorem bWeight_laurent {t : ℝ} (ht : 0<t) :
    bWeight t=
      (4/21)+
      (2/441)*t^1+
      poleDensity (0) (-262/3969) (0) (0) t+
      poleDensity (3) (-2816/3969) (1408/1323) (-512/441) t := by
  have h0 : t≠0 := ht.ne'
  have h1 : t+(1)≠0 := by positivity
  have h2 : t+(2)≠0 := by positivity
  have h3 : t+(3)≠0 := by positivity
  have h4 : t+(5)≠0 := by positivity
  have h5 : t+(5/3)≠0 := by positivity
  have h6 : 2*t+2≠0 := by positivity
  have h7 : 3*t+5≠0 := by positivity
  unfold bWeight bCoeff enhanced ub lowerLog upperLog poleDensity
  field_simp
  ring

end
end SigmaExistingLogError
