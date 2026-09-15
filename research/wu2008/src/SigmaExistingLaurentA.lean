import SigmaExistingEndpoints
namespace SigmaExistingLogError
open Real OriginalSigmaStrength OriginalSigmaCubicRestoration
open Wu2008DoubleSieve SharpLogRecurrence JointLogTotalComparison
noncomputable section
def aWeight (t : ℝ) : ℝ := aCoeff t*enhanced ((t+2)/3)/t

theorem aWeight_laurent {t : ℝ} (ht : 0<t) :
    aWeight t=
      (-172/1323)+
      (-4/1323)*t^1+
      poleDensity (0) (5666224/4134375) (-2395424/4134375) (-68176/275625) t+
      (-51088/55125)/(t+(0))^4+
      poleDensity (1) (277/2646) (0) (0) t+
      poleDensity (5) (1129701/306250) (-1270998/153125) (525528/30625) t := by
  have h0 : t≠0 := ht.ne'
  have h1 : t+(1)≠0 := by positivity
  have h2 : t+(2)≠0 := by positivity
  have h3 : t+(3)≠0 := by positivity
  have h4 : t+(5)≠0 := by positivity
  have h5 : t+(5/3)≠0 := by positivity
  have h6 : 2*t+2≠0 := by positivity
  have h7 : 3*t+5≠0 := by positivity
  unfold aWeight aCoeff enhanced ca ua lowerLog upperLog poleDensity
  field_simp
  ring

end
end SigmaExistingLogError
