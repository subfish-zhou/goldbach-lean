import SigmaInnerEndpointPaid
namespace SigmaInnerPaid
open Real OriginalSigmaStrength OriginalSigmaCubicRestoration
open Wu2008DoubleSieve SharpLogRecurrence JointLogTotalComparison SigmaExistingLogError
noncomputable section

def aWeight (t : ℝ) : ℝ := aCoeff t*enhanced ((t+2)/3)/t

theorem aWeight_laurent {t : ℝ} (ht : 0<t) : aWeight t =
    (4/189) +
    poleDensity (0) (78877744/56723625) (-451213408/607753125) (-409936/5788125) t +
    (-51088/55125)/(t+(0))^4 +
    poleDensity (5) (4752318/1164625) (-23702004/2646875) (850824/48125) t +
    ((-683930606/201331053)*t+(-7246584746/1811979477))/(t^2+18*t+21) := by
  have h0 : t≠0 := ht.ne'
  have h1 : t+1≠0 := by positivity
  have h2 : t+2≠0 := by positivity
  have h3 : t+3≠0 := by positivity
  have h5 : t+5≠0 := by positivity
  have h53 : t+5/3≠0 := by positivity
  have h6 : 2*t+2≠0 := by positivity
  have h7 : 3*t+5≠0 := by positivity
  have hq : t^2+18*t+21≠0 := by positivity
  unfold aWeight aCoeff enhanced ca ua lowerLog upperLog poleDensity
  rw [SigmaInnerProfile.beta_rational ht]
  field_simp
  ring

end
end SigmaInnerPaid
