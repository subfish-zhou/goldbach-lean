import SigmaInnerEndpointPaid
namespace SigmaInnerPaid
open Real OriginalSigmaStrength OriginalSigmaCubicRestoration
open Wu2008DoubleSieve SharpLogRecurrence JointLogTotalComparison SigmaExistingLogError
noncomputable section

def cWeight (t : ℝ) : ℝ := cCoeff t*V ((2*t+2)/(t+3))/t

theorem cWeight_laurent {t : ℝ} (ht : 0<t) : cWeight t =
    (0) +
    poleDensity (0) (-1118385788/1012921875) (140935786/144703125) (-142502/459375) t +
    (12164/13125)/(t+(0))^4 +
    poleDensity (3) (-32/135) (0) (0) t +
    poleDensity (5/3) (-73544192/186046875) (22433792/79734375) (-557056/6834375) t +
    ((-42368/21609)*t+(-687616/64827))/(t^2+18*t+21) := by
  have h0 : t≠0 := ht.ne'
  have h1 : t+1≠0 := by positivity
  have h2 : t+2≠0 := by positivity
  have h3 : t+3≠0 := by positivity
  have h5 : t+5≠0 := by positivity
  have h53 : t+5/3≠0 := by positivity
  have h6 : 2*t+2≠0 := by positivity
  have h7 : 3*t+5≠0 := by positivity
  have hq : t^2+18*t+21≠0 := by positivity
  unfold cWeight cCoeff cb ca uc V lowerLog upperLog poleDensity
  rw [SigmaInnerProfile.beta_rational ht]
  field_simp
  ring

end
end SigmaInnerPaid
