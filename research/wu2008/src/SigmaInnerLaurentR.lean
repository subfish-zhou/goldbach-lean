import SigmaInnerEndpointPaid
namespace SigmaInnerPaid
open Real OriginalSigmaStrength OriginalSigmaCubicRestoration
open Wu2008DoubleSieve SharpLogRecurrence JointLogTotalComparison SigmaExistingLogError
noncomputable section

def rWeight (t : ℝ) : ℝ := rationalPart t/t

theorem rWeight_laurent {t : ℝ} (ht : 0<t) : rWeight t =
    (0) +
    poleDensity (0) (-76/1029) (-34/147) (8/21) t +
    ((-610/1029)*t+(-2510/1029))/(t^2+18*t+21) := by
  have h0 : t≠0 := ht.ne'
  have h1 : t+1≠0 := by positivity
  have h2 : t+2≠0 := by positivity
  have h3 : t+3≠0 := by positivity
  have h5 : t+5≠0 := by positivity
  have h53 : t+5/3≠0 := by positivity
  have h6 : 2*t+2≠0 := by positivity
  have h7 : 3*t+5≠0 := by positivity
  have hq : t^2+18*t+21≠0 := by positivity
  unfold rWeight rationalPart cc cd poleDensity
  rw [SigmaInnerProfile.beta_rational ht]
  field_simp
  ring

end
end SigmaInnerPaid
