import SigmaInnerEndpointPaid
namespace SigmaInnerPaid
open Real OriginalSigmaStrength OriginalSigmaCubicRestoration
open Wu2008DoubleSieve SharpLogRecurrence JointLogTotalComparison SigmaExistingLogError
noncomputable section

def bWeight (t : ℝ) : ℝ := bCoeff t*enhanced ((t+1)/2)/t

theorem bWeight_laurent {t : ℝ} (ht : 0<t) : bWeight t =
    (2/21) +
    poleDensity (0) (-262/3969) (0) (0) t +
    poleDensity (3) (-752/567) (352/189) (-128/63) t +
    ((1664/441)*t+(2176/441))/(t^2+18*t+21) := by
  have h0 : t≠0 := ht.ne'
  have h1 : t+1≠0 := by positivity
  have h2 : t+2≠0 := by positivity
  have h3 : t+3≠0 := by positivity
  have h5 : t+5≠0 := by positivity
  have h53 : t+5/3≠0 := by positivity
  have h6 : 2*t+2≠0 := by positivity
  have h7 : 3*t+5≠0 := by positivity
  have hq : t^2+18*t+21≠0 := by positivity
  unfold bWeight bCoeff enhanced ub lowerLog upperLog poleDensity
  rw [SigmaInnerProfile.beta_rational ht]
  field_simp
  ring

end
end SigmaInnerPaid
