import SigmaExistingEndpoints
namespace SigmaExistingLogError
open Real OriginalSigmaStrength OriginalSigmaCubicRestoration
open Wu2008DoubleSieve SharpLogRecurrence JointLogTotalComparison
noncomputable section
def rWeight (t : ℝ) : ℝ := rationalPart t/t

theorem rWeight_laurent {t : ℝ} (ht : 0<t) :
    rWeight t=
      poleDensity (0) (-4/21) (-10/63) (8/21) t+
      poleDensity (1) (-4/21) (0) (0) t+
      poleDensity (3) (0) (64/63) (0) t := by
  have h0 : t≠0 := ht.ne'
  have h1 : t+(1)≠0 := by positivity
  have h2 : t+(2)≠0 := by positivity
  have h3 : t+(3)≠0 := by positivity
  have h4 : t+(5)≠0 := by positivity
  have h5 : t+(5/3)≠0 := by positivity
  have h6 : 2*t+2≠0 := by positivity
  have h7 : 3*t+5≠0 := by positivity
  unfold rWeight rationalPart cc cd poleDensity
  field_simp
  ring

end
end SigmaExistingLogError
