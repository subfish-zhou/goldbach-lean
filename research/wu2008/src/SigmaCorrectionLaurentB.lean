import SigmaCorrectionBase
namespace SigmaCorrectionFTC
open Real OriginalSigmaStrength OriginalSigmaCubicRestoration
open SigmaExistingLogError SigmaSignedCells Wu2008DoubleSieve SharpLogRecurrence
noncomputable section

def termB (t : ℝ) : ℝ := SigmaInnerPaid.bCoeff t*SigmaSignedCells.lowerRemainder ((t+1)/2)/t

def partialB (t : ℝ) : ℝ :=
  (-2/21)+
  poleFour (0) (-19/3750705) (0) (0) (0) t+
  poleFour (3) (80656/76545) (-7136/3645) (3968/1701) (1024/2835) t+
  ((5288000/3969)*t+(2216000/1323))/qB t^2+
  ((109640/27783)*t+(-2291440/27783))/qB t

theorem termB_partial {t : ℝ} (ht : 0<t) : termB t=partialB t := by
  have h0 : t≠0 := ht.ne'
  have h1 : t+1≠0 := by positivity
  have h2 : t+2≠0 := by positivity
  have h3 : t+3≠0 := by positivity
  have h5 : t+5≠0 := by positivity
  have h53 : t+5/3≠0 := by positivity
  have h6 : 2*t+2≠0 := by positivity
  have h7 : 3*t+5≠0 := by positivity
  have hq : t^2+18*t+21≠0 := by positivity
  have hr : t^2+28*t+61≠0 := by positivity
  unfold termB
  rw [lowerRemainder_rational (by positivity)]
  unfold partialB poleFour poleDensity SigmaInnerPaid.bCoeff ub qB
  rw [SigmaInnerProfile.beta_rational ht]
  field_simp
  ring

end
end SigmaCorrectionFTC
