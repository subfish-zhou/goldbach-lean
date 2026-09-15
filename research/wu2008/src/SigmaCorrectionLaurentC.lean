import SigmaCorrectionBase
namespace SigmaCorrectionFTC
open Real OriginalSigmaStrength OriginalSigmaCubicRestoration
open SigmaExistingLogError SigmaSignedCells Wu2008DoubleSieve SharpLogRecurrence
noncomputable section

def termC (t : ℝ) : ℝ := -SigmaInnerPaid.cCoeff t*F1FullRecoveryPayment.upperGapPayment ((2*t+2)/(t+3))/t

def partialC (t : ℝ) : ℝ :=
  (0)+
  poleFour (0) (9647194/11817421875) (-15833/67528125) (2189/48234375) (-2/459375) t+
  poleFour (1) (-4/35) (0) (0) (0) t+
  poleFour (3) (32/945) (0) (0) (0) t+
  poleFour (5/3) (-19101750784/45581484375) (-113291264/1302328125) (-46825472/558140625) (4456448/143521875) t+
  ((226400/453789)*t+(1263200/151263))/qB t

theorem termC_partial {t : ℝ} (ht : 0<t) : termC t=partialC t := by
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
  unfold termC
  unfold partialC poleFour poleDensity SigmaInnerPaid.cCoeff cb ca uc F1FullRecoveryPayment.upperGapPayment qB
  rw [SigmaInnerProfile.beta_rational ht]
  field_simp
  ring

end
end SigmaCorrectionFTC
