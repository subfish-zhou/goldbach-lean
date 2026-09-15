import SigmaCorrectionBase
namespace SigmaCorrectionFTC
open Real OriginalSigmaStrength OriginalSigmaCubicRestoration
open SigmaExistingLogError SigmaSignedCells Wu2008DoubleSieve SharpLogRecurrence
noncomputable section

def termA (t : ℝ) : ℝ := SigmaInnerPaid.aCoeff t*SigmaSignedCells.lowerRemainder ((t+2)/3)/t

def partialA (t : ℝ) : ℝ :=
  (-4/189)+
  poleFour (0) (237900238098139/1963465731734062500) (-127848017567/1379484120656250) (27209719/538440328125) (-986/84065625) t+
  poleFour (2) (-3/20) (0) (0) (0) t+
  poleFour (5) (-71076470774/24020390625) (1341054884/145578125) (-275166648/13234375) (-1134432/240625) t+
  ((-7903489340/2035338627)*t+(6526017140/2035338627))/qA t+
  ((49020605720/6643924749)*t+(184438191640/19931774247))/qB t

theorem termA_partial {t : ℝ} (ht : 0<t) : termA t=partialA t := by
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
  unfold termA
  rw [lowerRemainder_rational (by positivity)]
  unfold partialA poleFour poleDensity SigmaInnerPaid.aCoeff ca ua qA qB
  rw [SigmaInnerProfile.beta_rational ht]
  field_simp
  ring

end
end SigmaCorrectionFTC
