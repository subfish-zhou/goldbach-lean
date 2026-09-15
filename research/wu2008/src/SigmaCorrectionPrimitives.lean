import SigmaCorrectionBase
namespace SigmaCorrectionFTC
open Real Set MeasureTheory OriginalSigmaStrength
noncomputable section

/-- Primitive of every retained linear principal part, including order four. -/
def poleFourPrimitive (p a b c d t : ℝ) : ℝ :=
  polePrimitive p a b c t-d/(3*(t+p)^3)

theorem poleFourPrimitive_deriv (p a b c d : ℝ) {t : ℝ} (ht : t+p≠0) :
    HasDerivAt (poleFourPrimitive p a b c d) (poleFour p a b c d t) t := by
  have hp := polePrimitive_deriv p a b c ht
  have hf := ((((hasDerivAt_id t).add_const p).pow 3).inv (pow_ne_zero 3 ht)).const_mul (d/3)
  convert hp.sub hf using 1 <;> first | rfl | skip
  · funext x
    dsimp [poleFourPrimitive]
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  · dsimp [poleFour]
    field_simp
    ring

/-- The other original quadratic is an affine pullback of the existing sqrt15 primitive. -/
def quadraticAPrimitive (f g t : ℝ) : ℝ :=
  TerminalE.quadraticPrimitive f ((g-2*f)/3) ((t+2)/3)

theorem quadraticAPrimitive_deriv (f g : ℝ) {t : ℝ} (ht : 1≤t) :
    HasDerivAt (quadraticAPrimitive f g) ((f*t+g)/qA t) t := by
  have h := (TerminalE.quadraticPrimitive_deriv f ((g-2*f)/3)
    (by linarith : 1≤(t+2)/3)).comp t (((hasDerivAt_id t).add_const 2).div_const 3)
  convert h using 1 <;> first | rfl | skip
  dsimp [TerminalE.q,qA]
  field_simp
  ring

/-- Forced Hermite reduction of the genuine repeated beta/residual quadratic. -/
def repeatedPrimitive (f g t : ℝ) : ℝ :=
  ((9*f-g)/120*t+(9*(9*f-g)/120-f/2))/qB t+
  SigmaInnerPaid.quadraticPrimitive 0 ((9*f-g)/120) t

theorem repeatedPrimitive_deriv (f g : ℝ) {t : ℝ} (ht : 1≤t) :
    HasDerivAt (repeatedPrimitive f g) ((f*t+g)/(qB t)^2) t := by
  have hq : qB t≠0 := (qB_pos (by linarith)).ne'
  have hdq : HasDerivAt qB (2*t+18) t := by
    convert (((hasDerivAt_id t).pow 2).add ((hasDerivAt_id t).const_mul 18)).add_const 21 using 1 <;>
      first | rfl | (dsimp; ring)
  have hn := (((hasDerivAt_id t).const_mul ((9*f-g)/120)).add_const
    (9*(9*f-g)/120-f/2)).div hdq hq
  have hp := SigmaInnerPaid.quadraticPrimitive_deriv 0 ((9*f-g)/120) ht
  convert hn.add hp using 1 <;> first | rfl | skip
  dsimp [qB]
  field_simp
  ring

end
end SigmaCorrectionFTC
