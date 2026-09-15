import SigmaRationalOuterActual

noncomputable section
namespace SigmaRationalOuterFTC
open Real

/-- A real expression for the real part of a complex simple-pole primitive.
The nonreal branch uses only the exact real and imaginary parts of its forced root.
No approximate roots or transcendental evaluations occur. -/
def rootPrimitive (a b u v t : ℝ) : ℝ :=
  if b=0 then u*log (t-a)
  else (u/2)*log ((t-a)^2+b^2)-v*arctan ((t-a)/b)

def rootKernel (a b u v t : ℝ) : ℝ :=
  (u*(t-a)-v*b)/((t-a)^2+b^2)

/-- This includes the negative-real side via Real.log, so no hidden logarithm cut is used. -/
theorem rootPrimitive_deriv (a b u v t : ℝ) (hn : (t-a)^2+b^2≠0) :
    HasDerivAt (rootPrimitive a b u v) (rootKernel a b u v t) t := by
  by_cases hb : b=0
  · subst b
    have hta : t-a≠0 := by
      intro h
      apply hn
      simp [h]
    have hh := (((hasDerivAt_id t).sub_const a).log hta).const_mul u
    convert hh using 1 <;> first | rfl | skip
    · funext x
      simp [rootPrimitive]
    · dsimp [rootKernel]
      field_simp
      ring
  · have hq : 0<(t-a)^2+b^2 := by positivity
    have hid := (hasDerivAt_id t).sub_const a
    have hlog := (((hid.pow 2).add_const (b^2)).log hq.ne').const_mul (u/2)
    have hatan := ((hid.div_const b).arctan).const_mul v
    have hd := hlog.sub hatan
    convert hd using 1 <;> first | rfl | skip
    · funext x
      simp [rootPrimitive,hb]
    · dsimp [rootKernel]
      have hden : 1+((t-a)/b)^2≠0 := by positivity
      field_simp [hb,hn,hden]
      ring

/-- Each rational part emitted by Hermite reduction is differentiated without removing powers. -/
theorem hermiteTerm_deriv {A B : ℝ → ℝ} {a b t : ℝ} (hA : HasDerivAt A a t)
    (hB : HasDerivAt B b t) (hn : B t≠0) (m : ℕ) :
    HasDerivAt (fun x => A x/(B x)^m)
      ((a*(B t)^m-A t*((m:ℝ)*(B t)^(m-1)*b))/((B t)^m)^2) t := by
  exact hA.div (hB.pow m) (pow_ne_zero m hn)

end SigmaRationalOuterFTC
