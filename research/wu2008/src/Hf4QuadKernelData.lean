import SigmaRationalOuterData
import TerminalERadical

noncomputable section
namespace Hf4Quad
open TerminalE
def low (x : ℝ) : ℝ := (x-1)*((1/30)+x*((-37/210)+x*((169/42)+x*((327/14)+x*((2213/42)+x*((11093/210)+x*((1649/70)+x*(155/42))))))))/(x^2*(x+1)^4*(x^2+8*x+1))

def up (x : ℝ) : ℝ :=
  (21*x*(x-1)*(x^2+10*x+1)*(x+1)^3+168*x^2*(x-1)*(x+1)^3+
    56*x^2*(x-1)^3*(x+1)-3*(x-1)^7)/(210*x^2*(x+1)^4)


def sl (x : ℝ) : ℝ := low ((x+1)/2)+low (2*x/(x+1))
def su (x : ℝ) : ℝ := up ((x+1)/2)+up (2*x/(x+1))


def kernel (t : ℝ) : ℝ :=
  (-(2145*t^2+4418*t+2280)/(210*(t+1)^2))*su ((t+2)/3)/t+
  (64*(10*t^4+18*t^3-t^2-6*t+3)/(945*t^4))*sl ((t+3)*(t+2)/(6*(t+1)))/t+
  (250*(-5*t^2+21*t+26)/(189*(-t^2+6*t+6)))*sl ((t^2+18*t+21)*(t+2)^2/(90*(t+1)^2))/t+
  (250*(-11*t^2+97*t+108)/(189*radical*(-t^2+6*t+6)))*
    sl ((t+9-2*radical)*(5+radical)/((t+9+2*radical)*(5-radical)))/t+
  SigmaRationalOuterFTC.jointNum t/SigmaRationalOuterFTC.jointDen t

end Hf4Quad
