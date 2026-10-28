import Hf4QuadKernelData

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
noncomputable section
namespace Hf4Quad

/-- Exact rational form of the old lower envelope in the Cayley coordinate. -/
def lowZ (z : ℝ) : ℝ :=
  2*z*(525+z*(1050+z*(385+z*(-280+z*(-140+z^2*(12-2*z))))))/
    (105*(1+z)^2*(5-3*z^2))

/-- Exact rational form of the old upper envelope in the Cayley coordinate. -/
def upZ (z : ℝ) : ℝ :=
  2*z*(105+z*(105+z*(-70+z*(-70+z*(-14+z*(-14-6*z))))))/
    (105*(1-z)*(1+z)^2)

theorem lowZ_eq {z : ℝ} (hz : 0 ≤ z) (hz' : z < 1) :
    lowZ z = low ((1+z)/(1-z)) := by
  have hm : 1-z ≠ 0 := by linarith
  have hp : 1+z ≠ 0 := by linarith
  have hq : 5-3*z^2 ≠ 0 := by nlinarith [mul_pos (by linarith : 0 < 1-z) (by linarith : 0 < 1+z)]
  have hq' : 10-z^2*6 ≠ 0 := by nlinarith [mul_pos (by linarith : 0 < 1-z) (by linarith : 0 < 1+z)]
  have hq'' : 5-z^2*3 ≠ 0 := by nlinarith [mul_pos (by linarith : 0 < 1-z) (by linarith : 0 < 1+z)]
  unfold lowZ low
  field_simp
  ring_nf
  field_simp [hq',hq'']
  ring

theorem upZ_eq {z : ℝ} (hz : 0 ≤ z) (hz' : z < 1) :
    upZ z = up ((1+z)/(1-z)) := by
  have hm : 1-z ≠ 0 := by linarith
  have hp : 1+z ≠ 0 := by linarith
  unfold upZ up
  field_simp
  ring

def slCompact (x : ℝ) : ℝ := lowZ ((x-1)/(x+3))+lowZ ((x-1)/(3*x+1))
def suCompact (x : ℝ) : ℝ := upZ ((x-1)/(x+3))+upZ ((x-1)/(3*x+1))

theorem lowZ_ratio {x : ℝ} (hx : 1 ≤ x) : lowZ ((x-1)/(x+1)) = low x := by
  have hp : 0 < x+1 := by linarith
  have hz : 0 ≤ (x-1)/(x+1) := div_nonneg (by linarith) hp.le
  have hz' : (x-1)/(x+1) < 1 := (div_lt_iff₀ hp).mpr (by linarith)
  have he : (1+(x-1)/(x+1))/(1-(x-1)/(x+1)) = x := by field_simp; ring
  simpa only [he] using lowZ_eq hz hz'

theorem upZ_ratio {x : ℝ} (hx : 1 ≤ x) : upZ ((x-1)/(x+1)) = up x := by
  have hp : 0 < x+1 := by linarith
  have hz : 0 ≤ (x-1)/(x+1) := div_nonneg (by linarith) hp.le
  have hz' : (x-1)/(x+1) < 1 := (div_lt_iff₀ hp).mpr (by linarith)
  have he : (1+(x-1)/(x+1))/(1-(x-1)/(x+1)) = x := by field_simp; ring
  simpa only [he] using upZ_eq hz hz'

theorem split_coordinate_left (x : ℝ) :
    (((x+1)/2)-1)/(((x+1)/2)+1) = (x-1)/(x+3) := by field_simp; ring

theorem split_coordinate_right {x : ℝ} (hx : 1 ≤ x) :
    (2*x/(x+1)-1)/(2*x/(x+1)+1) = (x-1)/(3*x+1) := by
  have hp : x+1 ≠ 0 := by linarith
  field_simp
  ring

theorem slCompact_eq {x : ℝ} (hx : 1 ≤ x) : slCompact x = sl x := by
  have hl : 1 ≤ (x+1)/2 := by linarith
  have hr : 1 ≤ 2*x/(x+1) := (le_div_iff₀ (by linarith)).mpr (by linarith)
  simpa only [slCompact,sl,suCompact,su,split_coordinate_left,split_coordinate_right hx] using
    congrArg₂ (fun a b : ℝ => a+b) (lowZ_ratio hl) (lowZ_ratio hr)

theorem suCompact_eq {x : ℝ} (hx : 1 ≤ x) : suCompact x = su x := by
  have hl : 1 ≤ (x+1)/2 := by linarith
  have hr : 1 ≤ 2*x/(x+1) := (le_div_iff₀ (by linarith)).mpr (by linarith)
  simpa only [slCompact,sl,suCompact,su,split_coordinate_left,split_coordinate_right hx] using
    congrArg₂ (fun a b : ℝ => a+b) (upZ_ratio hl) (upZ_ratio hr)

open TerminalE

def compactKernel (t : ℝ) : ℝ :=
  (-(2145*t^2+4418*t+2280)/(210*(t+1)^2))*suCompact ((t+2)/3)/t+
  (64*(10*t^4+18*t^3-t^2-6*t+3)/(945*t^4))*slCompact ((t+3)*(t+2)/(6*(t+1)))/t+
  (250*(-5*t^2+21*t+26)/(189*(-t^2+6*t+6)))*slCompact ((t^2+18*t+21)*(t+2)^2/(90*(t+1)^2))/t+
  (250*(-11*t^2+97*t+108)/(189*radical*(-t^2+6*t+6)))*
    slCompact ((t+9-2*radical)*(5+radical)/((t+9+2*radical)*(5-radical)))/t+
  SigmaRationalOuterFTC.jointNum t/SigmaRationalOuterFTC.jointDen t

end Hf4Quad
