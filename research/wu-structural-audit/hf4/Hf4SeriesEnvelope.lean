import Hf4QuadKernel
import WE09JointMainMajorLog

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
noncomputable section
namespace Hf4Quad

def series7 (z : ℝ) : ℝ := 2*z*(1+z^2/3+z^4/5+z^6/7)
def series7Upper (z : ℝ) : ℝ := series7 z+2*z^9/(9*(1-z^2))

theorem series7_log_bounds {z : ℝ} (hz : 0 ≤ z) (hz' : z < 1) :
    series7 z ≤ Real.log ((1+z)/(1-z)) ∧
    Real.log ((1+z)/(1-z)) ≤ series7Upper z := by
  have hm : 0 < 1-z := by linarith
  have hp : 1+z ≠ 0 := by linarith
  have hq : 1-z^2 ≠ 0 := by nlinarith [mul_pos hm (by linarith : 0 < 1+z)]
  have ht : 1 ≤ (1+z)/(1-z) := (le_div_iff₀ hm).mpr (by linarith)
  have he : WuTarget.E09JointMainMajor.lowerLog ((1+z)/(1-z)) = series7 z := by
    unfold WuTarget.E09JointMainMajor.lowerLog series7
    field_simp
    ring
  have hu : WuTarget.E09JointMainMajor.upperLog ((1+z)/(1-z)) = series7Upper z := by
    unfold WuTarget.E09JointMainMajor.upperLog series7Upper
    rw [he]
    congr 1
    field_simp [hq]
    ring
  constructor
  · rw [← he]
    exact WuTarget.E09JointMainMajor.log_lower ht
  · rw [← hu]
    exact WuTarget.E09JointMainMajor.log_upper ht

theorem series7_lower_dominates {z : ℝ} (hz : 0 ≤ z) (hz' : z ≤ 1/3) :
    low ((1+z)/(1-z)) ≤ series7 z := by
  have hm : 1-z ≠ 0 := by linarith
  have hp : z+1 ≠ 0 := by linarith
  have hp' : 1+z ≠ 0 := by linarith
  have h2 : z^2 ≤ 1/9 := by nlinarith
  have h3 : z^3 ≤ 1/27 := by nlinarith [mul_nonneg (sub_nonneg.mpr hz') (sub_nonneg.mpr h2)]
  have hq : 5-3*z^2 > 0 := by nlinarith
  have hq' : 3*z^2-5 ≠ 0 := by linarith
  have he : series7 z-low ((1+z)/(1-z)) =
      2*z^8*(26-33*z-90*z^2-45*z^3)/(105*(z+1)^2*(5-3*z^2)) := by
    unfold series7 low
    field_simp
    ring_nf
    field_simp [show 10-z^2*6 ≠ 0 by nlinarith, show 5-z^2*3 ≠ 0 by nlinarith]
    ring
  have hn : 0 ≤ 26-33*z-90*z^2-45*z^3 := by linarith
  have hh : 0 ≤ series7 z-low ((1+z)/(1-z)) := by
    rw [he]
    positivity
  linarith

theorem series7_upper_dominates {z : ℝ} (hz : 0 ≤ z) (hz' : z < 1) :
    series7Upper z ≤ up ((1+z)/(1-z)) := by
  have hm : 1-z ≠ 0 := by linarith
  have hp : 1+z ≠ 0 := by linarith
  have hq : 1-z^2 ≠ 0 := by nlinarith [mul_pos (sub_pos.mpr hz') (by linarith : 0 < 1+z)]
  have he : up ((1+z)/(1-z))-series7Upper z =
      4*z^8*(5*z^2+5*z+9)/(315*(1-z)*(z+1)^2) := by
    unfold up series7Upper series7
    field_simp [hm,hp,hq]
    ring
  have hh : 0 ≤ up ((1+z)/(1-z))-series7Upper z := by
    rw [he]
    positivity
  linarith
theorem series7_upper_dominates_split {z : ℝ} (hz : 0 ≤ z) (hz' : z ≤ 1/4) :
    series7Upper z ≤ su ((1+z)/(1-z)) := by
  have hm : 1-z ≠ 0 := by linarith
  have hp : 1+z ≠ 0 := by linarith
  have hq : 1-z^2 ≠ 0 := by nlinarith [mul_pos (by linarith : 0 < 1-z) (by linarith : 0 < 1+z)]
  have hzm : 0 < 1-z := by linarith
  have hz2 : z-2 ≠ 0 := by linarith
  have hd : 16-z*32+z^2*24-z^3*8+z^4 ≠ 0 := by
    convert pow_ne_zero 4 hz2 using 1
    ring
  have hd2 : 256-z*512+z^2*384-z^3*128+z^4*16 ≠ 0 := by
    have hh := mul_ne_zero (by norm_num : (16:ℝ) ≠ 0) (pow_ne_zero 4 hz2)
    convert hh using 1
    ring
  have h3 := pow_le_pow_left₀ hz hz' 3
  have h4 := pow_le_pow_left₀ hz hz' 4
  have h7 := pow_le_pow_left₀ hz hz' 7
  have h8 := pow_le_pow_left₀ hz hz' 8
  have hn : 0 ≤ 40*z^10+40*z^9-568*z^8-568*z^7+2856*z^6+2847*z^5-
      5383*z^4-5752*z^3+1048*z^2+112*z+144 := by
    nlinarith only [h3,h4,h7,h8,hz,pow_nonneg hz 2,pow_nonneg hz 5,
      pow_nonneg hz 6,pow_nonneg hz 9,pow_nonneg hz 10]
  have he : su ((1+z)/(1-z))-series7Upper z =
      z^8*(40*z^10+40*z^9-568*z^8-568*z^7+2856*z^6+2847*z^5-
        5383*z^4-5752*z^3+1048*z^2+112*z+144)/
        (630*(z-2)^4*(1-z)*(z+1)^2*(z+2)^4) := by
    unfold su up series7Upper series7
    field_simp [hm,hp,hq]
    ring_nf
  have hh : 0 ≤ su ((1+z)/(1-z))-series7Upper z := by
    rw [he]
    positivity
  linarith

end Hf4Quad
#print axioms Hf4Quad.series7_lower_dominates
#print axioms Hf4Quad.series7_upper_dominates

#print axioms Hf4Quad.series7_upper_dominates_split

#print axioms Hf4Quad.series7_log_bounds
