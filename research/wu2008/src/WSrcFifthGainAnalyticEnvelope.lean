import WSrcFifthGainRoot
import WE09JointMainMajorLog

namespace WuSource.SrcFifthGain.Analytic
open Wu2008DoubleSieve WuTarget.Wu08FifthSource SharpMassBalance
open MeasureTheory Set Real
open scoped Interval
noncomputable section

def denominator (s : ℝ) : ℝ := s*(1-2*a*s)
def lowerSlope (l : ℝ) : ℝ := a/(l*(1/2-a*l)^2)
def upperSlope (l : ℝ) : ℝ :=
  2/((2+FifthClassicalShape.q-l)*denominator l)

theorem log_ratio_lower {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    2*(y-x)/(y+x) ≤ log (y/x) := by
  have ht : 1 ≤ y/x := (le_div_iff₀ hx).mpr (by simpa using hxy)
  have hp := WuTarget.E09JointMainMajor.log_lower ht
  have hq : 0 ≤ (y/x-1)/(y/x+1) := div_nonneg (by linarith) (by linarith)
  have h3 := pow_nonneg hq 3
  have h5 := pow_nonneg hq 5
  have h7 := pow_nonneg hq 7
  unfold WuTarget.E09JointMainMajor.lowerLog at hp
  have hh : 2*((y/x-1)/(y/x+1)) ≤ log (y/x) := by
    linarith only [hp, h3, h5, h7]
  have he : 2*((y/x-1)/(y/x+1)) = 2*(y-x)/(y+x) := by
    field_simp [hx.ne']
  rwa [he] at hh

theorem parameter_bounds {s : ℝ} (hs : s ∈ Icc s0 FifthClassicalShape.q) :
    0 < a ∧ 0 < s ∧ 0 < 1/2-a*s ∧ 1 ≤ 4*a*s := by
  have ha : 0 < a := truncatedSixthLower_parameters.1
  have hz := slice_geometry (scalar_geometry hs)
  have hs0 : 0 < s0 := by
    norm_num [s0, a, b, truncatedSixthLowerAlpha, truncatedSixthLowerBeta]
  have hbase : (1 : ℝ) ≤ 4*a*s0 := by
    norm_num [s0, a, b, truncatedSixthLowerAlpha, truncatedSixthLowerBeta]
  have hm := mul_le_mul_of_nonneg_left hs.1 (by positivity : 0 ≤ 4*a)
  exact ⟨ha, hs0.trans_le hs.1, hz.2.2.1, hbase.trans hm⟩

theorem denominator_pos {s : ℝ} (hs : s ∈ Icc s0 FifthClassicalShape.q) :
    0 < denominator s := by
  have hp := parameter_bounds hs
  exact mul_pos hp.2.1 (by linarith [hp.2.2.1])

theorem denominator_antitone {l s : ℝ}
    (hl : l ∈ Icc s0 FifthClassicalShape.q)
    (hls : l ≤ s) :
    denominator s ≤ denominator l := by
  have hp := parameter_bounds hl
  have hs : 0 ≤ s-l := sub_nonneg.mpr hls
  have hc : 0 ≤ 2*a*(s+l)-1 := by
    have h := mul_nonneg hp.1.le hs
    nlinarith [hp.2.2.2]
  have hprod := mul_nonneg hs hc
  unfold denominator
  nlinarith only [hprod]

theorem low_log_lower {s : ℝ} (hs : s ∈ Icc s0 geometricSplit) :
    2*a*(s-s0)/(1/2-a*s) ≤ log (2*b/(1-2*b-2*a*s)) := by
  have ha : 0 < a := truncatedSixthLower_parameters.1
  have hsplit : a ≤ 1/2-a*s-b := by
    have h := (le_div_iff₀ ha).mp hs.2
    linarith
  have hpos : 0 < 1/2-a*s-b := ha.trans_le hsplit
  have hsmall : 1/2-a*s-b ≤ b := by
    have h := (div_le_iff₀ ha).mp hs.1
    linarith
  have h := log_ratio_lower hpos hsmall
  have he : 2*(b-(1/2-a*s-b))/(b+(1/2-a*s-b)) =
      2*a*(s-s0)/(1/2-a*s) := by
    unfold s0
    field_simp [ha.ne']
    ring
  have hr : 2*b/(1-2*b-2*a*s) = b/(1/2-a*s-b) := by
    rw [show (1 : ℝ)-2*b-2*a*s = 2*(1/2-a*s-b) by ring]
    exact mul_div_mul_left b (1/2-a*s-b) (by norm_num : (2 : ℝ) ≠ 0)
  rwa [he, ← hr] at h

theorem high_log_lower {s : ℝ} (hs : s ≤ FifthClassicalShape.q) :
    2*(FifthClassicalShape.q-s)/(2+FifthClassicalShape.q-s) ≤
      log (1/(2*a)-1-s) := by
  have h := log_ratio_lower (by norm_num : (0 : ℝ) < 1)
    (show (1 : ℝ) ≤ 1+FifthClassicalShape.q-s by linarith)
  have he : (1 : ℝ)+FifthClassicalShape.q-s = 1/(2*a)-1-s := by
    unfold FifthClassicalShape.q
    have ha := truncatedSixthLower_parameters.1.ne'
    change a ≠ 0 at ha
    field_simp [ha]
    ring
  rw [div_one, show (1 : ℝ)+FifthClassicalShape.q-s-1 =
    FifthClassicalShape.q-s by ring,
    show (1 : ℝ)+FifthClassicalShape.q-s+1 = 2+FifthClassicalShape.q-s by ring,
    he] at h
  exact h

theorem lower_envelope {l s : ℝ} (hl : s0 ≤ l) (hls : l ≤ s)
    (hs : s ≤ geometricSplit) :
    lowerSlope l*(s-s0) ≤ weight s := by
  have hsq : s ≤ FifthClassicalShape.q := hs.trans fixed_breakpoints.2.2.2.2.2.le
  have hlmem : l ∈ Icc s0 FifthClassicalShape.q := ⟨hl, hls.trans hsq⟩
  have hsmem : s ∈ Icc s0 FifthClassicalShape.q := ⟨hl.trans hls, hsq⟩
  have hpl := parameter_bounds hlmem
  have hps := parameter_bounds hsmem
  have hcl : 1/2-a*s ≤ 1/2-a*l := by
    nlinarith [mul_nonneg hpl.1.le (sub_nonneg.mpr hls)]
  have hn : 0 ≤ 2*a*(s-s0) :=
    mul_nonneg (mul_nonneg (by norm_num) hpl.1.le) (sub_nonneg.mpr (hl.trans hls))
  have hlog := (div_le_div_of_nonneg_left hn hps.2.2.1 hcl).trans
    (low_log_lower ⟨hl.trans hls, hs⟩)
  have hrat : 0 ≤ 2*a*(s-s0)/(1/2-a*l) := div_nonneg hn hpl.2.2.1.le
  have hd := denominator_antitone hlmem hls
  have hh := (div_le_div_of_nonneg_left hrat (denominator_pos hsmem) hd).trans
    (div_le_div_of_nonneg_right hlog (denominator_pos hsmem).le)
  rw [weight_lower ⟨hl.trans hls, hs⟩]
  change lowerSlope l*(s-s0) ≤ log (2*b/(1-2*b-2*a*s))/denominator s
  have he : lowerSlope l*(s-s0) = (2*a*(s-s0)/(1/2-a*l))/denominator l := by
    unfold lowerSlope denominator
    rw [show (1 : ℝ)-2*a*l=2*(1/2-a*l) by ring]
    field_simp
  rw [he]
  exact hh

theorem upper_envelope {l s : ℝ} (hl : geometricSplit ≤ l) (hls : l ≤ s)
    (hs : s ≤ FifthClassicalShape.q) :
    upperSlope l*(FifthClassicalShape.q-s) ≤ weight s := by
  have hL : s0 ≤ geometricSplit := by
    linarith [fixed_breakpoints.2.2.2.1, fixed_breakpoints.2.2.2.2.1]
  have hlmem : l ∈ Icc s0 FifthClassicalShape.q := ⟨hL.trans hl, hls.trans hs⟩
  have hsmem : s ∈ Icc s0 FifthClassicalShape.q := ⟨hL.trans (hl.trans hls), hs⟩
  have hn : 0 ≤ 2*(FifthClassicalShape.q-s) := by linarith
  have hz : 0 < 2+FifthClassicalShape.q-s := by linarith
  have hlog := (div_le_div_of_nonneg_left hn hz
    (show 2+FifthClassicalShape.q-s ≤ 2+FifthClassicalShape.q-l by linarith)).trans
      (high_log_lower hs)
  have hrat : 0 ≤ 2*(FifthClassicalShape.q-s)/(2+FifthClassicalShape.q-l) :=
    div_nonneg hn (by linarith)
  have hh := (div_le_div_of_nonneg_left hrat (denominator_pos hsmem)
    (denominator_antitone hlmem hls)).trans
      (div_le_div_of_nonneg_right hlog (denominator_pos hsmem).le)
  rw [weight_upper ⟨hl.trans hls, hs⟩]
  change upperSlope l*(FifthClassicalShape.q-s) ≤
    log (1/(2*a)-1-s)/denominator s
  have he : upperSlope l*(FifthClassicalShape.q-s) =
      (2*(FifthClassicalShape.q-s)/(2+FifthClassicalShape.q-l))/denominator l := by
    unfold upperSlope
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [he]
  exact hh

end
end WuSource.SrcFifthGain.Analytic
