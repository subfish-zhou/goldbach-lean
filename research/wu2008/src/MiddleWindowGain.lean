import DisjointTailGain

namespace Wu2008DoubleSieve.Phase12
open Real Set MeasureTheory HighSixPhase9 SingleUpperHSource SingleUpperHIntegral Phase11
noncomputable section

/-- The fixed anchor is induced by the original upper endpoint, not by a search. -/
def sB : ℝ := 51327/10000
def middleMass : ℝ := k4*(33/5-sB)^4
def Cmid : ℝ := 2*16*middleMass*(2/5)*truncatedSixthLowerAlpha
def Cfull : ℝ := Cgeo+Ctail+Cmid

theorem sB_identity : (1/2-b0)/truncatedSixthLowerAlpha = sB := by
  norm_num [sB,b0,truncatedSixthLowerAlpha]

theorem sB_domain : sB ∈ Icc (5 : ℝ) (33/5) := by norm_num [sB]

theorem middleMass_exact : middleMass =
    (1716769171734483/2143232000000000000 : ℝ) := by
  norm_num [middleMass,k4,sB]

theorem middleMass_pos : 0 < middleMass := by rw [middleMass_exact]; norm_num

theorem Cmid_exact : Cmid = (1716769171734483/2221928800000000000 : ℝ) := by
  norm_num [Cmid,middleMass,k4,sB,truncatedSixthLowerAlpha]

theorem Cmid_pos : 0 < Cmid := by rw [Cmid_exact]; norm_num

theorem Cfull_pos : 0 < Cfull := add_pos (add_pos Cgeo_pos Ctail_pos) Cmid_pos

/-- The actual antitone theorem is used only in its original [1,10] domain. -/
theorem H_quartic_antitone {δ s r : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100)
    (hs : 1 ≤ s) (hsr : s ≤ r) (hr : r ∈ Icc (5 : ℝ) (33/5)) :
    amplitude δ*k4*(33/5-r)^4 ≤ wuImprovementLimit true δ s := by
  exact (H_quartic hδ hδhi hr).trans
    (wuImprovementLimit_upper_antitone hδ (by linarith)
      ⟨hs,by linarith [hr.2]⟩ ⟨by linarith [hr.1],by linarith [hr.2]⟩ hsr)

theorem middle_argument {δ t : ℝ} (hδ : 0 < δ)
    (ht : t ∈ Icc b0 (shapeLeft δ)) :
    argument δ t ∈ Icc (23/5 : ℝ) sB := by
  constructor
  · apply (le_div_iff₀ (by norm_num [truncatedSixthLowerAlpha])).2
    dsimp [shapeLeft] at ht
    linarith [ht.2]
  · apply (div_le_iff₀ (by norm_num [truncatedSixthLowerAlpha])).2
    dsimp [b0,sB,truncatedSixthLowerAlpha] at *
    linarith [ht.1]

theorem middle_width {δ : ℝ} (hδhi : δ ≤ 1/100) :
    (2/5)*truncatedSixthLowerAlpha ≤ shapeLeft δ-b0 := by
  dsimp [shapeLeft,b0]
  linarith

/-- Positive constant mass stays inside the original weighted kernel. -/
theorem kernel_middle_lower {δ t : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100)
    (ht : t ∈ Icc b0 (shapeLeft δ)) :
    16*amplitude δ*middleMass ≤ kernel δ t := by
  have hg := tail_geometry hδ hδhi
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num [b0,truncatedSixthLowerAlpha]) ht.1
  have htHi : t ≤ (1/2-δ)/2 := ht.2.trans hg.2.2.2
  have hct : 0 < (1/2-δ)-t := by linarith
  have hd : t*((1/2-δ)-t) ≤ (1/16 : ℝ) := by
    have hc : (1/2-δ)^2 ≤ (1/2 : ℝ)^2 :=
      pow_le_pow_left₀ (by linarith) (by linarith) 2
    nlinarith only [hc,sq_nonneg (t-(1/2-δ)/2)]
  have harg := middle_argument hδ ht
  have hH := H_quartic_antitone hδ hδhi (by linarith [harg.1]) harg.2 sB_domain
  have he : amplitude δ*k4*(33/5-sB)^4 = amplitude δ*middleMass := by
    unfold middleMass
    ring
  rw [he] at hH
  have hp := mul_nonneg (amplitude_nonneg hδ hδhi) middleMass_pos.le
  unfold kernel
  apply (le_div_iff₀ (mul_pos ht0 hct)).2
  have hh := mul_le_mul_of_nonneg_left hd hp
  nlinarith only [hH,hh]

/-- Kernel integrability is inherited; only the constant comparison is integrated. -/
theorem middle_integral_lower {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100) :
    (16*amplitude δ*middleMass)*((2/5)*truncatedSixthLowerAlpha) ≤
      ∫ t in b0..shapeLeft δ, kernel δ t := by
  have hg := tail_geometry hδ hδhi
  have hi := kernel_integrable hδ hδhi
    (show truncatedSixthLowerAlpha/2 ≤ b0 by norm_num [b0,truncatedSixthLowerAlpha])
    hg.2.2.1.le hg.2.2.2
  have hm := intervalIntegral.integral_mono_on hg.2.2.1.le intervalIntegrable_const hi
    (fun t ht => kernel_middle_lower hδ hδhi ht)
  rw [intervalIntegral.integral_const,smul_eq_mul] at hm
  have hp : 0 ≤ 16*amplitude δ*middleMass :=
    mul_nonneg (mul_nonneg (by norm_num) (amplitude_nonneg hδ hδhi)) middleMass_pos.le
  have hw := mul_le_mul_of_nonneg_left (middle_width hδhi) hp
  nlinarith only [hm,hw]

/-- Rebuild all three disjoint pieces of ONE original integral. -/
theorem three_piece_original_integral_lower {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100) :
    tailCoefficient δ/5*((b0-a0)^5-(truncatedSixthLowerAlpha-a0)^5)+
      shapeCoefficient δ/3*(513/5308)^3+
      (16*amplitude δ*middleMass)*((2/5)*truncatedSixthLowerAlpha) ≤
      ∫ t in truncatedSixthLowerAlpha..((1/2-δ)/2), kernel δ t := by
  have hg := tail_geometry hδ hδhi
  have hs := shape_geometry hδ hδhi
  have ha : truncatedSixthLowerAlpha/2 ≤ truncatedSixthLowerAlpha := by
    norm_num [truncatedSixthLowerAlpha]
  have hi1 := kernel_integrable hδ hδhi ha hg.2.1.le (hg.2.2.1.le.trans hg.2.2.2)
  have hi2 := kernel_integrable hδ hδhi (ha.trans hg.2.1.le) hg.2.2.1.le hg.2.2.2
  have hi3 := kernel_integrable hδ hδhi (ha.trans hs.1) hg.2.2.2 le_rfl
  have htail : tailCoefficient δ/5*((b0-a0)^5-(truncatedSixthLowerAlpha-a0)^5) ≤
      ∫ t in truncatedSixthLowerAlpha..b0, kernel δ t := by
    have hi : IntervalIntegrable (fun t : ℝ => tailCoefficient δ*(t-a0)^4)
        volume truncatedSixthLowerAlpha b0 :=
      (continuous_const.mul ((continuous_id.sub continuous_const).pow 4)).intervalIntegrable _ _
    have hm := intervalIntegral.integral_mono_on hg.2.1.le hi hi1
      (fun t ht => kernel_tail_lower hδ hδhi ht)
    rwa [quartic_integral] at hm
  have hmiddle := middle_integral_lower hδ hδhi
  have hlast : shapeCoefficient δ/3*((1/2-δ)/2-shapeLeft δ)^3 ≤
      ∫ t in shapeLeft δ..((1/2-δ)/2), kernel δ t := by
    have hi : IntervalIntegrable (fun t : ℝ => shapeCoefficient δ*(t-shapeLeft δ)^2)
        volume (shapeLeft δ) ((1/2-δ)/2) :=
      (continuous_const.mul ((continuous_id.sub continuous_const).pow 2)).intervalIntegrable _ _
    have hm := intervalIntegral.integral_mono_on hg.2.2.2 hi hi3
      (fun t ht => kernel_shape_lower hδ hδhi ht)
    rwa [quadratic_integral] at hm
  have hwidth := mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 513/5308) hs.2.2 3)
    (div_nonneg (shapeCoefficient_nonneg hδ hδhi) (by norm_num : (0 : ℝ) ≤ 3))
  have hadd12 := intervalIntegral.integral_add_adjacent_intervals hi1 hi2
  have hadd123 := intervalIntegral.integral_add_adjacent_intervals (hi1.trans hi2) hi3
  linarith only [htail,hmiddle,hlast,hwidth,hadd12,hadd123]

theorem Cmid_identity (δ : ℝ) : Cmid*amplitude δ =
    2*((16*amplitude δ*middleMass)*((2/5)*truncatedSixthLowerAlpha)) := by
  unfold Cmid
  ring

/-- The genuine doubling and final division by four remain unchanged. -/
theorem actual_low_H_full_lower {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100) :
    Cfull*amplitude δ ≤ gainH34 δ/4 := by
  have hi := three_piece_original_integral_lower hδ hδhi
  rw [Cfull,add_mul,add_mul,Cgeo_identity,Ctail_identity,Cmid_identity]
  dsimp [gainH34,windowGain]
  linarith only [hi]

end
end Wu2008DoubleSieve.Phase12
