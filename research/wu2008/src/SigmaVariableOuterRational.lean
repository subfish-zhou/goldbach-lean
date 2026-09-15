import SigmaVariableOuterSigns

noncomputable section
namespace SigmaVariableOuterPayment
open Real TerminalE SigmaVariableFull

/-- Exact ratios after joint removal of the moving-pole logarithm. -/
def zeroRatio (t : ℝ) : ℝ := (t+2)/3
def negRatio (t : ℝ) : ℝ := (t+3)*(t+2)/(6*(t+1))
def quadRatio (t : ℝ) : ℝ := (t^2+18*t+21)*(t+2)^2/(90*(t+1)^2)
def radRatio (t : ℝ) : ℝ :=
  ((t+9-2*radical)*(5+radical))/((t+9+2*radical)*(5-radical))

theorem zeroRatio_ge {t : ℝ} (ht : 1 ≤ t) : 1 ≤ zeroRatio t := by
  unfold zeroRatio
  linarith

theorem negRatio_ge {t : ℝ} (ht : 1 ≤ t) : 1 ≤ negRatio t := by
  unfold negRatio
  apply (one_le_div (by positivity : 0<6*(t+1))).mpr
  have h : 0 ≤ (t-1)*(t+2) := mul_nonneg (by linarith) (by linarith)
  nlinarith only [h]

theorem quadRatio_ge {t : ℝ} (ht : 1 ≤ t) : 1 ≤ quadRatio t := by
  unfold quadRatio
  apply (one_le_div (by positivity : 0<90*(t+1)^2)).mpr
  have he : (t^2+18*t+21)*(t+2)^2-90*(t+1)^2=
      (t-1)^4+26*(t-1)^3+79*(t-1)^2+60*(t-1) := by ring
  have h : 0 ≤ t-1 := by linarith
  have hn : 0 ≤ (t-1)^4+26*(t-1)^3+79*(t-1)^2+60*(t-1) := by positivity
  linarith only [he,hn]

theorem radRatio_ge {t : ℝ} (ht : 1 ≤ t) : 1 ≤ radRatio t := by
  have h5 : 0<5-radical := by linarith [radical_lt_four]
  have hp : 0<t+9+2*radical := by linarith [radical_pos]
  unfold radRatio
  apply (one_le_div (mul_pos hp h5)).mpr
  have h : 0 ≤ radical*(t-1) := mul_nonneg radical_pos.le (by linarith)
  nlinarith only [h]

/-- This preserves the exact collected mass, including every rational principal part. -/
theorem mass_regrouped {t : ℝ} (ht : 1 ≤ t) :
    collectedMass t=
      logZeroCoeff (-(t+1))*log (zeroRatio t)+
      logNegCoeff (-(t+1))*log (negRatio t)+
      logQuadCoeff (-(t+1))*log (quadRatio t)+
      logRadCoeff (-(t+1))*log (radRatio t)+
      jointRational (-(t+1)) ((t+1)/2)-jointRational (-(t+1)) 1 := by
  let x := (t+1)/2
  let m := (x-(-(t+1)))/(1-(-(t+1)))
  have hx : 0<x := by dsimp [x]; linarith
  have hxp : 0<x-(-(t+1)) := by dsimp [x]; linarith
  have h1p : 0<1-(-(t+1)) := by linarith
  have hm : 0 < m := div_pos hxp h1p
  have hq : 0<q x := by unfold q; positivity
  have hq1 : 0<q 1 := by norm_num [q]
  have hxm : 0<x+4-radical := by dsimp [x]; linarith [radical_lt_four]
  have hxp4 : 0<x+4+radical := by linarith [radical_pos]
  have h5m : 0<1+4-radical := by linarith [radical_lt_four]
  have h5p : 0<1+4+radical := by linarith [radical_pos]
  have ht1 : t+1 ≠ 0 := by linarith
  have ht2 : t+2 ≠ 0 := by linarith
  have ht2' : 1-(-(t+1)) ≠ 0 := h1p.ne'
  have he0 : zeroRatio t=x/m := by
    dsimp [zeroRatio,m,x]
    field_simp
    ring
  have he1 : negRatio t=((x+1)/2)/m := by
    dsimp [negRatio,m,x]
    field_simp
    ring
  have heq : quadRatio t=(q x/q 1)/m^2 := by
    dsimp [quadRatio,m,x,q]
    field_simp
    ring
  have her : radRatio t=((x+4-radical)*(1+4+radical))/
      ((x+4+radical)*(1+4-radical)) := by
    have hd : (t+9+2*radical)*(5-radical) ≠ 0 := by
      apply mul_ne_zero
      · have hp : 0<t+9+2*radical := by linarith [radical_pos]
        exact hp.ne'
      · have hm5 : 0<5-radical := by linarith [radical_lt_four]
        exact hm5.ne'
    apply (div_eq_div_iff hd (mul_pos hxp4 h5m).ne').mpr
    dsimp [radRatio,x]
    ring
  have hl0 : log (zeroRatio t)=log x-log m := by
    rw [he0,log_div hx.ne' hm.ne']
  have hl1 : log (negRatio t)=log (x+1)-log 2-log m := by
    rw [he1,log_div (div_pos (by positivity) (by norm_num)).ne' hm.ne',
      log_div (by positivity : x+1 ≠ 0) (by norm_num : (2:ℝ) ≠ 0)]
  have hlq : log (quadRatio t)=log (q x)-log (q 1)-2*log m := by
    rw [heq,log_div (div_pos hq hq1).ne' (pow_ne_zero 2 hm.ne'),
      log_div hq.ne' hq1.ne',log_pow]
    norm_num
  have hlr : log (radRatio t)=
      log (x+4-radical)-log (x+4+radical)-log (1+4-radical)+log (1+4+radical) := by
    rw [her,log_div (mul_pos hxm h5p).ne' (mul_pos hxp4 h5m).ne',
      log_mul hxm.ne' h5p.ne',log_mul hxp4.ne' h5m.ne']
    ring
  have hlm : log m=log (x-(-(t+1)))-log (1-(-(t+1))) := log_div hxp.ne' h1p.ne'
  rw [hl0,hl1,hlq,hlr]
  unfold collectedMass
  change _ = _
  dsimp [x] at hlm ⊢
  rw [←hlm]
  have hb := joint_coefficient_balance (-(t+1))
  rw [←hb]
  ring

/-- A branch-free rational lower mass using the already admitted split exactly once. -/
def paidMass (t : ℝ) : ℝ :=
  logZeroCoeff (-(t+1))*RemainingHf.splitUpper (zeroRatio t)+
  logNegCoeff (-(t+1))*RemainingHf.splitLower (negRatio t)+
  logQuadCoeff (-(t+1))*RemainingHf.splitLower (quadRatio t)+
  logRadCoeff (-(t+1))*RemainingHf.splitLower (radRatio t)+
  jointRational (-(t+1)) ((t+1)/2)-jointRational (-(t+1)) 1

theorem paidMass_le_collected {t : ℝ} (ht : t ∈ Set.Icc 1 3) :
    paidMass t ≤ collectedMass t := by
  have h0 := mul_le_mul_of_nonpos_left (RemainingHf.le_splitUpper (zeroRatio_ge ht.1))
    (zero_coefficient_neg ht.1).le
  have h1 := mul_le_mul_of_nonneg_left (RemainingHf.splitLower_le (negRatio_ge ht.1))
    (neg_coefficient_pos ht.1).le
  have hq := mul_le_mul_of_nonneg_left (RemainingHf.splitLower_le (quadRatio_ge ht.1))
    (quad_coefficient_pos ht).le
  have hr := mul_le_mul_of_nonneg_left (RemainingHf.splitLower_le (radRatio_ge ht.1))
    (rad_coefficient_pos ht).le
  rw [mass_regrouped ht.1]
  unfold paidMass
  linarith only [h0,h1,hq,hr]

/-- The original external divisor is retained. -/
def paidWeight (t : ℝ) : ℝ := paidMass t/t

theorem paidWeight_le {t : ℝ} (ht : t ∈ Set.Icc 1 3) : paidWeight t ≤ weight t := by
  unfold paidWeight weight
  rw [←collectedMass_identity]
  exact div_le_div_of_nonneg_right (paidMass_le_collected ht) (by linarith [ht.1])

end SigmaVariableOuterPayment
