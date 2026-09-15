import WRMapMSigmaKernel

noncomputable section
namespace WuPaper.RMapMSigma
open Real Set MeasureTheory NodeExtension
open scoped Interval

theorem weighted_tail_exchange {a b B : ℝ} (hab : a ≤ b) (hbB : b ≤ B)
    {p w : ℝ → ℝ} (hp : IntervalIntegrable p volume a B)
    (hw : IntervalIntegrable w volume a b) (C : ℝ) :
    IntervalIntegrable (fun x => (C + ∫ t in x..B, p t) * w x) volume a b ∧
    (∫ x in a..b, (C + ∫ t in x..B, p t) * w x) =
      (C + ∫ t in b..B, p t) * (∫ x in a..b, w x) +
        ∫ t in a..b, p t * (∫ x in a..t, w x) := by
  have hpab : IntervalIntegrable p volume a b := by
    apply hp.mono_set
    rw [uIcc_of_le hab, uIcc_of_le (hab.trans hbB)]
    exact Icc_subset_Icc le_rfl hbB
  have hpB : IntervalIntegrable p volume b B := by
    apply hp.mono_set
    rw [uIcc_of_le hbB, uIcc_of_le (hab.trans hbB)]
    exact Icc_subset_Icc hab le_rfl
  have hc : ContinuousOn (fun x => ∫ t in x..b, p t) (uIcc a b) :=
    intervalIntegral.continuousOn_primitive_interval_left
      ((intervalIntegrable_iff' (by finiteness)).mp hpab)
  have htri : IntervalIntegrable (fun x => (∫ t in x..b, p t) * w x) volume a b := by
    simpa only [mul_comm] using hw.mul_continuousOn hc
  have he (x : ℝ) (hx : x ∈ uIcc a b) :
      (C + ∫ t in x..B, p t) * w x =
        (C + ∫ t in b..B, p t) * w x + (∫ t in x..b, p t) * w x := by
    rw [uIcc_of_le hab] at hx
    have hpx : IntervalIntegrable p volume x b := by
      apply hpab.mono_set
      rw [uIcc_of_le hx.2, uIcc_of_le hab]
      exact Icc_subset_Icc hx.1 le_rfl
    rw [← intervalIntegral.integral_add_adjacent_intervals hpx hpB]
    ring
  have hi := (hw.const_mul (C + ∫ t in b..B, p t)).add htri
  constructor
  · exact hi.congr (fun x hx => (he x (uIoc_subset_uIcc hx)).symm)
  · have hF : IntegrableOn (fun z : ℝ × ℝ => w z.1 * p z.2)
        (Icc a b ×ˢ Icc a b) := by
      change Integrable _ ((volume.prod volume).restrict (Icc a b ×ˢ Icc a b))
      rw [← Measure.prod_restrict]
      exact ((intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp hw).mul_prod
        ((intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp hpab)
    have hswap := triangle_swap hab (fun z : ℝ × ℝ => w z.1 * p z.2) hF
    have ht : (∫ x in a..b, (∫ t in x..b, p t) * w x) =
        ∫ t in a..b, p t * (∫ x in a..t, w x) := by
      simpa only [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_mul_const, mul_comm] using hswap
    rw [intervalIntegral.integral_congr he,
      intervalIntegral.integral_add (hw.const_mul _) htri,
      intervalIntegral.integral_const_mul, ht]

def rationalWeight (c x : ℝ) : ℝ := c / (x * (c - x))

theorem rationalWeight_continuous {c a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbc : b < c) :
    ContinuousOn (rationalWeight c) (uIcc a b) := by
  apply continuousOn_const.div (continuousOn_id.mul (continuousOn_const.sub continuousOn_id))
  rw [uIcc_of_le hab]
  intro x hx
  dsimp
  exact mul_ne_zero (by linarith [hx.1]) (by linarith [hx.2])

theorem rationalWeight_primitive {c a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbc : b < c) :
    (∫ x in a..b, rationalWeight c x) = log ((c - a) * b / (a * (c - b))) := by
  have hd (x : ℝ) (hx : x ∈ uIcc a b) :
      HasDerivAt (fun x : ℝ => log x - log (c - x)) (rationalWeight c x) x := by
    rw [uIcc_of_le hab] at hx
    have hx0 : x ≠ 0 := by linarith [hx.1]
    have hcx : c - x ≠ 0 := by linarith [hx.2]
    have h := ((hasDerivAt_id x).log hx0).sub
      (((hasDerivAt_const x c).sub (hasDerivAt_id x)).log hcx)
    have he : rationalWeight c x = 1 / x - (0 - 1) / (c - x) := by
      dsimp [rationalWeight]
      field_simp
      ring
    rw [he]
    exact h
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (rationalWeight_continuous ha hab hbc).intervalIntegrable]
  have hb : 0 < b := ha.trans_le hab
  have hca : 0 < c - a := by linarith
  have hcb : 0 < c - b := by linarith
  rw [log_div (mul_ne_zero hca.ne' hb.ne') (mul_ne_zero ha.ne' hcb.ne'),
    log_mul hca.ne' hb.ne', log_mul ha.ne' hcb.ne']
  ring

theorem rationalWeight_rescale {a b c : ℝ} (ha : 0 < a) (hab : a < b)
    (hb : b < 1) (hc : 0 < c) (F : ℝ → ℝ) :
    (∫ t in a..b, F (c * t) / (t * (1 - t))) =
      ∫ u in (a * c)..(b * c), F u * rationalWeight c u := by
  have he : (∫ t in a..b, F (c * t) / (t * (1 - t))) =
      c * ∫ t in a..b, F (c * t) * rationalWeight c (c * t) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hab.le] at ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have ht1 : 1 - t ≠ 0 := by linarith [ht.2]
    have hct : c - c * t ≠ 0 := by
      rw [← mul_one_sub]
      exact mul_ne_zero hc.ne' ht1
    dsimp [rationalWeight]
    field_simp
  rw [he, intervalIntegral.integral_comp_mul_left
    (fun u => F u * rationalWeight c u) hc.ne']
  simp only [smul_eq_mul]
  rw [← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul, mul_comm c a, mul_comm c b]

theorem rationalWeight_source_log {a b c : ℝ} (ha : 0 < a) (hab : a < b)
    (hb : b < 1) (hc : 0 < c) :
    (∫ u in (a * c)..(b * c), rationalWeight c u) =
      log ((b - a * b) / (a - a * b)) := by
  rw [rationalWeight_primitive (mul_pos ha hc) (mul_le_mul_of_nonneg_right hab.le hc.le)
    (by nlinarith : b * c < c)]
  congr 1
  have hb1 : 1 - b ≠ 0 := by linarith
  have hcb : c - b * c ≠ 0 := by nlinarith
  have hab0 : a - a * b ≠ 0 := by nlinarith
  field_simp

theorem rationalWeight_partial_log {a b c u : ℝ} (ha : 0 < a) (_hab : a < b)
    (hb : b < 1) (hc : 0 < c) (hu : u ∈ Icc (a * c) (b * c)) :
    (∫ x in (a * c)..u, rationalWeight c x) =
      log ((1 - a) * u / (a * (c - u))) := by
  rw [rationalWeight_primitive (mul_pos ha hc) hu.1 (by nlinarith [hu.2] : u < c)]
  congr 1
  have hcu : c - u ≠ 0 := by nlinarith [hu.2]
  field_simp

end WuPaper.RMapMSigma

#check @WuPaper.RMapMSigma.weighted_tail_exchange
#check @WuPaper.RMapMSigma.rationalWeight
#check @WuPaper.RMapMSigma.rationalWeight_continuous
#check @WuPaper.RMapMSigma.rationalWeight_primitive
#check @WuPaper.RMapMSigma.rationalWeight_rescale
#check @WuPaper.RMapMSigma.rationalWeight_source_log
#check @WuPaper.RMapMSigma.rationalWeight_partial_log
#print axioms WuPaper.RMapMSigma.weighted_tail_exchange
#print axioms WuPaper.RMapMSigma.rationalWeight
#print axioms WuPaper.RMapMSigma.rationalWeight_continuous
#print axioms WuPaper.RMapMSigma.rationalWeight_primitive
#print axioms WuPaper.RMapMSigma.rationalWeight_rescale
#print axioms WuPaper.RMapMSigma.rationalWeight_source_log
#print axioms WuPaper.RMapMSigma.rationalWeight_partial_log
