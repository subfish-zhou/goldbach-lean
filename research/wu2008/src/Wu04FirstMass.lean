import Wu04FirstCost

namespace Wu04FirstMass
open Wu2008DoubleSieve ActualNineFeedback Set MeasureTheory Real
open Wu04FirstCost
open Wu04RecoverGamma (W d d_pos)
open SecondFunctionalGeometricMass
noncomputable section

/-- FTC evaluation on arbitrary ordered positive endpoints; no numerical integration. -/
theorem selected_square_exact {l r h : ℝ} (hl : 1/10≤l) (hlr : l≤r) (hrh : r≤h) :
    (∫ a in l..r,∫ b in a..r,∫ c in r..h,W a b c)=
      log (h/r)*(1/l-(1+log (r/l))/r) := by
  have lpos : 0<l := lt_of_lt_of_le (by norm_num) hl
  have rpos := lpos.trans_le hlr
  have hpos := rpos.trans_le hrh
  have inner (a b : ℝ) (ha : l≤a) (hb : l≤b) :
      (∫ c in r..h,W a b c)=(log (h/r)/a)*(1/b^2) := by
    calc
      _ = ∫ c in r..h,(1/(a*b^2))*(1/c) := by
        apply intervalIntegral.integral_congr
        intro c hc
        rw [uIcc_of_le hrh] at hc
        rw [show W a b c=1/(a*b^2*c) from Omega3ElementaryRegularity.extension_eq
          (hl.trans ha) (hl.trans hb) ((hl.trans hlr).trans hc.1)]
        ring
      _ = _ := by
        rw [intervalIntegral.integral_const_mul,
          integral_one_div_of_pos rpos hpos]
        ring
  have middle (a : ℝ) (ha : a∈Icc l r) :
      (∫ b in a..r,∫ c in r..h,W a b c)=log (h/r)*(1/a^2-(1/r)*(1/a)) := by
    calc
      _ = ∫ b in a..r,(log (h/r)/a)*(1/b^2) := by
        apply intervalIntegral.integral_congr
        intro b hb
        rw [uIcc_of_le ha.2] at hb
        exact inner a b ha.1 (ha.1.trans hb.1)
      _ = _ := by
        rw [intervalIntegral.integral_const_mul,Wu04RecoverGammaMass.invsq_integral (lpos.trans_le ha.1) ha.2]
        ring
  have recInt : IntervalIntegrable (fun a : ℝ => 1/a) volume l r := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hlr]
    exact continuousOn_const.div continuousOn_id (fun a ha => (lpos.trans_le ha.1).ne')
  calc
    _ = ∫ a in l..r,log (h/r)*(1/a^2-(1/r)*(1/a)) := by
      apply intervalIntegral.integral_congr
      intro a ha
      rw [uIcc_of_le hlr] at ha
      exact middle a ha
    _ = _ := by
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_sub (Wu04RecoverGammaMass.invsq_integrable lpos hlr) (recInt.const_mul _),
        intervalIntegral.integral_const_mul,Wu04RecoverGammaMass.invsq_integral lpos hlr,
        integral_one_div_of_pos lpos rpos]
      ring

def massLower (i : Fin 5) : ℝ := Wu04FactorEnvelopes.lower (hi i/cut i)*
  (1/lo i-(1+Wu04FactorEnvelopes.upper (cut i/lo i))/cut i)
def gain (i : Fin 5) : ℝ := d*massLower i

theorem factors_nonneg (i : Fin 5) : 0≤Wu04FactorEnvelopes.lower (hi i/cut i) ∧
    0≤1/lo i-(1+Wu04FactorEnvelopes.upper (cut i/lo i))/cut i := by
  revert i
  simp only [lo,hi,cut,firstNode,firstS,Fin.forall_fin_succ,Fin.forall_fin_zero,
    and_true,Matrix.cons_val_zero,Matrix.cons_val_succ]
  norm_num [Wu04FactorEnvelopes.lower,Wu04FactorEnvelopes.upper,
    Wu04FactorEnvelopes.leftFactor,Wu04FactorEnvelopes.rightFactor,
    SharpLogRecurrence.lowerLog,SharpLogRecurrence.upperLog,JointLogTotalComparison.V]

theorem mass_paid (i : Fin 5) : massLower i≤
    ∫ a in lo i..cut i,∫ b in a..cut i,∫ c in cut i..hi i,W a b c := by
  have g := geometry i
  have rpos := g.2.1.trans_le g.2.2.1
  rw [selected_square_exact g.1 g.2.2.1 g.2.2.2]
  have lower := Wu04FactorEnvelopes.lower_le_log ((one_le_div rpos).mpr g.2.2.2)
  have upper := Wu04FactorEnvelopes.log_le_upper ((one_le_div g.2.1).mpr g.2.2.1)
  have fact := div_le_div_of_nonneg_right (add_le_add_right upper 1) rpos.le
  exact mul_le_mul lower (by linarith only [fact]) (factors_nonneg i).2
    ((factors_nonneg i).1.trans lower)

/-- Every original row, every original phi≥2, with the selected-square deficit paid. -/
theorem integral_paid (i : Fin 5) {φ : ℝ} (hφ : 2≤φ) :
    omega3XIntegral (firstNode i) (firstS i) φ≤
      Wu04MainTail.cap*Elementary.elementaryMomentOne 1 (lo i) (hi i)-gain i := by
  have hd := deficit_paid i hφ
  rw [deficit_identity] at hd
  have hm := mul_le_mul_of_nonneg_left (mass_paid i) d_pos.le
  unfold gain
  linarith only [hd,hm]

/-- The actual unbounded envelope, not a bounded-phi replacement. -/
theorem envelope_paid (i : Fin 5) : omega3XIntegralEnvelope (firstNode i) (firstS i)≤
    Wu04MainTail.cap*Elementary.elementaryMomentOne 1 (lo i) (hi i)-gain i := by
  apply csSup_le
  · exact ⟨omega3XIntegral (firstNode i) (firstS i) 2,mem_image_of_mem _ (show (2:ℝ)∈Ici 2 by simp)⟩
  · rintro y ⟨φ,hφ,rfl⟩
    exact integral_paid i hφ
end
end Wu04FirstMass
