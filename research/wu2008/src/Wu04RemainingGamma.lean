import Wu04RemainingLower

namespace Wu04RemainingGamma
open Wu2008DoubleSieve Set MeasureTheory Wu04RemainingCore Wu04MainTail
open SecondFunctionalGeometricMass
noncomputable section

/-- A common original-endpoint gate; h is the original Gamma9 upper endpoint. -/
theorem kernel_paid {φ h a b c : ℝ} (hφ : 2≤φ)
    (hg : (3+1/cap)*h≤2) (ha : 0<a) (hb : 0<b) (hc : 0<c)
    (hah : a≤h) (hbh : b≤h) (hch : c≤h) :
    omega3XIntegralKernel φ a b c≤cap*((1:ℝ)/(a*b^2*c)) := by
  have cp : 0<cap := by norm_num [cap]
  have hb' := mul_le_mul_of_nonneg_left hbh (show 0≤1+1/cap by positivity)
  have gate : a+(1+1/cap)*b+c≤2 := by nlinarith only [hg,hah,hb',hch]
  have arg : 1/cap≤(φ-a-b-c)/b := by
    apply (le_div_iff₀ hb).mpr
    linarith only [gate,hφ]
  have hu : 1≤cap*((φ-a-b-c)/b) := by
    have hm := mul_le_mul_of_nonneg_left arg cp.le
    rwa [mul_one_div_cancel cp.ne'] at hm
  have paid := div_le_div_of_nonneg_right (buchstab_le hu)
    (show 0≤a*b^2*c by positivity)
  simpa only [omega3XIntegralKernel,mul_one_div] using paid

/-- Gamma9 is integrated and bounded on its own full domain, for its own phi. -/
theorem integral_paid {lo hi φ : ℝ} (hl : (1:ℝ)/10≤lo) (hlh : lo≤hi)
    (hg : (3+1/cap)*hi≤2) (hφ : 2≤φ) :
    (∫ a in lo..hi, ∫ b in a..hi, ∫ c in b..hi,omega3XIntegralKernel φ a b c)≤
    cap*Elementary.elementaryMomentOne 1 lo hi := by
  have hp : 0<lo := lt_of_lt_of_le (by norm_num) hl
  have point (a b c : ℝ) (ha : a∈Icc lo hi) (hb : b∈Icc a hi) (hc : c∈Icc b hi) :=
    kernel_paid hφ hg (hp.trans_le ha.1) ((hp.trans_le ha.1).trans_le hb.1)
      (((hp.trans_le ha.1).trans_le hb.1).trans_le hc.1) ha.2 hb.2 hc.2
  have inner (a b : ℝ) (ha : a∈Icc lo hi) (hb : b∈Icc a hi) :
      (∫ c in b..hi,omega3XIntegralKernel φ a b c)≤
      cap*(∫ c in b..hi,(1:ℝ)/(a*b^2*c)) := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_mono_on hb.2
      (omega3XIntegralKernel_intervalIntegrable (hl.trans ha.1) ((hl.trans ha.1).trans hb.1) hb.2)
      ((Omega3ElementaryRegularity.kernel_integrable (hl.trans ha.1)
        ((hl.trans ha.1).trans hb.1) hb.2).const_mul cap) (fun c hc => point a b c ha hb hc)
  have middle (a : ℝ) (ha : a∈Icc lo hi) :
      (∫ b in a..hi,∫ c in b..hi,omega3XIntegralKernel φ a b c)≤
      cap*(∫ b in a..hi,∫ c in b..hi,(1:ℝ)/(a*b^2*c)) := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_mono_on ha.2
      (omega3XIntegral_inner_intervalIntegrable (hl.trans ha.1) ha.2)
      ((Omega3ElementaryRegularity.inner_integrable (hl.trans ha.1) ha.2).const_mul cap)
      (fun b hb => inner a b ha hb)
  rw [← Omega3ElementaryMass.nested_eq_elementary hp hlh,← intervalIntegral.integral_const_mul]
  exact intervalIntegral.integral_mono_on hlh
    (omega3XIntegral_middle_intervalIntegrable hl hlh)
    ((Omega3ElementaryRegularity.middle_integrable hl hlh).const_mul cap) middle

theorem original_gates (i : Fin 3) :
    (1:ℝ)/10≤1/(row i).kappa1 ∧ 1/(row i).kappa1≤1/(row i).kappa3 ∧
    (3+1/cap)*(1/(row i).kappa3)≤2 := by
  revert i
  simp only [row,ActualNineFeedback.coupledRow,SecondFunctionalPositive.parameters,
    Fin.forall_fin_succ,Fin.forall_fin_zero,and_true,Matrix.cons_val_zero,Matrix.cons_val_succ]
  norm_num [SecondFunctionalParameters.row2,SecondFunctionalParameters.row3,SecondFunctionalParameters.row4,cap]

theorem remaining_omega (i : Fin 3) {φ : ℝ} (hφ : 2≤φ) :
    omega3XIntegral (row i).kappa3 (row i).kappa1 φ≤
    cap*Elementary.elementaryMomentOne 1 (1/(row i).kappa1) (1/(row i).kappa3) := by
  obtain ⟨hl,hh,hg⟩ := original_gates i
  exact integral_paid hl hh hg hφ

end
end Wu04RemainingGamma
