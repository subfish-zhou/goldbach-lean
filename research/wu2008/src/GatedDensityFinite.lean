import GatedDensityEndpoint

namespace GatedDensityPayment
open Wu2008DoubleSieve MotherPair Real Set MeasureTheory
open FiniteEndpointPayment ActualNineFeedback NodeExtension
open scoped Interval BigOperators
noncomputable section

/-- The upper-boundary branch meeting point already forced by the gamma-eight domain. -/
def upperSwitch (p : SecondFunctionalParameters) : ℝ := p.kappa1-2

/-- The lower-boundary branch meeting point already forced by the gamma-eight domain. -/
def lowerSwitch (p : SecondFunctionalParameters) : ℝ := p.S*(1-1/p.kappa2)-1

theorem upperSwitch_boundary (p : SecondFunctionalParameters) :
    1/(upperSwitch p+2)=upperP p .gammaEight := by
  simp [upperSwitch,upperP]

theorem lowerSwitch_boundary {p : SecondFunctionalParameters} (hp : AnalyticParameters p) :
    (1-upperQ p .gammaEight)/(lowerSwitch p+1)=1/p.S := by
  have hk : 1 < p.kappa2 := by
    linarith [hp.two_lt_s,hp.mother.s_le_kappa3,hp.mother.kappa3_lt_kappa2]
  have hk0 : p.kappa2 ≠ 0 := by linarith
  have hS0 : p.S ≠ 0 := by linarith [hp.three_le_S]
  have hq : 1-1/p.kappa2 ≠ 0 := by
    have h := (div_lt_one (by linarith : 0<p.kappa2)).mpr hk
    linarith
  simp only [upperQ,lowerSwitch,sub_add_cancel]
  field_simp [hk0,hS0,hq,ne_of_gt (sub_pos.mpr hk)]

/-- Sorted original-domain branch meetings, clipped by the original cell endpoints. -/
def firstSplit (p : SecondFunctionalParameters) (a b : ℝ) : ℝ :=
  clip a b (min (upperSwitch p) (lowerSwitch p))

def secondSplit (p : SecondFunctionalParameters) (a b : ℝ) : ℝ :=
  clip a b (max (upperSwitch p) (lowerSwitch p))

theorem split_order (p : SecondFunctionalParameters) {a b : ℝ} (hab : a ≤ b) :
    a ≤ firstSplit p a b ∧ firstSplit p a b ≤ secondSplit p a b ∧ secondSplit p a b ≤ b :=
  ⟨(clip_bounds hab).1,clip_mono a b min_le_max,(clip_bounds hab).2⟩

/-- The four original labels are kept separate in every interval payment. -/
def densityEndpoint (p : SecondFunctionalParameters) (a b : ℝ) : ℝ :=
  kernelEndpoint p .gammaFive a b+kernelEndpoint p .gammaSix a b+
    kernelEndpoint p .gammaSeven a b+kernelEndpoint p .gammaEight a b

theorem densityEndpoint_le {p : SecondFunctionalParameters} (hp : AnalyticParameters p)
    {a b v : ℝ} (ha : 1 ≤ a) (hb : b ≤ 3) (hv : v ∈ Icc a b) :
    densityEndpoint p a b ≤ SecondFunctionalCoupledFeedback.density p v :=
  add_le_add (add_le_add (add_le_add (kernelEndpoint_le hp .gammaFive ha hb hv)
    (kernelEndpoint_le hp .gammaSix ha hb hv)) (kernelEndpoint_le hp .gammaSeven ha hb hv))
      (kernelEndpoint_le hp .gammaEight ha hb hv)

theorem densityEndpoint_nonneg {p : SecondFunctionalParameters} (hp : AnalyticParameters p)
    {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) (hb : b ≤ 3) :
    0 ≤ densityEndpoint p a b :=
  add_nonneg (add_nonneg (add_nonneg (kernelEndpoint_nonneg hp .gammaFive ha hab hb)
    (kernelEndpoint_nonneg hp .gammaSix ha hab hb)) (kernelEndpoint_nonneg hp .gammaSeven ha hab hb))
      (kernelEndpoint_nonneg hp .gammaEight ha hab hb)

theorem densityEndpoint_integral_le {p : SecondFunctionalParameters} (hp : AnalyticParameters p)
    {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) (hb : b ≤ 3) :
    (b-a)*densityEndpoint p a b ≤ ∫ v in a..b,SecondFunctionalCoupledFeedback.density p v := by
  have hm := intervalIntegral.integral_mono_on hab
    (intervalIntegrable_const (c := densityEndpoint p a b))
    (density_integrable p hp).intervalIntegrable (fun v hv => densityEndpoint_le hp ha hb hv)
  simpa only [intervalIntegral.integral_const,smul_eq_mul] using hm

/-- A finite full-cell bound; the two branch meetings introduce no arbitrary cut. -/
def intervalPayment (p : SecondFunctionalParameters) (a b : ℝ) : ℝ :=
  (firstSplit p a b-a)*densityEndpoint p a (firstSplit p a b)+
    (secondSplit p a b-firstSplit p a b)*densityEndpoint p (firstSplit p a b) (secondSplit p a b)+
    (b-secondSplit p a b)*densityEndpoint p (secondSplit p a b) b

theorem intervalPayment_le {p : SecondFunctionalParameters} (hp : AnalyticParameters p)
    {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) (hb : b ≤ 3) :
    intervalPayment p a b ≤ ∫ v in a..b,SecondFunctionalCoupledFeedback.density p v := by
  have ho := split_order p hab
  have h0 := densityEndpoint_integral_le hp ha ho.1 (ho.2.1.trans (ho.2.2.trans hb))
  have h1 := densityEndpoint_integral_le hp (ha.trans ho.1) ho.2.1 (ho.2.2.trans hb)
  have h2 := densityEndpoint_integral_le hp (ha.trans (ho.1.trans ho.2.1)) ho.2.2 hb
  have hi := density_integrable p hp
  have he0 := intervalIntegral.integral_add_adjacent_intervals
    (a := a) (b := firstSplit p a b) (c := secondSplit p a b)
    hi.intervalIntegrable hi.intervalIntegrable
  have he1 := intervalIntegral.integral_add_adjacent_intervals
    (a := a) (b := secondSplit p a b) (c := b) hi.intervalIntegrable hi.intervalIntegrable
  unfold intervalPayment
  exact (add_le_add (add_le_add h0 h1) h2).trans_eq (by rw [he0,he1])

/-- A genuinely finite expression, with all original cells and four gated kernels retained. -/
def densityFinite (p : SecondFunctionalParameters) (z : Fin 9 → ℝ) : ℝ :=
  ∑ k : Fin 9,z k*intervalPayment p (left 1 3 k) (right 1 3 k)

theorem densityFinite_le {p : SecondFunctionalParameters} (hp : AnalyticParameters p)
    (z : Fin 9 → ℝ) (hz : ∀ k,0 ≤ z k) : densityFinite p z ≤ densityMoment p z := by
  rw [densityMoment,integral_cells z (by norm_num) (by norm_num) le_rfl (density_profile_integrable p hp z)]
  apply Finset.sum_le_sum
  intro k _
  exact mul_le_mul_of_nonneg_left
    (intervalPayment_le hp (clip_bounds (by norm_num : (1:ℝ) ≤ 3)).1
      (cell_order 1 3 k) (clip_bounds (by norm_num : (1:ℝ) ≤ 3)).2) (hz k)

/-- The original H, and the original four coupledRow objects, not replacement rows. -/
theorem original_four_densityFinite_le (i : Fin 4) :
    densityFinite (coupledRow i) NineFeedbackStrength.originalH ≤
      densityMoment (coupledRow i) NineFeedbackStrength.originalH :=
  densityFinite_le (coupledRow_geometry i).1 _ CoupledIntegralRecovery.originalH_nonneg

end
end GatedDensityPayment
