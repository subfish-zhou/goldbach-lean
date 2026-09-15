import WE10FourMajorOuter

noncomputable section
open Real Set MeasureTheory Wu2008DoubleSieve Wu08OriginalFourWeights
open FourRoughClosedMass WuTarget.W13

namespace WuTarget.E10FourMajor

def momentTerm (i : Fin 5) : ℝ :=
  coefA i*moment (i.val+2)+coefB i*moment (i.val+3)

theorem profileTerm_integrable (i : Fin 5) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (profileTerm i) volume a b :=
  ((tail_continuousOn (i.val+2) ha hab).intervalIntegrable.const_mul (coefA i)).add
    ((tail_continuousOn (i.val+3) ha hab).intervalIntegrable.const_mul (coefB i))

theorem profile_integrable {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable profile volume a b :=
  IntervalIntegrable.sum Finset.univ (fun i _ => profileTerm_integrable i ha hab)

theorem weighted_profileTerm_integrable (i : Fin 5) :
    IntervalIntegrable (fun x => profileTerm i x/(1-x)) volume alpha cut := by
  convert ((weighted_tail_integrable (i.val+2)).const_mul (coefA i)).add
    ((weighted_tail_integrable (i.val+3)).const_mul (coefB i)) using 1
  funext x
  unfold profileTerm
  ring

theorem weighted_profile_integrable :
    IntervalIntegrable (fun x => profile x/(1-x)) volume alpha cut := by
  have he : (fun x => profile x/(1-x)) =
      (fun x => ∑ i : Fin 5, profileTerm i x/(1-x)) := by
    funext x
    simp only [profile,Finset.sum_div]
  rw [he]
  exact IntervalIntegrable.sum Finset.univ (fun i _ => weighted_profileTerm_integrable i)

theorem profile_integral {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ x in a..b, profile x) =
      ∑ i : Fin 5, (coefA i*(∫ x in a..b, tail (i.val+2) x)+
        coefB i*(∫ x in a..b, tail (i.val+3) x)) := by
  unfold profile
  rw [intervalIntegral.integral_finsetSum (fun i _ => profileTerm_integrable i ha hab)]
  apply Finset.sum_congr rfl
  intro i _
  unfold profileTerm
  rw [intervalIntegral.integral_add
    ((tail_continuousOn (i.val+2) ha hab).intervalIntegrable.const_mul (coefA i))
    ((tail_continuousOn (i.val+3) ha hab).intervalIntegrable.const_mul (coefB i))]
  simp only [intervalIntegral.integral_const_mul]

theorem weighted_profile_integral :
    (∫ x in alpha..cut, profile x/(1-x)) =
      ∑ i : Fin 5, (coefA i*(∫ x in alpha..cut, tail (i.val+2) x/(1-x))+
        coefB i*(∫ x in alpha..cut, tail (i.val+3) x/(1-x))) := by
  have he : (fun x => profile x/(1-x)) =
      (fun x => ∑ i : Fin 5, profileTerm i x/(1-x)) := by
    funext x
    simp only [profile,Finset.sum_div]
  rw [he,intervalIntegral.integral_finsetSum (fun i _ => weighted_profileTerm_integrable i)]
  apply Finset.sum_congr rfl
  intro i _
  have hi : (fun x => profileTerm i x/(1-x)) =
      (fun x => coefA i*(tail (i.val+2) x/(1-x))+
        coefB i*(tail (i.val+3) x/(1-x))) := by
    funext x
    unfold profileTerm
    ring
  rw [hi,intervalIntegral.integral_add
    ((weighted_tail_integrable (i.val+2)).const_mul (coefA i))
    ((weighted_tail_integrable (i.val+3)).const_mul (coefB i))]
  simp only [intervalIntegral.integral_const_mul]

theorem weighted_amount_identity :
    (36/5)*(∫ x in alpha..cut, profile x/(1-x))+
      8*(∫ x in cut..beta, profile x) = ∑ i : Fin 5, momentTerm i := by
  rw [weighted_profile_integral,
    profile_integral (geometry.1.trans_le geometry.2.1) geometry.2.2.1,
    Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  unfold momentTerm moment
  ring

theorem original_pair_le_moments :
    original10+original11 ≤ ∑ i : Fin 5, momentTerm i := by
  have hs10 := weighted_integrable regularOuter10_continuous
  have hs11 := weighted_integrable regularOuter11_continuous
  change IntervalIntegrable (fun x => regularOuter10 x/(1-x)) volume alpha cut at hs10
  change IntervalIntegrable (fun x => regularOuter11 x/(1-x)) volume alpha cut at hs11
  have hl10 := regularOuter10_continuous.intervalIntegrable (μ := volume) cut beta
  have hl11 := regularOuter11_continuous.intervalIntegrable (μ := volume) cut beta
  have hs := intervalIntegral.integral_mono_on geometry.2.1
    (hs10.add hs11) weighted_profile_integrable (fun x hx => by
      have hden : 0 ≤ 1-x := by linarith only [hx.2,geometry.2.2.2]
      simpa only [add_div] using div_le_div_of_nonneg_right
        (outer_pair_upper ⟨hx.1,hx.2.trans geometry.2.2.1⟩) hden)
  have hl := intervalIntegral.integral_mono_on geometry.2.2.1
    (hl10.add hl11)
    (profile_integrable (geometry.1.trans_le geometry.2.1) geometry.2.2.1)
    (fun x hx => outer_pair_upper ⟨geometry.2.1.trans hx.1,hx.2⟩)
  rw [intervalIntegral.integral_add hs10 hs11] at hs
  rw [intervalIntegral.integral_add hl10 hl11] at hl
  rw [← weighted_amount_identity]
  unfold original10 original11 original
  dsimp only [cut] at hs hl ⊢
  linarith only [hs,hl]

theorem momentTerm_upper (i : Fin 5) : momentTerm i ≤ capTerm i := by
  have ha := mul_le_mul_of_nonneg_left (W13Tight.moment_upper (i.val+2))
    (coefficients_pos i).1.le
  have hb := mul_le_mul_of_nonneg_left (W13Tight.moment_upper (i.val+3))
    (coefficients_pos i).2.le
  have h := add_le_add ha hb
  change momentTerm i ≤ _ at h
  convert h using 1
  unfold capTerm coefA coefB
  ring

theorem original_pair_upper : original10+original11 ≤ pairCap :=
  original_pair_le_moments.trans (Finset.sum_le_sum (fun i _ => momentTerm_upper i))

theorem original_pair_lt_target : original10+original11 < (7/10 : ℝ) :=
  original_pair_upper.trans_lt pairCap_lt_target

theorem original_pair_target : original10+original11 ≤ (7/10 : ℝ) :=
  original_pair_lt_target.le

end WuTarget.E10FourMajor
