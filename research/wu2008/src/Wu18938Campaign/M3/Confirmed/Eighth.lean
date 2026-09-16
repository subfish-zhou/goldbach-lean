import Wu18938Campaign.M3.Confirmed.SeventhNinth

noncomputable section

namespace Wu18938Campaign.M3.Confirmed.Eighth

open Real Set MeasureTheory Finset Wu2008DoubleSieve LogMoments Wu08TerminalAlignment

def a : ℝ := truncatedSixthLowerAlpha
def top : ℝ := coordinate (1/3) 1 a
def middle : ℝ := coordinate (1/3) 1 (1/10)

def polyPrimitive (n : ℕ) (b z : ℝ) : ℝ :=
  2*(∑ i ∈ range n, z^(2*i+2)/((2*i+1:ℝ)*(2*i+2:ℝ)))+
    2*z^(2*n+2)/((1-b^2)*(2*n+2:ℝ))

theorem poly_derivative (n : ℕ) (b z : ℝ) :
    HasDerivAt (polyPrimitive n b) (polynomial n b z) z := by
  have h := ((HasDerivAt.fun_sum fun i (_ : i ∈ range n) =>
    ((hasDerivAt_id z).pow (2*i+2)).div_const ((2*i+1:ℝ)*(2*i+2:ℝ))).const_mul 2).add
    ((((hasDerivAt_id z).pow (2*n+2)).const_mul 2).div_const ((1-b^2)*(2*n+2:ℝ)))
  convert! h using 1
  simp only [polynomial]
  have hs : (∑ i ∈ range n, (2*↑i+2)*z^(2*i+2-1)*1/((2*↑i+1)*(2*↑i+2))) =
      ∑ i ∈ range n, z^(2*i+1)/(2*i+1:ℝ) := by
    apply sum_congr rfl
    intro i _
    norm_num only [show 2*i+2-1=2*i+1 by omega]
    field_simp
  push_cast
  simp only [id_eq]
  norm_num only [show ∀ i : ℕ, 2*i+2-1=2*i+1 by omega] at hs
  rw [hs]
  field_simp

theorem kernel_identity {t : ℝ} (ht : t < 1) :
    transformedKernel (1/3) 1 t = log (2-3*t)/(t*(1-t)) := by
  have hn : 1-t ≠ 0 := by linarith
  unfold transformedKernel coordinate
  simp only [one_mul]
  congr 2
  have hd : (1:ℝ)-(1/3-t)/(1-t) = (2/3)/(1-t) := by
    field_simp
    ring
  rw [hd]
  field_simp [hn]
  ring

def smallCap : ℝ :=
  (9/10)*endpointBound 10 (1/3) top middle top
    (logUpper 24 (((1/3)-middle)/((1/3)-top)))+
    (27/20)*(polyPrimitive 10 top top-polyPrimitive 10 top middle)

def largeCap : ℝ :=
  endpointBound 10 (1/3) middle 0 middle
    (logUpper 24 ((1/3)/((1/3)-middle)))

theorem small_integral_upper :
    U8CanonicalMother.I ≤ smallCap := by
  have ha : a ≤ (1/10:ℝ) := by norm_num [a,truncatedSixthLowerAlpha]
  have hg (t : ℝ) (ht : t ∈ Icc a (1/10)) :
      0 < t ∧ t < 1 ∧ 0 ≤ coordinate (1/3) 1 t ∧
        coordinate (1/3) 1 t ≤ top ∧ coordinate (1/3) 1 t < 1/3 := by
    have ht0 : 0 < t := (by norm_num [a,truncatedSixthLowerAlpha] : (0:ℝ) < a).trans_le ht.1
    have ht1 : t < 1 := by linarith [ht.2]
    exact ⟨ht0,ht1,(by norm_num [coordinate] : (0:ℝ) ≤ coordinate (1/3) 1 (1/10)).trans
      (coordinate_antitone (by norm_num) ht.2 (by norm_num)),
      coordinate_antitone (by norm_num) ht.1 ht1,coordinate_lt (by norm_num) ht0 ht1⟩
  have hc : ContinuousOn (coordinate (1/3) 1) (Icc a (1/10)) := by
    intro t ht
    exact (coordinate_derivative (hg t ht).2.1).continuousAt.continuousWithinAt
  have hpi : IntervalIntegrable
      (fun t => (9/10)*polynomial 10 top (coordinate (1/3) 1 t)/(t*(1-t)^2))
        volume a (1/10) := by
    apply ContinuousOn.intervalIntegrable_of_Icc ha
    apply ContinuousOn.div
    · exact continuousOn_const.mul
        ((by unfold polynomial; fun_prop : Continuous (polynomial 10 top)).comp_continuousOn hc)
    · fun_prop
    · intro t ht
      exact mul_ne_zero (hg t ht).1.ne' (pow_ne_zero 2 (by linarith [(hg t ht).2.1]))
  have hd (t : ℝ) (ht : t ∈ uIcc a (1/10)) :
      HasDerivAt (fun t =>
        -((9/10)*primitive 10 (1/3) top (coordinate (1/3) 1 t)+
          (27/20)*polyPrimitive 10 top (coordinate (1/3) 1 t)))
      ((9/10)*polynomial 10 top (coordinate (1/3) 1 t)/(t*(1-t)^2)) t := by
    rw [uIcc_of_le ha] at ht
    have ht' := hg t ht
    have h := ((((primitive_derivative 10 (b := top) ht'.2.2.2.2).const_mul (9/10)).add
      ((poly_derivative 10 top (coordinate (1/3) 1 t)).const_mul (27/20))).comp t
        (coordinate_derivative ht'.2.1)).neg
    convert! h using 1
    have he : (1/3:ℝ)-coordinate (1/3) 1 t = (2/3)*t/(1-t) := by
      unfold coordinate
      field_simp [show 1-t ≠ 0 by linarith [ht'.2.1]]
      ring
    rw [he]
    field_simp [ht'.1.ne', show 1-t ≠ 0 by linarith [ht'.2.1]]
    ring
  have hi : IntervalIntegrable (fun t : ℝ => (9/10)*log (2-3*t)/(t*(1-t)^2))
      volume a (1/10) := by
    convert OriginalU8.SymbolicSmallGain.weighted_integrable.const_mul (9/10) using 1
    · ext t
      ring
    · rfl
    · rfl
  have hp (t : ℝ) (ht : t ∈ Icc a (1/10)) :
      (9/10)*log (2-3*t)/(t*(1-t)^2) ≤
        (9/10)*polynomial 10 top (coordinate (1/3) 1 t)/(t*(1-t)^2) := by
    have hh := polynomial_upper 10 (hg t ht).2.2.1 (hg t ht).2.2.2.1
      (by norm_num [top,coordinate,a,truncatedSixthLowerAlpha])
    have he : log ((1+coordinate (1/3) 1 t)/(1-coordinate (1/3) 1 t)) = log (2-3*t) := by
      have h := kernel_identity (hg t ht).2.1
      unfold transformedKernel at h
      exact (div_left_inj' (mul_ne_zero (hg t ht).1.ne'
        (by linarith [(hg t ht).2.1]))).mp h
    rw [he] at hh
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hh (by norm_num))
      (mul_pos (hg t ht).1 (sq_pos_of_pos (by linarith [(hg t ht).2.1]))).le
  have hm := intervalIntegral.integral_mono_on ha hi hpi hp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hpi] at hm
  have heI : U8CanonicalMother.I =
      ∫ t in a..(1/10:ℝ), (9/10)*log (2-3*t)/(t*(1-t)^2) := by
    rw [U8CanonicalMother.I_literal, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t _
    ring
  rw [← heI] at hm
  have he := endpoint_bound 10 (d := (1/3:ℝ)) (b := top) (l := middle) (r := top)
    (by norm_num) (by norm_num [top,coordinate,a,truncatedSixthLowerAlpha])
    (by norm_num [top,coordinate,a,truncatedSixthLowerAlpha])
    (by norm_num [middle,coordinate]) (by norm_num [top,coordinate,a,truncatedSixthLowerAlpha])
    (log_upper (by norm_num [middle,top,coordinate,a,truncatedSixthLowerAlpha]) 24)
  change _ ≤ -((9/10)*primitive 10 (1/3) top middle+(27/20)*polyPrimitive 10 top middle)-
    -((9/10)*primitive 10 (1/3) top top+(27/20)*polyPrimitive 10 top top) at hm
  unfold smallCap
  linarith only [hm,he]

theorem large_integral_upper : U8MotherInsertion.largeIntegral ≤ largeCap := by
  have h := transformed_integral_upper 10 (d := (1/3:ℝ)) (e := 1)
    (l := (1/10:ℝ)) (r := (1/3:ℝ)) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num [coordinate]) (by norm_num [coordinate])
  have he : (∫ t in (1/10:ℝ)..(1/3), transformedKernel (1/3) 1 t) =
      U8MotherInsertion.largeIntegral := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le (by norm_num : (1/10:ℝ) ≤ 1/3)] at ht
    exact kernel_identity (by linarith [ht.2])
  rw [he, show coordinate (1/3) 1 (1/3) = 0 by norm_num [coordinate]] at h
  apply h.trans
  apply endpoint_bound 10 (by norm_num) (by norm_num [middle,coordinate])
    (by norm_num [middle,coordinate]) (by norm_num) (by norm_num [middle,coordinate])
  change log (((1/3:ℝ)-0)/((1/3)-middle)) ≤ logUpper 24 ((1/3)/((1/3)-middle))
  rw [sub_zero]
  exact log_upper (by norm_num [middle,coordinate] : (1:ℝ) ≤ (1/3)/((1/3)-middle)) 24

theorem eighth_main_upper : eighthMain ≤ (5279581/1000000:ℝ) := by
  have hs := small_integral_upper
  have hl := large_integral_upper
  have hc : 8*(smallCap+largeCap) ≤ (5279581/1000000:ℝ) := by
    norm_num [smallCap,largeCap,endpointBound,momentBound,logUpper,polyPrimitive,
      top,middle,coordinate,a,truncatedSixthLowerAlpha,Finset.sum_range_succ]
  unfold eighthMain
  rw [U8MotherInsertion.J8_split]
  change 8*(U8CanonicalMother.L+U8MotherInsertion.largeIntegral)-
    8*(U8CanonicalMother.L-U8CanonicalMother.I) ≤ _
  linarith only [hs,hl,hc]

end Wu18938Campaign.M3.Confirmed.Eighth
