import MathlibNt.Wu2008DoubleSieve.NaturalSplitLowFTC
import MathlibNt.Wu2008DoubleSieve.NaturalSplitHighFTC

namespace Wu2008DoubleSieve.NaturalSplitActual
open Real Set MeasureTheory FixedCoefficientUpperEnclosure NaturalSplitDensity
open RetainedSixthDensity (lam moving_geometry tail_zero)
open scoped Interval

noncomputable def moving (x : ℝ) : ℝ :=
  NaturalSplitHighFTC.moving x+NaturalSplitLowFTC.moving x
noncomputable def newSixth : ℝ :=
  NaturalSplitHighFTC.rationalPart+NaturalSplitLowFTC.rationalPart

theorem regular_continuous :
    Continuous (fun v : ℝ × ℝ => truncatedSixthZeroDeltaRegular 0 (v.1,v.2)) :=
  truncatedSixthZeroDelta_regular_continuous.comp (f := fun v : ℝ × ℝ => (0,v)) (by fun_prop)

theorem actual_split {x : ℝ} (hx : x ∈ Icc a b) :
    (∫ y in b..s, truncatedSixthZeroDeltaRegular 0 (x,y)) =
    (∫ y in b..cut x, truncatedSixthZeroDeltaRegular 0 (x,y))+
    (∫ y in cut x..lam-x, truncatedSixthZeroDeltaRegular 0 (x,y)) := by
  have hc := regular_continuous.comp (f := fun y : ℝ => (x,y)) (by fun_prop)
  have hz : (∫ y in (lam-x)..s, truncatedSixthZeroDeltaRegular 0 (x,y)) = 0 := by
    calc
      _ = ∫ _y in (lam-x)..s, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro y hy
        exact tail_zero hx (uIcc_of_le (moving_geometry hx).2 ▸ hy)
      _ = 0 := by simp
  have htail := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hc.intervalIntegrable b (lam-x)) (hc.intervalIntegrable (lam-x) s)
  have hsplit := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hc.intervalIntegrable b (cut x)) (hc.intervalIntegrable (cut x) (lam-x))
  simp only [Function.comp_apply] at htail hsplit
  rw [hz,add_zero] at htail
  exact htail.symm.trans hsplit.symm

theorem slice_upper {x : ℝ} (hx : x ∈ Icc a b) :
    (∫ y in b..s, truncatedSixthZeroDeltaRegular 0 (x,y)) ≤ moving x := by
  have hc := regular_continuous.comp (f := fun y : ℝ => (x,y)) (by fun_prop)
  have hg := cut_geometry hx
  have hhigh := intervalIntegral.integral_mono_on (μ := volume) hg.1
    (hc.intervalIntegrable b (cut x))
    ((NaturalSplitHighFTC.polynomial_continuous.comp (f := fun y : ℝ => (x,y))
      (by fun_prop)).intervalIntegrable b (cut x))
    (fun y hy => high_upper hx hy)
  have hlow := intervalIntegral.integral_mono_on (μ := volume) hg.2
    (hc.intervalIntegrable (cut x) (lam-x))
    ((NaturalSplitLowFTC.polynomial_continuous.comp (f := fun y : ℝ => (x,y))
      (by fun_prop)).intervalIntegrable (cut x) (lam-x))
    (fun y hy => low_upper hx hy)
  simp only [Function.comp_apply] at hhigh hlow
  rw [NaturalSplitHighFTC.inner_ftc] at hhigh
  rw [NaturalSplitLowFTC.inner_ftc] at hlow
  rw [actual_split hx]
  exact add_le_add hhigh hlow

theorem moving_continuous : Continuous moving :=
  NaturalSplitHighFTC.moving_continuous.add NaturalSplitLowFTC.moving_continuous

theorem polynomial_integral : 4*(∫ x in a..b, moving x) = newSixth := by
  unfold moving newSixth
  rw [intervalIntegral.integral_add
    (NaturalSplitHighFTC.moving_continuous.intervalIntegrable a b)
    (NaturalSplitLowFTC.moving_continuous.intervalIntegrable a b),mul_add,
    NaturalSplitHighFTC.polynomial_integral,NaturalSplitLowFTC.polynomial_integral]

theorem actual_sixth_upper : truncatedSixthLowerF6lin ≤ newSixth := by
  have hi : Continuous (fun x : ℝ => ∫ y in b..s, truncatedSixthZeroDeltaRegular 0 (x,y)) := by
    apply gamma5Gain_moving_integral
      (f := fun x y : ℝ => truncatedSixthZeroDeltaRegular 0 (x,y)) regular_continuous <;> fun_prop
  have hmono := intervalIntegral.integral_mono_on (μ := volume)
    truncatedSixthLower_parameters.2.1.le
    (hi.intervalIntegrable a b) (moving_continuous.intervalIntegrable a b)
    (fun x hx => slice_upper hx)
  have he := truncatedSixthZeroDelta_extension_eq (by norm_num : (0 : ℝ) ≤ 0)
  change (4*∫ x in a..b, ∫ y in b..s, truncatedSixthZeroDeltaRegular 0 (x,y)) =
    truncatedSixthLowerF6lin at he
  have hf := polynomial_integral
  linarith

noncomputable def exactSixth : ℝ :=
  14195634170987930770085604909336115142970060629557233283705544909/
  3434673431296849357165490043023985995514180840660970560000000000
noncomputable def exactGain : ℝ :=
  14608359578464400173268994771708418258704973637524668704803698803/
  30912060881671644214489410387215873959627627565948735040000000000

theorem sixth_exact : newSixth = exactSixth := by
  norm_num [newSixth,NaturalSplitHighFTC.rationalPart,NaturalSplitLowFTC.rationalPart,exactSixth]

theorem exact_improvement : newSixth+exactGain = RefinedRetainedFTC.rationalSixth := by
  rw [sixth_exact]
  norm_num [exactSixth,exactGain,RefinedRetainedFTC.rationalSixth]

theorem gain_positive : 0 < exactGain := by norm_num [exactGain]

theorem strict_improvement : newSixth < RefinedRetainedFTC.rationalSixth := by
  have h := exact_improvement
  have hp := gain_positive
  linarith

theorem actual_exact_upper : truncatedSixthLowerF6lin ≤ exactSixth := by
  rw [← sixth_exact]
  exact actual_sixth_upper

end Wu2008DoubleSieve.NaturalSplitActual
