import SrcFourRoot
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.IntervalIntegral.TrapezoidalRule

noncomputable section
open Real Set MeasureTheory Wu2008DoubleSieve FourRoughClosedMass
open Wu08OriginalFourWeights

namespace WuSource.SrcFourEnclosure

def clamp (x : ℝ) : ℝ := min beta (max alpha x)
def cross (z : ℝ) : ℝ := log (lam-z)-log z
def density (z : ℝ) : ℝ := cross (clamp z)/clamp z
def G (y : ℝ) : ℝ := ∫ z in y..beta, density z
def H (x : ℝ) : ℝ := ∫ y in x..beta, G y/(clamp y)^2
def outerMass (x : ℝ) : ℝ := H x/clamp x
def mass : ℝ := original outerMass

theorem geometry :
    0 < alpha ∧ alpha ≤ beta ∧ beta < 1 ∧ beta < lam ∧
      2*beta ≤ lam ∧ alpha ≤ (1/10 : ℝ) ∧ (1/10 : ℝ) ≤ beta := by
  norm_num [alpha,beta,lam,truncatedSixthLowerAlpha,truncatedSixthLowerBeta,
    truncatedSixthLowerLambda]

theorem clamp_mem (x : ℝ) : clamp x ∈ Icc alpha beta :=
  ⟨le_min geometry.2.1 (le_max_left _ _),min_le_left _ _⟩

theorem clamp_eq {x : ℝ} (hx : x ∈ Icc alpha beta) : clamp x = x := by
  simp only [clamp,max_eq_right hx.1,min_eq_right hx.2]

theorem clamp_pos (x : ℝ) : 0 < clamp x := geometry.1.trans_le (clamp_mem x).1

theorem clamp_continuous : Continuous clamp := by unfold clamp; fun_prop

theorem density_continuous : Continuous density := by
  have hz (z : ℝ) : lam-clamp z ≠ 0 := by
    have := (clamp_mem z).2
    linarith only [this,geometry.2.2.2.1]
  exact ((continuous_const.sub clamp_continuous).log hz |>.sub
    (clamp_continuous.log (fun z => (clamp_pos z).ne'))).div clamp_continuous
      (fun z => (clamp_pos z).ne')

theorem density_eq {z : ℝ} (hz : z ∈ Icc alpha beta) :
    density z = cross z/z := by rw [density,clamp_eq hz]

theorem G_derivative (y : ℝ) : HasDerivAt G (-density y) y := by
  exact intervalIntegral.integral_hasDerivAt_left
    (density_continuous.intervalIntegrable (μ := volume) y beta)
    density_continuous.stronglyMeasurable.stronglyMeasurableAtFilter
    density_continuous.continuousAt

theorem G_continuous : Continuous G :=
  continuous_iff_continuousAt.mpr (fun y => (G_derivative y).continuousAt)

theorem H_integrand_continuous : Continuous (fun y => G y/(clamp y)^2) :=
  G_continuous.div (clamp_continuous.pow 2) (fun y => pow_ne_zero _ (clamp_pos y).ne')

theorem H_derivative (x : ℝ) : HasDerivAt H (-(G x/(clamp x)^2)) x :=
  intervalIntegral.integral_hasDerivAt_left
    (H_integrand_continuous.intervalIntegrable (μ := volume) x beta)
    H_integrand_continuous.stronglyMeasurable.stronglyMeasurableAtFilter
    H_integrand_continuous.continuousAt

theorem H_continuous : Continuous H :=
  continuous_iff_continuousAt.mpr (fun x => (H_derivative x).continuousAt)

theorem outerMass_continuous : Continuous outerMass :=
  H_continuous.div clamp_continuous (fun x => (clamp_pos x).ne')

theorem cross_nonneg {z : ℝ} (hz : z ∈ Icc alpha beta) : 0 ≤ cross z := by
  have hz0 := geometry.1.trans_le hz.1
  exact sub_nonneg.mpr (log_le_log hz0 (by linarith only [hz.2,geometry.2.2.2.2.1]))

theorem density_nonneg (z : ℝ) : 0 ≤ density z :=
  div_nonneg (cross_nonneg (clamp_mem z)) (clamp_pos z).le

theorem G_nonneg {y : ℝ} (hy : y ≤ beta) : 0 ≤ G y :=
  intervalIntegral.integral_nonneg_of_forall hy density_nonneg

theorem H_nonneg {x : ℝ} (hx : x ≤ beta) : 0 ≤ H x :=
  intervalIntegral.integral_nonneg hx (fun y hy =>
    div_nonneg (G_nonneg hy.2) (sq_nonneg _))

theorem outerMass_nonneg {x : ℝ} (hx : x ≤ beta) : 0 ≤ outerMass x :=
  div_nonneg (H_nonneg hx) (clamp_pos x).le

theorem mass_nonneg : 0 ≤ mass := by
  unfold mass original
  have hs : 0 ≤ ∫ x in alpha..(1/10 : ℝ), outerMass x/(1-x) :=
    intervalIntegral.integral_nonneg geometry.2.2.2.2.2.1 (fun x hx =>
      div_nonneg (outerMass_nonneg (hx.2.trans geometry.2.2.2.2.2.2))
        (by linarith only [hx.2]))
  have hl : 0 ≤ ∫ x in (1/10 : ℝ)..beta, outerMass x :=
    intervalIntegral.integral_nonneg geometry.2.2.2.2.2.2
      (fun x hx => outerMass_nonneg hx.2)
  positivity

theorem merged_kernel_bounds {l u x y z t : ℝ}
    (hl : ∀ v : ℝ, (3 : ℝ) ≤ v → l ≤ LiLiuPrereqBuchstab.buchstab v)
    (hu : ∀ v : ℝ, (3 : ℝ) ≤ v → LiLiuPrereqBuchstab.buchstab v ≤ u)
    (hx : alpha ≤ x) (hxy : x ≤ y) (hyz : y ≤ z) (hz : z ≤ beta)
    (ht : t ∈ Icc z (lam-z)) :
    l/(x*y^2*z*t) ≤ regularKernel x y z t ∧
      regularKernel x y z t ≤ u/(x*y^2*z*t) := by
  have hat := hx.trans (hxy.trans (hyz.trans ht.1))
  have hp : (3 : ℝ) ≤ parameter x y z t := by
    have hy0 := geometry.1.trans_le (hx.trans hxy)
    rw [parameter,le_div_iff₀ hy0]
    have hb : 5*beta+lam ≤ 1 := by
      norm_num [beta,lam,truncatedSixthLowerAlpha,truncatedSixthLowerBeta,
        truncatedSixthLowerLambda]
    linarith only [hxy,hyz,hz,ht.2,hb]
  have ha := geometry.1
  have hx0 := ha.trans_le hx
  have hy0 := hx0.trans_le hxy
  have hz0 := hy0.trans_le hyz
  have ht0 := hz0.trans_le ht.1
  simp only [regularKernel,clip,max_eq_right hx,max_eq_right (hx.trans hxy),
    max_eq_right (hx.trans (hxy.trans hyz)),max_eq_right hat,
    max_eq_right (show (2 : ℝ) ≤ parameter x y z t by linarith only [hp])]
  exact ⟨div_le_div_of_nonneg_right (hl _ hp) (by positivity),
    div_le_div_of_nonneg_right (hu _ hp) (by positivity)⟩

theorem merged_parameter {x y z t : ℝ}
    (hx : alpha ≤ x) (hxy : x ≤ y) (hyz : y ≤ z) (hz : z ≤ beta)
    (ht : t ≤ lam-z) : (3 : ℝ) ≤ parameter x y z t := by
  have hy0 := geometry.1.trans_le (hx.trans hxy)
  rw [parameter,le_div_iff₀ hy0]
  have hb : 5*beta+lam ≤ 1 := by
    norm_num [beta,lam,truncatedSixthLowerAlpha,truncatedSixthLowerBeta,
      truncatedSixthLowerLambda]
  linarith only [hxy,hyz,hz,ht,hb]

#check @G_derivative
#check @H_derivative
#check @mass_nonneg
#check @merged_parameter
#print axioms mass_nonneg
#print axioms merged_parameter
end WuSource.SrcFourEnclosure
