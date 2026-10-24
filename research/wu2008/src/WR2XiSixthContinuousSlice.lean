import WR2XiSixthContinuousGeometry

noncomputable section
namespace WuPaper.R2Xi.SixthContinuous
open Real Set MeasureTheory QuarterTrim NodeExtension
open WuTarget.W01Continuous WuSource.SrcSixthGain WuTarget.Wu08FifthSource
open Wu2008DoubleSieve
open scoped Classical Interval

def sumKernel (x : Fin 9 → ℝ) (v : ℝ × ℝ) : ℝ :=
  continuousUniform x 0 (sumShear v)

def reduced (x : Fin 9 → ℝ) (z : ℝ) : ℝ :=
  hContinuous x ((1/2-z)/alpha)/(z*(1/2-z))*
    log (upperX z*(z-lowerX z)/(lowerX z*(z-upperX z)))

theorem sum_integrable {x : Fin 9 → ℝ} (hx : ∀ i, 0 ≤ x i) : Integrable (sumKernel x) :=
  sum_shear_preserving.integrable_comp_of_integrable (continuousUniform_integrable hx le_rfl)

theorem sum_inner (x : Fin 9 → ℝ) {z : ℝ}
    (hz : z ∈ Icc (alpha+beta) (1/2-2*alpha)) :
    (∫ t, sumKernel x (z,t)) = reduced x z := by
  have hg := slice_bounds hz
  have hs : Function.support (fun t => sumKernel x (z,t)) ⊆ Icc (lowerX z) (upperX z) := by
    intro t ht
    by_contra hn
    have hv : (t,z-t) ∉ StaircaseShrink.domain 0 :=
      fun hv => hn ((sum_region_iff z t).mp hv).2
    exact ht (by simp [sumKernel,sumShear,continuousUniform,hv])
  rw [truncatedSixthMass_integral_eq_interval hg.2.1 hs]
  have he : (∫ t in lowerX z..upperX z, sumKernel x (z,t)) =
      ∫ t in lowerX z..upperX z,
        (hContinuous x ((1/2-z)/alpha)/(1/2-z))*(1/(t*(z-t))) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hg.2.1] at ht
    have hv := (sum_region_iff z t).mpr ⟨hz,ht⟩
    change continuousUniform x 0 (t,z-t) = _
    rw [continuousUniform,if_pos hv]
    unfold kernel u
    rw [show (1/2:ℝ)-t-(z-t)=1/2-z by ring]
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  rw [he,intervalIntegral.integral_const_mul,
    reciprocal_ftc hg.1 hg.2.1 (by linarith [hg.2.2.1])]
  unfold reduced
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

end WuPaper.R2Xi.SixthContinuous
#print axioms WuPaper.R2Xi.SixthContinuous.sum_inner
