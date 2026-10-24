import WR2XiSixthContinuousSlice

noncomputable section
namespace WuPaper.R2Xi.SixthContinuous
open Real Set MeasureTheory QuarterTrim NodeExtension Wu2008DoubleSieve
open WuTarget.W01Continuous WuSource.SrcSixthGain WuTarget.Wu08FifthSource
open scoped Classical Interval

def density (s : ℝ) : ℝ :=
  let z := 1/2-alpha*s
  log (upperX z*(z-lowerX z)/(lowerX z*(z-upperX z)))/(s*(1-2*alpha*s))

theorem continuous_sum_integral {w : Fin 9 → ℝ} (hw : ∀ i, 0 ≤ w i) :
    continuousGain w = 4*∫ z in (alpha+beta)..(1/2-2*alpha), reduced w z := by
  have h := WuTarget.Wu08FifthSource.sum_shear_preserving.integral_comp
    WuTarget.Wu08FifthSource.sumShear.measurableEmbedding
    (continuousUniform w 0)
  change (∫ v : ℝ × ℝ, sumKernel w v) = ∫ v, continuousUniform w 0 v at h
  rw [continuousGain, continuousGamma,← h]
  rw [show (∫ v : ℝ × ℝ, sumKernel w v) = ∫ z, ∫ x, sumKernel w (z,x) from
    integral_prod _ (sum_integrable hw)]
  have hs : Function.support (fun z => ∫ x, sumKernel w (z,x)) ⊆
      Icc (alpha+beta) (1/2-2*alpha) := by
    intro z hz
    by_contra hn
    apply hz
    have he : (fun x => sumKernel w (z,x)) = 0 := by
      funext x
      have hv : (x,z-x) ∉ StaircaseShrink.domain 0 :=
        fun hv => hn ((sum_region_iff z x).mp hv).1
      simp [sumKernel,WuTarget.Wu08FifthSource.sumShear,continuousUniform,hv]
    change (∫ x, sumKernel w (z,x)) = 0
    rw [he]
    simp
  have hab : alpha+beta ≤ 1/2-2*alpha := by norm_num [alpha,beta]
  rw [truncatedSixthMass_integral_eq_interval hab hs]
  congr 1
  apply intervalIntegral.integral_congr
  intro z hz
  rw [uIcc_of_le hab] at hz
  exact sum_inner w hz

theorem continuous_density_integral {w : Fin 9 → ℝ} (hw : ∀ i, 0 ≤ w i) :
    continuousGain w = 8*∫ s in (2 : ℝ)..endpoint, density s * hContinuous w s := by
  have ha : alpha ≠ 0 := alpha_pos.ne'
  have h := intervalIntegral.integral_comp_sub_mul (reduced w) ha (1/2)
    (a := 2) (b := endpoint)
  have he : (1/2 : ℝ)-alpha*endpoint = alpha+beta := by
    unfold endpoint
    field_simp [ha]
    ring
  rw [he,smul_eq_mul] at h
  have hk : (fun s => reduced w (1/2-alpha*s)) =
      fun s => (2/alpha)*(density s*hContinuous w s) := by
    funext s
    unfold reduced density
    rw [show (1/2 : ℝ)-(1/2-alpha*s)=alpha*s by ring,
      mul_div_cancel_left₀ s ha]
    rw [show (1/2-alpha*s)*(alpha*s) = (alpha/2)*(s*(1-2*alpha*s)) by ring]
    simp only [div_eq_mul_inv,mul_inv_rev]
    field_simp [ha]
  rw [hk,intervalIntegral.integral_const_mul] at h
  rw [continuous_sum_integral hw]
  have hh := congrArg (fun t : ℝ => alpha*t) h
  field_simp [ha] at hh
  rw [show (1-alpha*2^2)/2 = 1/2-2*alpha by ring] at hh
  linarith only [hh]

end WuPaper.R2Xi.SixthContinuous
#print axioms WuPaper.R2Xi.SixthContinuous.continuous_density_integral
