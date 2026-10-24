import WSrcSixthGainOriginal
import WR2ClassicalLowerLog

noncomputable section
namespace WuPaper.ClassicalSixthReduction
open Real Set MeasureTheory QuarterTrim DirectFiniteF6 Wu08G6High
open Wu08G6TableGeometryRecovery Wu2008DoubleSieve WuSource.SrcSixthGain
open scoped Classical

/-- Full published sixth region, with an arbitrary integrable coefficient. -/
def published (p : ℝ → ℝ) : ℝ := 4 * ∫ v, rawMasked publishedReducedDomain p v
def sumKernel (p : ℝ → ℝ) (v : ℝ × ℝ) : ℝ :=
  rawMasked publishedReducedDomain p (WuTarget.Wu08FifthSource.sumShear v)
def reduced (p : ℝ → ℝ) (z : ℝ) : ℝ :=
  p ((1/2-z)/alpha)/(z*(1/2-z)) *
    log (upperX z*(z-alpha)/(alpha*(z-upperX z)))

theorem sum_inner (p : ℝ → ℝ) {z : ℝ}
    (hz : z ∈ Icc (alpha+beta) (1/2-2*alpha)) :
    (∫ x, sumKernel p (z,x)) = reduced p z := by
  have hg := slice_bounds hz
  have hs : Function.support (fun x => sumKernel p (z,x)) ⊆ Icc alpha (upperX z) := by
    intro x hx
    by_contra hn
    have hv : (x,z-x) ∉ publishedReducedDomain :=
      fun hv => hn ((sum_region_iff z x).mp hv).2
    exact hx (by simp [sumKernel,WuTarget.Wu08FifthSource.sumShear,rawMasked,hv])
  rw [truncatedSixthMass_integral_eq_interval hg.1 hs]
  have he : (∫ x in alpha..upperX z, sumKernel p (z,x)) =
      ∫ x in alpha..upperX z,
        (p ((1/2-z)/alpha)/(1/2-z))*(1/(x*(z-x))) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hg.1] at hx
    have hv := (sum_region_iff z x).mpr ⟨hz,hx⟩
    change rawMasked publishedReducedDomain p (x,z-x) = _
    rw [rawMasked,if_pos hv]
    unfold kernel u
    rw [show (1/2 : ℝ)-x-(z-x)=1/2-z by ring]
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  rw [he,intervalIntegral.integral_const_mul,
    reciprocal_ftc alpha_pos hg.1 (by linarith [hg.2.1])]
  unfold reduced
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

theorem published_sum_integral (p : ℝ → ℝ)
    (hi : Integrable (rawMasked publishedReducedDomain p)) :
    published p = 4*∫ z in (alpha+beta)..(1/2-2*alpha), reduced p z := by
  have h := WuTarget.Wu08FifthSource.sum_shear_preserving.integral_comp
    WuTarget.Wu08FifthSource.sumShear.measurableEmbedding
    (rawMasked publishedReducedDomain p)
  change (∫ v : ℝ × ℝ, sumKernel p v) = ∫ v, rawMasked publishedReducedDomain p v at h
  rw [published,← h]
  rw [show (∫ v : ℝ × ℝ, sumKernel p v) = ∫ z, ∫ x, sumKernel p (z,x) from
    integral_prod _ (WuTarget.Wu08FifthSource.sum_shear_preserving.integrable_comp_of_integrable hi)]
  have hs : Function.support (fun z => ∫ x, sumKernel p (z,x)) ⊆
      Icc (alpha+beta) (1/2-2*alpha) := by
    intro z hz
    by_contra hn
    apply hz
    have he : (fun x => sumKernel p (z,x)) = 0 := by
      funext x
      have hv : (x,z-x) ∉ publishedReducedDomain :=
        fun hv => hn ((sum_region_iff z x).mp hv).1
      simp [sumKernel,WuTarget.Wu08FifthSource.sumShear,rawMasked,hv]
    change (∫ x, sumKernel p (z,x)) = 0
    rw [he]
    simp
  have hab : alpha+beta ≤ 1/2-2*alpha := by norm_num [alpha,beta]
  rw [truncatedSixthMass_integral_eq_interval hab hs]
  congr 1
  apply intervalIntegral.integral_congr
  intro z hz
  rw [uIcc_of_le hab] at hz
  exact sum_inner p hz

theorem published_density_integral (p : ℝ → ℝ)
    (hi : Integrable (rawMasked publishedReducedDomain p)) :
    published p = 8*∫ s in (2 : ℝ)..endpoint, density s * p s := by
  have ha : alpha ≠ 0 := alpha_pos.ne'
  have h := intervalIntegral.integral_comp_sub_mul (reduced p) ha (1/2)
    (a := 2) (b := endpoint)
  have he : (1/2 : ℝ)-alpha*endpoint = alpha+beta := by
    unfold endpoint
    field_simp [ha]
    ring
  rw [he,smul_eq_mul] at h
  have hk : (fun s => reduced p (1/2-alpha*s)) =
      fun s => (2/alpha)*(density s*p s) := by
    funext s
    unfold reduced density
    rw [show (1/2 : ℝ)-(1/2-alpha*s)=alpha*s by ring,
      mul_div_cancel_left₀ s ha]
    rw [show (1/2-alpha*s)*(alpha*s) = (alpha/2)*(s*(1-2*alpha*s)) by ring]
    simp only [div_eq_mul_inv,mul_inv_rev]
    field_simp [ha]
  rw [hk,intervalIntegral.integral_const_mul] at h
  rw [published_sum_integral p hi]
  have hh := congrArg (fun t : ℝ => alpha*t) h
  field_simp [ha] at hh
  rw [show (1-alpha*2^2)/2 = 1/2-2*alpha by ring] at hh
  linarith only [hh]


end WuPaper.ClassicalSixthReduction
#print axioms WuPaper.ClassicalSixthReduction.published_density_integral
