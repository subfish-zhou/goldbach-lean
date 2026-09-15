import Wu08G6HighLoss
import W03Weights
import WE07FifthSourceReduction

noncomputable section
namespace WuSource.SrcSixthGain
open Real Set MeasureTheory QuarterTrim DirectFiniteF6 Wu08G6High
open Wu08G6TableGeometryRecovery Wu2008DoubleSieve
open scoped Classical

def split : ℝ := (1/2-2*beta)/alpha
def endpoint : ℝ := (1/2-alpha-beta)/alpha
def upperX (z : ℝ) : ℝ := min beta (z-beta)
def sumKernel (w : Fin 21 → ℝ) (v : ℝ × ℝ) : ℝ :=
  masked publishedReducedDomain w (WuTarget.Wu08FifthSource.sumShear v)
def reduced (w : Fin 21 → ℝ) (z : ℝ) : ℝ :=
  profile w ((1/2-z)/alpha)/(z*(1/2-z)) *
    log (upperX z*(z-alpha)/(alpha*(z-upperX z)))
def density (s : ℝ) : ℝ :=
  log (upperX (1/2-alpha*s)*((1/2-alpha*s)-alpha) /
    (alpha*((1/2-alpha*s)-upperX (1/2-alpha*s)))) / (s*(1-2*alpha*s))
def lowerKernel (s : ℝ) : ℝ :=
  log (beta*(1-2*alpha-2*alpha*s)/(alpha*(1-2*beta-2*alpha*s))) /
    (s*(1-2*alpha*s))
def upperKernel (s : ℝ) : ℝ :=
  log ((1-2*alpha-2*alpha*s)*(1-2*beta-2*alpha*s)/(4*alpha*beta)) /
    (s*(1-2*alpha*s))

theorem breakpoints :
    split = (70331/20600 : ℝ) ∧ endpoint = (41453/10300 : ℝ) ∧
    (34/10 : ℝ) < split ∧ split < 35/10 ∧
    (40/10 : ℝ) < endpoint ∧ endpoint < 41/10 := by
  norm_num [split, endpoint, alpha, beta]

theorem source_reduced_domain : QuarterTrim.originalP = publishedReducedDomain :=
  QuarterTrim.originalP_eq_clippedP

theorem sum_region_iff (z x : ℝ) :
    (x,z-x) ∈ publishedReducedDomain ↔
      z ∈ Icc (alpha+beta) (1/2-2*alpha) ∧ x ∈ Icc alpha (upperX z) := by
  simp only [publishedReducedDomain, mem_ofPred_eq, mem_Icc, upperX, le_min_iff]
  constructor
  · rintro ⟨hx,hxb,hy,hz⟩
    exact ⟨⟨by linarith, by linarith⟩,hx,hxb,by linarith⟩
  · rintro ⟨hz,hx,hxb,hy⟩
    exact ⟨hx,hxb,by linarith,by linarith [hz.2]⟩

theorem slice_bounds {z : ℝ} (hz : z ∈ Icc (alpha+beta) (1/2-2*alpha)) :
    alpha ≤ upperX z ∧ 0 < z-upperX z ∧ 0 < z ∧ 0 < 1/2-z := by
  have hab : alpha ≤ beta := by norm_num [alpha,beta]
  have hb : 0 < beta := by norm_num [beta]
  have hm := min_le_right beta (z-beta)
  refine ⟨le_min hab (by linarith [hz.1]),?_,?_,?_⟩
  · dsimp [upperX]
    linarith
  · linarith [hz.1,alpha_pos]
  · linarith [hz.2,alpha_pos]

theorem reciprocal_ftc {z l b : ℝ} (hl : 0 < l) (hlb : l ≤ b) (hbz : b < z) :
    (∫ x in l..b, 1/(x*(z-x))) =
      log (b*(z-l)/(l*(z-b)))/z := by
  have hz : 0 < z := by linarith
  have hb : 0 < b := hl.trans_le hlb
  have hzl : 0 < z-l := by linarith
  have hzb : 0 < z-b := by linarith
  have hn (x : ℝ) (hx : x ∈ uIcc l b) : 0 < x ∧ 0 < z-x := by
    rw [uIcc_of_le hlb] at hx
    exact ⟨hl.trans_le hx.1,by linarith [hx.2]⟩
  have hi : IntervalIntegrable (fun x => 1/(x*(z-x))) volume l b :=
    ContinuousOn.intervalIntegrable
      (continuousOn_const.div (continuousOn_id.mul (continuousOn_const.sub continuousOn_id))
        (fun x hx => mul_ne_zero (hn x hx).1.ne' (hn x hx).2.ne'))
  have hd (x : ℝ) (hx : x ∈ uIcc l b) :
      HasDerivAt (fun x => (log x-log (z-x))/z) (1/(x*(z-x))) x := by
    have hh := ((hasDerivAt_log (hn x hx).1.ne').sub
      (((hasDerivAt_const x z).sub (hasDerivAt_id x)).log
        (by simpa only [Pi.sub_apply,id_eq] using (hn x hx).2.ne'))).div_const z
    convert hh using 1 <;> first | rfl |
      (simp only [Pi.sub_apply,id_eq]
       field_simp [hz.ne', (hn x hx).1.ne', (hn x hx).2.ne']
       ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi,
    log_div (mul_pos hb hzl).ne' (mul_pos hl hzb).ne',
    log_mul hb.ne' hzl.ne',log_mul hl.ne' hzb.ne']
  ring

theorem sum_integrable (w : Fin 21 → ℝ) : Integrable (sumKernel w) :=
  WuTarget.Wu08FifthSource.sum_shear_preserving.integrable_comp_of_integrable
    (published_integrable w)

theorem sum_inner (w : Fin 21 → ℝ) {z : ℝ}
    (hz : z ∈ Icc (alpha+beta) (1/2-2*alpha)) :
    (∫ x, sumKernel w (z,x)) = reduced w z := by
  have hg := slice_bounds hz
  have hs : Function.support (fun x => sumKernel w (z,x)) ⊆ Icc alpha (upperX z) := by
    intro x hx
    by_contra hn
    have hv : (x,z-x) ∉ publishedReducedDomain :=
      fun hv => hn ((sum_region_iff z x).mp hv).2
    exact hx (by simp [sumKernel,WuTarget.Wu08FifthSource.sumShear,masked,hv])
  rw [truncatedSixthMass_integral_eq_interval hg.1 hs]
  have he : (∫ x in alpha..upperX z, sumKernel w (z,x)) =
      ∫ x in alpha..upperX z,
        (profile w ((1/2-z)/alpha)/(1/2-z))*(1/(x*(z-x))) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hg.1] at hx
    have hv := (sum_region_iff z x).mpr ⟨hz,hx⟩
    change masked publishedReducedDomain w (x,z-x) = _
    rw [masked,if_pos hv]
    unfold kernel u
    rw [show (1/2 : ℝ)-x-(z-x)=1/2-z by ring]
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  rw [he,intervalIntegral.integral_const_mul,
    reciprocal_ftc alpha_pos hg.1 (by linarith [hg.2.1])]
  unfold reduced
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

theorem published_sum_integral (w : Fin 21 → ℝ) :
    published w = 4*∫ z in (alpha+beta)..(1/2-2*alpha), reduced w z := by
  have h := WuTarget.Wu08FifthSource.sum_shear_preserving.integral_comp
    WuTarget.Wu08FifthSource.sumShear.measurableEmbedding
    (masked publishedReducedDomain w)
  change (∫ v : ℝ × ℝ, sumKernel w v) = ∫ v, masked publishedReducedDomain w v at h
  rw [published,← h]
  rw [show (∫ v : ℝ × ℝ, sumKernel w v) = ∫ z, ∫ x, sumKernel w (z,x) from
    integral_prod _ (sum_integrable w)]
  have hs : Function.support (fun z => ∫ x, sumKernel w (z,x)) ⊆
      Icc (alpha+beta) (1/2-2*alpha) := by
    intro z hz
    by_contra hn
    apply hz
    have he : (fun x => sumKernel w (z,x)) = 0 := by
      funext x
      have hv : (x,z-x) ∉ publishedReducedDomain :=
        fun hv => hn ((sum_region_iff z x).mp hv).1
      simp [sumKernel,WuTarget.Wu08FifthSource.sumShear,masked,hv]
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

theorem published_density_integral (w : Fin 21 → ℝ) :
    published w = 8*∫ s in (2 : ℝ)..endpoint, density s * profile w s := by
  have ha : alpha ≠ 0 := alpha_pos.ne'
  have h := intervalIntegral.integral_comp_sub_mul (reduced w) ha (1/2)
    (a := 2) (b := endpoint)
  have he : (1/2 : ℝ)-alpha*endpoint = alpha+beta := by
    unfold endpoint
    field_simp [ha]
    ring
  rw [he,smul_eq_mul] at h
  have hk : (fun s => reduced w (1/2-alpha*s)) =
      fun s => (2/alpha)*(density s*profile w s) := by
    funext s
    unfold reduced density
    rw [show (1/2 : ℝ)-(1/2-alpha*s)=alpha*s by ring,
      mul_div_cancel_left₀ s ha]
    rw [show (1/2-alpha*s)*(alpha*s) = (alpha/2)*(s*(1-2*alpha*s)) by ring]
    simp only [div_eq_mul_inv,mul_inv_rev]
    field_simp [ha]
  rw [hk,intervalIntegral.integral_const_mul] at h
  rw [published_sum_integral]
  have hh := congrArg (fun t : ℝ => alpha*t) h
  field_simp [ha] at hh
  rw [show (1-alpha*2^2)/2 = 1/2-2*alpha by ring] at hh
  linarith only [hh]

theorem density_lower {s : ℝ} (hs : s ≤ split) : density s = lowerKernel s := by
  have hz : beta ≤ 1/2-alpha*s-beta := by
    have h := (le_div_iff₀ alpha_pos).mp hs
    linarith
  unfold density upperX lowerKernel
  rw [min_eq_left hz]
  congr 2
  rw [show 1-2*alpha-2*alpha*s = 2*((1/2-alpha*s)-alpha) by ring,
    show 1-2*beta-2*alpha*s = 2*((1/2-alpha*s)-beta) by ring]
  have hb : 0 < beta := by norm_num [beta]
  have hden : (1/2-alpha*s)-beta ≠ 0 := (hb.trans_le hz).ne'
  field_simp [alpha_pos.ne',hden]

theorem density_upper {s : ℝ} (hs : split ≤ s) : density s = upperKernel s := by
  have hz : 1/2-alpha*s-beta ≤ beta := by
    have h := (div_le_iff₀ alpha_pos).mp hs
    linarith
  unfold density upperX upperKernel
  rw [min_eq_right hz]
  rw [show (1/2-alpha*s)-(1/2-alpha*s-beta)=beta by ring]
  congr 2
  rw [show 1-2*alpha-2*alpha*s = 2*((1/2-alpha*s)-alpha) by ring,
    show 1-2*beta-2*alpha*s = 2*((1/2-alpha*s)-beta) by ring]
  ring

#print axioms published_density_integral
#print axioms density_lower
#print axioms density_upper
end WuSource.SrcSixthGain
