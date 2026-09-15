import RMapMSixthClassical

noncomputable section
namespace WuPaper.RMapMSixth
open Real Set MeasureTheory QuarterTrim Wu08G6High Wu2008DoubleSieve
open WuSource.SrcSixthGain
open scoped Interval

def g6Raw (p : ℝ → ℝ) : ℝ := 4*∫ v : ℝ × ℝ, rawMasked publishedReducedDomain p v
def g6SumKernel (p : ℝ → ℝ) (v : ℝ × ℝ) : ℝ :=
  rawMasked publishedReducedDomain p (WuTarget.Wu08FifthSource.sumShear v)
def g6ReducedKernel (p : ℝ → ℝ) (z : ℝ) : ℝ :=
  p ((1/2-z)/alpha)/(z*(1/2-z)) *
    log (upperX z*(z-alpha)/(alpha*(z-upperX z)))

theorem g6_reduced_measurable : MeasurableSet publishedReducedDomain := by
  change MeasurableSet {v : ℝ × ℝ |
    alpha ≤ v.1 ∧ v.1 ≤ beta ∧ beta ≤ v.2 ∧ v.1+v.2 ≤ 1/2-2*alpha}
  exact (measurableSet_le measurable_const measurable_fst).inter
    ((measurableSet_le measurable_fst measurable_const).inter
      ((measurableSet_le measurable_const measurable_snd).inter
        (measurableSet_le (measurable_fst.add measurable_snd) measurable_const)))

theorem g6_raw_integrable {p : ℝ → ℝ} {K : ℝ}
    (hp : Measurable p) (hK : 0 ≤ K)
    (hb : ∀ v ∈ envelope, |p (u v.1 v.2)| ≤ K) :
    Integrable (rawMasked publishedReducedDomain p) :=
  raw_integrable hp g6_reduced_measurable
    (published_subset.trans (union_subset rectangleA_subset rectangleB_subset)) hK hb

theorem g6_raw_le_whole {p : ℝ → ℝ} {K : ℝ}
    (hp : Measurable p) (hK : 0 ≤ K)
    (hb : ∀ v ∈ envelope, |p (u v.1 v.2)| ≤ K)
    (hn : ∀ v ∈ envelope, 0 ≤ p (u v.1 v.2)) :
    g6Raw p ≤ paperG6 p := by
  have hiA := raw_integrable hp (measurableSet_Icc.prod measurableSet_Icc) rectangleA_subset hK hb
  have hiB := raw_integrable hp (measurableSet_Icc.prod measurableSet_Icc) rectangleB_subset hK hb
  have hpos {S : Set (ℝ × ℝ)} (hsub : S ⊆ envelope) (v : ℝ × ℝ) :
      0 ≤ rawMasked S p v := by
    by_cases hv : v ∈ S
    · rw [rawMasked,if_pos hv]
      exact div_nonneg (hn v (hsub hv))
        ((envelope_bounds.2.2.2.2.2.trans_le (envelope_denominator (hsub hv))).le)
    · simp [rawMasked,hv]
  have hpoint (v : ℝ × ℝ) :
      rawMasked publishedReducedDomain p v ≤ rawMasked regionA p v+rawMasked regionB p v := by
    by_cases hv : v ∈ publishedReducedDomain
    · rw [rawMasked,if_pos hv]
      rcases published_subset hv with ha | hb
      · rw [rawMasked,if_pos ha]
        exact le_add_of_nonneg_right (hpos rectangleB_subset v)
      · have he : rawMasked regionB p v = kernel p v.1 v.2 := if_pos hb
        rw [he]
        exact le_add_of_nonneg_left (hpos rectangleA_subset v)
    · rw [rawMasked,if_neg hv]
      exact add_nonneg (hpos rectangleA_subset v) (hpos rectangleB_subset v)
  have h := integral_mono (g6_raw_integrable hp hK hb) (hiA.add hiB) hpoint
  simp only [Pi.add_apply] at h
  rw [integral_add hiA hiB] at h
  rw [raw_source_integrals hp hK hb]
  unfold g6Raw
  linarith only [h]

theorem g6_sum_inner (p : ℝ → ℝ) {z : ℝ}
    (hz : z ∈ Icc (alpha+beta) (1/2-2*alpha)) :
    (∫ x, g6SumKernel p (z,x)) = g6ReducedKernel p z := by
  have hg := slice_bounds hz
  have hs : Function.support (fun x => g6SumKernel p (z,x)) ⊆ Icc alpha (upperX z) := by
    intro x hx
    by_contra hn
    have hv : (x,z-x) ∉ publishedReducedDomain :=
      fun hv => hn ((sum_region_iff z x).mp hv).2
    exact hx (by simp [g6SumKernel,WuTarget.Wu08FifthSource.sumShear,rawMasked,hv])
  rw [truncatedSixthMass_integral_eq_interval hg.1 hs]
  have he : (∫ x in alpha..upperX z, g6SumKernel p (z,x)) =
      ∫ x in alpha..upperX z, (p ((1/2-z)/alpha)/(1/2-z))*(1/(x*(z-x))) := by
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
  unfold g6ReducedKernel
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

theorem g6_raw_sum_integral {p : ℝ → ℝ} {K : ℝ}
    (hp : Measurable p) (hK : 0 ≤ K)
    (hb : ∀ v ∈ envelope, |p (u v.1 v.2)| ≤ K) :
    g6Raw p = 4*∫ z in (alpha+beta)..(1/2-2*alpha), g6ReducedKernel p z := by
  have h := WuTarget.Wu08FifthSource.sum_shear_preserving.integral_comp
    WuTarget.Wu08FifthSource.sumShear.measurableEmbedding (rawMasked publishedReducedDomain p)
  change (∫ v : ℝ × ℝ, g6SumKernel p v) = ∫ v, rawMasked publishedReducedDomain p v at h
  rw [g6Raw,← h]
  have hi : Integrable (g6SumKernel p) :=
    WuTarget.Wu08FifthSource.sum_shear_preserving.integrable_comp_of_integrable
      (g6_raw_integrable hp hK hb)
  rw [show (∫ v : ℝ × ℝ, g6SumKernel p v) = ∫ z, ∫ x, g6SumKernel p (z,x) from integral_prod _ hi]
  have hs : Function.support (fun z => ∫ x, g6SumKernel p (z,x)) ⊆
      Icc (alpha+beta) (1/2-2*alpha) := by
    intro z hz
    by_contra hn
    apply hz
    have he : (fun x => g6SumKernel p (z,x)) = 0 := by
      funext x
      have hv : (x,z-x) ∉ publishedReducedDomain :=
        fun hv => hn ((sum_region_iff z x).mp hv).1
      simp [g6SumKernel,WuTarget.Wu08FifthSource.sumShear,rawMasked,hv]
    change (∫ x, g6SumKernel p (z,x)) = 0
    rw [he]
    simp
  have hab : alpha+beta ≤ 1/2-2*alpha := by norm_num [alpha,beta]
  rw [truncatedSixthMass_integral_eq_interval hab hs]
  congr 1
  apply intervalIntegral.integral_congr
  intro z hz
  rw [uIcc_of_le hab] at hz
  exact g6_sum_inner p hz

theorem g6_raw_density_integral {p : ℝ → ℝ} {K : ℝ}
    (hp : Measurable p) (hK : 0 ≤ K)
    (hb : ∀ v ∈ envelope, |p (u v.1 v.2)| ≤ K) :
    g6Raw p = 8*∫ s in (2 : ℝ)..endpoint, density s*p s := by
  have ha : alpha ≠ 0 := alpha_pos.ne'
  have h := intervalIntegral.integral_comp_sub_mul (g6ReducedKernel p) ha (1/2)
    (a := 2) (b := endpoint)
  have he : (1/2 : ℝ)-alpha*endpoint = alpha+beta := by
    unfold endpoint
    field_simp [ha]
    ring
  rw [he,smul_eq_mul] at h
  have hk : (fun s => g6ReducedKernel p (1/2-alpha*s)) =
      fun s => (2/alpha)*(density s*p s) := by
    funext s
    unfold g6ReducedKernel density
    rw [show (1/2 : ℝ)-(1/2-alpha*s)=alpha*s by ring,mul_div_cancel_left₀ s ha]
    rw [show (1/2-alpha*s)*(alpha*s) = (alpha/2)*(s*(1-2*alpha*s)) by ring]
    simp only [div_eq_mul_inv,mul_inv_rev]
    field_simp [ha]
  rw [hk,intervalIntegral.integral_const_mul] at h
  rw [g6_raw_sum_integral hp hK hb]
  have hh := congrArg (fun t : ℝ => alpha*t) h
  field_simp [ha] at hh
  rw [show (1-alpha*2^2)/2 = 1/2-2*alpha by ring] at hh
  linarith only [hh]

theorem g6_original_reduced_le_whole {delta : ℝ}
    (hd : 0 < delta) (hdhi : delta ≤ 1/10) :
    originalReduced delta ≤ paperG6 (wuImprovementLimit false delta) := by
  have hp := boundedH_measurable hd hdhi
  have hK : 0 ≤ wuImprovementLimit false delta 2 :=
    wuImprovementLimit_nonneg false hd (by linarith) (by norm_num) (by norm_num)
  have hb : ∀ v ∈ envelope,
      |boundedH delta (u v.1 v.2)| ≤ wuImprovementLimit false delta 2 := by
    intro v _
    rw [abs_of_nonneg (boundedH_bounds hd hdhi _).1]
    exact (boundedH_bounds hd hdhi _).2
  have h := g6_raw_le_whole hp hK hb (fun v _ => (boundedH_bounds hd hdhi (u v.1 v.2)).1)
  have he : paperG6 (boundedH delta) = paperG6 (wuImprovementLimit false delta) := by
    apply rectangle_congr
    intro v hv
    have hs := envelope_parameter hv
    exact boundedH_eq ⟨hs.1,hs.2.trans (by norm_num [endpoint,alpha,beta])⟩
  rw [he,g6_raw_density_integral hp hK hb] at h
  have hi : (∫ s in (2 : ℝ)..endpoint, density s*boundedH delta s) =
      ∫ s in (2 : ℝ)..endpoint, density s*wuImprovementLimit false delta s := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le scalar_interval] at hs
    dsimp only
    rw [boundedH_eq ⟨by linarith [hs.1],hs.2.trans (by norm_num [endpoint,alpha,beta])⟩]
  rw [hi] at h
  exact h

theorem g6_original_density_integrable {delta : ℝ}
    (hd : 0 < delta) (hdhi : delta ≤ 1/10) :
    IntervalIntegrable (fun s => density s*wuImprovementLimit false delta s) volume 2 endpoint := by
  have hm := (wuImprovementLimit_lower_antitone hd hdhi).mono
    (show Icc 2 endpoint ⊆ Icc (2 : ℝ) 10 from
      Icc_subset_Icc le_rfl (by norm_num [endpoint,alpha,beta]))
  have hm' : AntitoneOn (wuImprovementLimit false delta) (uIcc 2 endpoint) := by
    simpa only [uIcc_of_le scalar_interval] using hm
  have h := hm'.intervalIntegrable.mul_continuousOn
    (show ContinuousOn density (uIcc 2 endpoint) by
      simpa only [uIcc_of_le scalar_interval] using density_continuous)
  simpa only [mul_comm] using h

theorem g6_original_reduced_split {delta : ℝ}
    (hd : 0 < delta) (hdhi : delta ≤ 1/10) :
    originalReduced delta =
      8*(∫ s in (2 : ℝ)..split, lowerKernel s*wuImprovementLimit false delta s) +
      8*(∫ s in split..endpoint, upperKernel s*wuImprovementLimit false delta s) := by
  have hs : (2 : ℝ) ≤ split := by norm_num [split,alpha,beta]
  have he : split ≤ endpoint := by norm_num [split,endpoint,alpha,beta]
  have hi := g6_original_density_integrable hd hdhi
  have hl := hi.mono_set (show uIcc 2 split ⊆ uIcc 2 endpoint by
    rw [uIcc_of_le hs,uIcc_of_le scalar_interval]
    exact Icc_subset_Icc le_rfl he)
  have hr := hi.mono_set (show uIcc split endpoint ⊆ uIcc 2 endpoint by
    rw [uIcc_of_le he,uIcc_of_le scalar_interval]
    exact Icc_subset_Icc hs le_rfl)
  have hleft : (∫ s in (2 : ℝ)..split, density s*wuImprovementLimit false delta s) =
      ∫ s in (2 : ℝ)..split, lowerKernel s*wuImprovementLimit false delta s := by
    apply intervalIntegral.integral_congr
    intro s hs'
    rw [uIcc_of_le hs] at hs'
    dsimp only
    rw [density_lower hs'.2]
  have hright : (∫ s in split..endpoint, density s*wuImprovementLimit false delta s) =
      ∫ s in split..endpoint, upperKernel s*wuImprovementLimit false delta s := by
    apply intervalIntegral.integral_congr
    intro s hs'
    rw [uIcc_of_le he] at hs'
    dsimp only
    rw [density_upper hs'.1]
  rw [originalReduced,← intervalIntegral.integral_add_adjacent_intervals hl hr,hleft,hright]
  ring

#check @g6Raw
#check @g6SumKernel
#check @g6ReducedKernel
#check @g6_reduced_measurable
#check @g6_raw_integrable
#check @g6_raw_le_whole
#check @g6_sum_inner
#check @g6_raw_sum_integral
#check @g6_raw_density_integral
#check @g6_original_reduced_le_whole
#check @g6_original_density_integrable
#check @g6_original_reduced_split
#print axioms g6Raw
#print axioms g6SumKernel
#print axioms g6ReducedKernel
#print axioms g6_reduced_measurable
#print axioms g6_raw_integrable
#print axioms g6_raw_le_whole
#print axioms g6_sum_inner
#print axioms g6_raw_sum_integral
#print axioms g6_raw_density_integral
#print axioms g6_original_reduced_le_whole
#print axioms g6_original_density_integrable
#print axioms g6_original_reduced_split
end WuPaper.RMapMSixth
