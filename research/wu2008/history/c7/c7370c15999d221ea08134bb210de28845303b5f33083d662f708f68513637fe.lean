import SrcFifthGainProfile

namespace WuSource.SrcFifthGain
open Wu2008DoubleSieve WuTarget.Wu08FifthSource SharpMassBalance
open MeasureTheory Set Real
open scoped Interval
noncomputable section

def sourceKernel (p : ℝ → ℝ) (t u : ℝ) : ℝ :=
  p u/(t*u*(1-2*t-2*a*u))

def sourceGain (p : ℝ → ℝ) : ℝ :=
  8*∫ t in a..b, ∫ u in ((1/2-b-t)/a)..((1/2-2*t)/a), sourceKernel p t u

def weight (s : ℝ) : ℝ := reducedWeight s/2

def scalarGain (p : ℝ → ℝ) : ℝ :=
  8*∫ s in s0..FifthClassicalShape.q, p s*weight s

theorem source_inner_substitution (p : ℝ → ℝ) (t : ℝ) :
    2*(∫ u in ((1/2-b-t)/a)..((1/2-2*t)/a), sourceKernel p t u) =
      ∫ y in t..b, p ((1/2-t-y)/a)/(t*y*(1/2-t-y)) := by
  have ha : a ≠ 0 := truncatedSixthLower_parameters.1.ne'
  have h := intervalIntegral.integral_comp_sub_div (sourceKernel p t) ha ((1/2-t)/a)
    (a := t) (b := b)
  rw [show (1/2-t)/a-b/a = (1/2-b-t)/a by ring,
    show (1/2-t)/a-t/a = (1/2-2*t)/a by ring, smul_eq_mul] at h
  have hk : (fun y => sourceKernel p t ((1/2-t)/a-y/a)) =
      fun y => (a/2)*(p ((1/2-t-y)/a)/(t*y*(1/2-t-y))) := by
    funext y
    rw [show (1/2-t)/a-y/a = (1/2-t-y)/a by ring]
    unfold sourceKernel
    rw [show 1-2*t-2*a*((1/2-t-y)/a) = 2*y by field_simp [ha]; ring]
    field_simp [ha]
  rw [hk, intervalIntegral.integral_const_mul] at h
  apply mul_left_cancel₀ ha
  linarith only [h]

theorem triangle_outer (p : ℝ → ℝ) (hi : Integrable (profileKernel p)) :
    triangleGain p = 4*∫ t in a..b, ∫ y in t..b,
      p ((1/2-t-y)/a)/(t*y*(1/2-t-y)) := by
  unfold triangleGain
  rw [show (∫ v : ℝ × ℝ, profileKernel p v) =
    ∫ t, ∫ y, profileKernel p (t,y) from integral_prod _ hi]
  have hs : Function.support (fun t => ∫ y, profileKernel p (t,y)) ⊆ Icc a b := by
    intro t ht
    by_contra hn
    apply ht
    change (∫ y, profileKernel p (t,y)) = 0
    have hz : (fun y => profileKernel p (t,y)) = 0 := by
      funext y
      have hv : (t,y) ∉ fifthPairRegion := fun h => hn ⟨h.1, h.2.1.trans h.2.2⟩
      simp [profileKernel, hv]
    rw [hz]
    simp
  rw [truncatedSixthMass_integral_eq_interval truncatedSixthLower_parameters.2.1.le hs]
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le truncatedSixthLower_parameters.2.1.le] at ht
  have hs' : Function.support (fun y => profileKernel p (t,y)) ⊆ Icc t b := by
    intro y hy
    by_cases hv : (t,y) ∈ fifthPairRegion
    · exact ⟨hv.2.1, hv.2.2⟩
    · exact False.elim (hy (by simp [profileKernel, hv]))
  change (∫ y, profileKernel p (t,y)) = _
  rw [truncatedSixthMass_integral_eq_interval ht.2 hs']
  apply intervalIntegral.integral_congr
  intro y hy
  rw [uIcc_of_le ht.2] at hy
  exact indicator_of_mem (show (t,y) ∈ fifthPairRegion from ⟨ht.1, hy.1, hy.2⟩) _

theorem source_eq_triangle {p : ℝ → ℝ} (hi : Integrable (profileKernel p)) :
    sourceGain p = triangleGain p := by
  rw [triangle_outer p hi]
  have h : (∫ t in a..b,
      2*(∫ u in ((1/2-b-t)/a)..((1/2-2*t)/a), sourceKernel p t u)) =
      ∫ t in a..b, ∫ y in t..b, p ((1/2-t-y)/a)/(t*y*(1/2-t-y)) := by
    apply intervalIntegral.integral_congr
    intro t _
    exact source_inner_substitution p t
  rw [intervalIntegral.integral_const_mul] at h
  unfold sourceGain
  linarith only [h]

def shearedKernel (p : ℝ → ℝ) (v : ℝ × ℝ) : ℝ :=
  profileKernel p (sumShear v)

def reducedProfile (p : ℝ → ℝ) (z : ℝ) : ℝ :=
  p ((1/2-z)/a)/(z*(1/2-z))*log ((z-sliceLower z)/sliceLower z)

theorem sheared_inner (p : ℝ → ℝ) {z : ℝ} (hz : z ∈ Icc (2*a) (2*b)) :
    (∫ x, shearedKernel p (z,x)) = reducedProfile p z := by
  have hg := slice_geometry hz
  have hs : Function.support (fun x => shearedKernel p (z,x)) ⊆
      Icc (sliceLower z) (z/2) := by
    intro x hx
    by_contra hn
    have hv : (x,z-x) ∉ fifthPairRegion := fun hv => hn ((sum_region_iff z x).mp hv).2
    exact hx (by simp [shearedKernel, sumShear, profileKernel, hv])
  rw [truncatedSixthMass_integral_eq_interval hg.2.1 hs]
  have he : (∫ x in sliceLower z..(z/2), shearedKernel p (z,x)) =
      ∫ x in sliceLower z..(z/2), (p ((1/2-z)/a)/(1/2-z))*(1/(x*(z-x))) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hg.2.1] at hx
    have hv := (sum_region_iff z x).mpr ⟨hz, hx⟩
    change profileKernel p (x,z-x) = _
    rw [profileKernel, indicator_of_mem hv]
    dsimp only
    rw [show (1/2 : ℝ)-x-(z-x)=1/2-z by ring]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [he, intervalIntegral.integral_const_mul, pair_reciprocal_ftc hg.1 hg.2.1]
  unfold reducedProfile
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem triangle_reduced {p : ℝ → ℝ} (hi : Integrable (profileKernel p)) :
    triangleGain p = 4*∫ z in (2*a)..(2*b), reducedProfile p z := by
  have h := sum_shear_preserving.integral_comp sumShear.measurableEmbedding (profileKernel p)
  have hi' : Integrable (shearedKernel p) :=
    sum_shear_preserving.integrable_comp_of_integrable hi
  change (∫ v : ℝ × ℝ, shearedKernel p v) = ∫ v : ℝ × ℝ, profileKernel p v at h
  unfold triangleGain
  rw [← h, show (∫ v : ℝ × ℝ, shearedKernel p v) =
    ∫ z, ∫ x, shearedKernel p (z,x) from integral_prod _ hi']
  have hs : Function.support (fun z => ∫ x, shearedKernel p (z,x)) ⊆ Icc (2*a) (2*b) := by
    intro z hz
    by_contra hn
    apply hz
    change (∫ x, shearedKernel p (z,x)) = 0
    have he : (fun x => shearedKernel p (z,x)) = 0 := by
      funext x
      have hv : (x,z-x) ∉ fifthPairRegion := fun hv => hn ((sum_region_iff z x).mp hv).1
      simp [shearedKernel, sumShear, profileKernel, hv]
    rw [he]
    simp
  have hab : 2*a ≤ 2*b := by linarith [truncatedSixthLower_parameters.2.1]
  rw [truncatedSixthMass_integral_eq_interval hab hs]
  congr 1
  apply intervalIntegral.integral_congr
  intro z hz
  rw [uIcc_of_le hab] at hz
  exact sheared_inner p hz

theorem source_eq_scalar {p : ℝ → ℝ} (hi : Integrable (profileKernel p)) :
    sourceGain p = scalarGain p := by
  have ha : a ≠ 0 := truncatedSixthLower_parameters.1.ne'
  have h := intervalIntegral.integral_comp_sub_mul (reducedProfile p) ha (1/2)
    (a := s0) (b := FifthClassicalShape.q)
  have hlo : (1/2 : ℝ)-a*FifthClassicalShape.q = 2*a := by
    unfold FifthClassicalShape.q
    field_simp [ha]
    ring
  have hhi : (1/2 : ℝ)-a*s0 = 2*b := by
    unfold s0
    field_simp [ha]
    ring
  rw [hlo, hhi, smul_eq_mul] at h
  have hk : (fun s => reducedProfile p (1/2-a*s)) =
      fun s => (2/a)*(p s*weight s) := by
    funext s
    unfold reducedProfile weight reducedWeight
    rw [show (1/2 : ℝ)-(1/2-a*s)=a*s by ring, mul_div_cancel_left₀ s ha]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [hk, intervalIntegral.integral_const_mul] at h
  rw [source_eq_triangle hi, triangle_reduced hi]
  unfold scalarGain
  have h' := congrArg (fun x : ℝ => a*x) h
  field_simp [ha] at h'
  rw [mul_comm a 2] at h'
  linarith only [h']

theorem source_profile_count {p : ℝ → ℝ}
    (hi : Integrable (profileKernel p))
    (hn : ∀ s ∈ Icc s0 FifthClassicalShape.q, 0 ≤ p s)
    (hc : ∀ δ : ℝ, 0 < δ → δ ≤ 1/1000 →
      ∀ s ∈ Icc s0 FifthClassicalShape.q, p s ≤ wuImprovementLimit false δ s)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (fifthPairFlin+sourceGain p-ε)*wuSingularSeries N*N/log N^(2 : ℕ) ≤
        (fifthPairCount N : ℝ) := by
  rw [source_eq_triangle hi]
  exact profile_count hi hn hc hε

end
end WuSource.SrcFifthGain
