import SrcSixthGainAnalyticBoundary

noncomputable section
namespace WuSource.SrcSixthGain.Analytic
open Real Set MeasureTheory QuarterTrim DirectFiniteF6 Wu08G6High
open Wu2008DoubleSieve NodeExtension
open scoped Classical BigOperators

def highEndpoint : ℝ := 927/400
def highSumKernel (w : Fin 21 → ℝ) (v : ℝ × ℝ) : ℝ :=
  masked highDomain w (WuTarget.Wu08FifthSource.sumShear v)
def highReduced (w : Fin 21 → ℝ) (z : ℝ) : ℝ :=
  profile w ((1/2-z)/alpha)/(z*(1/2-z)) *
    log ((z-1/4)*(z-alpha)/(alpha*(1/4)))
def highDensity (s : ℝ) : ℝ :=
  log ((1/4-alpha*s)*(1/2-alpha*s-alpha)/(alpha*(1/4))) /
    (s*(1-2*alpha*s))
def highWeight (j : Fin 21) : ℝ := highLoss (WuTarget.W03.basis j)/8
def legalWeight (j : Fin 21) : ℝ := g6Weight j-highWeight j

theorem high_shear_iff (z x : ℝ) :
    (x,z-x) ∈ highDomain ↔
      z ∈ Ioc (alpha+1/4) (1/2-2*alpha) ∧ x ∈ Ico alpha (z-1/4) := by
  rw [high_iff]
  simp only [mem_Icc,mem_Ioc,mem_Ico]
  constructor <;> rintro ⟨⟨h1,h2⟩,h3,h4⟩ <;>
    exact ⟨⟨by linarith,by linarith⟩,by linarith,by linarith⟩

theorem high_z_bounds {z : ℝ}
    (hz : z ∈ Icc (alpha+1/4) (1/2-2*alpha)) :
    alpha ≤ z-1/4 ∧ z-1/4 < z ∧ 0 < z ∧ 0 < 1/2-z := by
  have ha := alpha_pos
  constructor
  · linarith [hz.1]
  constructor
  · linarith
  constructor
  · linarith [hz.1]
  · linarith [hz.2]

theorem highSum_integrable (w : Fin 21 → ℝ) : Integrable (highSumKernel w) :=
  WuTarget.Wu08FifthSource.sum_shear_preserving.integrable_comp_of_integrable
    (high_integrable w)

theorem high_sum_inner (w : Fin 21 → ℝ) {z : ℝ}
    (hz : z ∈ Icc (alpha+1/4) (1/2-2*alpha)) :
    (∫ x, highSumKernel w (z,x)) = highReduced w z := by
  have hg := high_z_bounds hz
  have hs : Function.support (fun x => highSumKernel w (z,x)) ⊆ Icc alpha (z-1/4) := by
    intro x hx
    by_contra hn
    have hv : (x,z-x) ∉ highDomain := by
      intro hv
      have h := (high_shear_iff z x).mp hv
      exact hn ⟨h.2.1,h.2.2.le⟩
    exact hx (by simp [highSumKernel,WuTarget.Wu08FifthSource.sumShear,masked,hv])
  rw [truncatedSixthMass_integral_eq_interval hg.1 hs]
  have he : (∫ x in alpha..(z-1/4), highSumKernel w (z,x)) =
      ∫ x in alpha..(z-1/4),
        (profile w ((1/2-z)/alpha)/(1/2-z))*(1/(x*(z-x))) := by
    apply intervalIntegral.integral_congr_uIoo
    intro x hx
    rw [uIoo_of_le hg.1] at hx
    have hv : (x,z-x) ∈ highDomain :=
      (high_shear_iff z x).mpr ⟨⟨by linarith [hx.1,hx.2],hz.2⟩,hx.1.le,hx.2⟩
    change masked highDomain w (x,z-x) = _
    rw [masked,if_pos hv]
    unfold kernel u
    rw [show (1/2 : ℝ)-x-(z-x)=1/2-z by ring]
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  rw [he,intervalIntegral.integral_const_mul,reciprocal_ftc alpha_pos hg.1 hg.2.1]
  unfold highReduced
  rw [show z-(z-1/4) = (1/4 : ℝ) by ring]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

theorem high_sum_integral (w : Fin 21 → ℝ) :
    highLoss w = 4*∫ z in (alpha+1/4)..(1/2-2*alpha), highReduced w z := by
  have h := WuTarget.Wu08FifthSource.sum_shear_preserving.integral_comp
    WuTarget.Wu08FifthSource.sumShear.measurableEmbedding (masked highDomain w)
  change (∫ v : ℝ × ℝ, highSumKernel w v) = ∫ v, masked highDomain w v at h
  rw [highLoss,← h]
  rw [show (∫ v : ℝ × ℝ, highSumKernel w v) = ∫ z, ∫ x, highSumKernel w (z,x) from
    integral_prod _ (highSum_integrable w)]
  have hs : Function.support (fun z => ∫ x, highSumKernel w (z,x)) ⊆
      Icc (alpha+1/4) (1/2-2*alpha) := by
    intro z hz
    by_contra hn
    apply hz
    have he : (fun x => highSumKernel w (z,x)) = 0 := by
      funext x
      have hv : (x,z-x) ∉ highDomain := by
        intro hv
        have h := (high_shear_iff z x).mp hv
        exact hn ⟨h.1.1.le,h.1.2⟩
      simp [highSumKernel,WuTarget.Wu08FifthSource.sumShear,masked,hv]
    change (∫ x, highSumKernel w (z,x)) = 0
    rw [he]
    simp
  have hab : alpha+1/4 ≤ 1/2-2*alpha := by norm_num [alpha]
  rw [truncatedSixthMass_integral_eq_interval hab hs]
  congr 1
  apply intervalIntegral.integral_congr
  intro z hz
  rw [uIcc_of_le hab] at hz
  exact high_sum_inner w hz

theorem high_density_integral (w : Fin 21 → ℝ) :
    highLoss w = 8*∫ s in (2 : ℝ)..highEndpoint, highDensity s*profile w s := by
  have ha : alpha ≠ 0 := alpha_pos.ne'
  have h := intervalIntegral.integral_comp_sub_mul (highReduced w) ha (1/2)
    (a := 2) (b := highEndpoint)
  have he : (1/2 : ℝ)-alpha*highEndpoint=alpha+1/4 := by norm_num [alpha,highEndpoint]
  rw [he,smul_eq_mul] at h
  have hk : (fun s => highReduced w (1/2-alpha*s)) =
      fun s => (2/alpha)*(highDensity s*profile w s) := by
    funext s
    unfold highReduced highDensity
    rw [show (1/2 : ℝ)-(1/2-alpha*s)=alpha*s by ring,
      mul_div_cancel_left₀ s ha,
      show (1/2-alpha*s)-1/4=1/4-alpha*s by ring,
      show (1/2-alpha*s)*(alpha*s)=(alpha/2)*(s*(1-2*alpha*s)) by ring]
    simp only [div_eq_mul_inv,mul_inv_rev]
    field_simp [ha]
  rw [hk,intervalIntegral.integral_const_mul] at h
  have hh := congrArg (fun t : ℝ => alpha*t) h
  field_simp [ha] at hh
  rw [show (1-alpha*2^2)/2=1/2-2*alpha by ring,
    show (alpha*4+1)/4=alpha+1/4 by ring] at hh
  rw [high_sum_integral]
  linarith only [hh]

theorem high_cell_bounds (j : Fin 21) (hj : j.val < 4) :
    2 ≤ rNode j.val ∧
      rNode j.val ≤ min (rNode (j.val+1)) highEndpoint ∧
      min (rNode (j.val+1)) highEndpoint ≤ highEndpoint := by
  refine ⟨?_,le_min (rNode_mono (by omega)) ?_,min_le_right _ _⟩
  · unfold rNode
    exact le_add_of_nonneg_right (by positivity)
  · exact (rNode_mono (show j.val ≤ 3 by omega)).trans (by norm_num [rNode,highEndpoint])

theorem high_weight_integral (j : Fin 21) (hj : j.val < 4) :
    highWeight j = ∫ s in rNode j.val..min (rNode (j.val+1)) highEndpoint, highDensity s := by
  have hi : (2 : ℝ) ≤ highEndpoint := by norm_num [highEndpoint]
  have he : (fun s => highDensity s*profile (WuTarget.W03.basis j) s) =
      (Ioc (rNode j.val) (rNode (j.val+1))).indicator highDensity := by
    funext s
    rw [WuTarget.W03.profile_basis]
    by_cases hc : WuTarget.W03.cell j s
    · rw [if_pos hc,indicator_of_mem
        (show s ∈ Ioc (rNode j.val) (rNode (j.val+1)) from hc),mul_one]
    · rw [if_neg hc,indicator_of_notMem
        (show s ∉ Ioc (rNode j.val) (rNode (j.val+1)) from hc),mul_zero]
  have hs : Ioc (2 : ℝ) highEndpoint ∩ Ioc (rNode j.val) (rNode (j.val+1)) =
      Ioc (rNode j.val) (min (rNode (j.val+1)) highEndpoint) := by
    ext s
    simp only [mem_inter_iff,mem_Ioc,le_min_iff]
    constructor
    · rintro ⟨⟨_,he⟩,hl,hu⟩
      exact ⟨hl,hu,he⟩
    · rintro ⟨hl,hu,he⟩
      exact ⟨⟨(high_cell_bounds j hj).1.trans_lt hl,he⟩,hl,hu⟩
  rw [highWeight,high_density_integral,he,intervalIntegral.integral_of_le hi,
    setIntegral_indicator measurableSet_Ioc,hs,
    ← intervalIntegral.integral_of_le (high_cell_bounds j hj).2.1]
  ring

theorem first_three_high_weights (j : Fin 21) (hj : j.val < 3) :
    highWeight j = ∫ s in rNode j.val..rNode (j.val+1), highDensity s := by
  rw [high_weight_integral j (by omega)]
  have he : rNode (j.val+1) ≤ highEndpoint :=
    (rNode_mono (show j.val+1 ≤ 3 by omega)).trans (by norm_num [rNode,highEndpoint])
  rw [min_eq_left he]

theorem fourth_high_weight :
    highWeight (3 : Fin 21) = ∫ s in (23/10 : ℝ)..(927/400 : ℝ), highDensity s := by
  rw [high_weight_integral (3 : Fin 21) (by norm_num)]
  norm_num [rNode,highEndpoint]

theorem later_high_weights_zero (j : Fin 21) (hj : 4 ≤ j.val) :
    highWeight j = 0 := by
  rw [highWeight,high_basis_zero j hj,zero_div]

theorem high_masked_expansion (w : Fin 21 → ℝ) (v : ℝ × ℝ) :
    masked highDomain w v =
      ∑ j : Fin 21, w j*masked highDomain (WuTarget.W03.basis j) v := by
  unfold masked
  by_cases hv : v ∈ highDomain
  · simp only [if_pos hv,kernel,WuTarget.W03.profile_expansion w,Finset.sum_div,mul_div_assoc]
  · simp [hv]

theorem high_loss_expansion (w : Fin 21 → ℝ) :
    highLoss w = 8*∑ j : Fin 21, highWeight j*w j := by
  unfold highLoss
  simp_rw [high_masked_expansion w]
  rw [integral_finsetSum _ (fun j _ => (high_integrable (WuTarget.W03.basis j)).const_mul (w j))]
  simp only [integral_const_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  unfold highWeight highLoss
  ring

theorem legal_weight_exact (j : Fin 21) :
    8*legalWeight j = WuTarget.W03.weight j := by
  have h := published_eq_legal_add_high (WuTarget.W03.basis j)
  rw [published_basis] at h
  unfold legalWeight highWeight
  change 8*g6Weight j = WuTarget.W03.weight j+highLoss (WuTarget.W03.basis j) at h
  linarith only [h]

theorem legal_weight_nonneg (j : Fin 21) : 0 ≤ legalWeight j := by
  have h := WuTarget.W03.weight_nonneg j
  rw [← legal_weight_exact] at h
  linarith

theorem high_weight_nonneg (j : Fin 21) : 0 ≤ highWeight j :=
  div_nonneg (high_nonneg (WuTarget.W03.basis_nonneg j)) (by norm_num)

theorem high_weight_le_full (j : Fin 21) : highWeight j ≤ g6Weight j := by
  have h := legal_weight_nonneg j
  unfold legalWeight at h
  linarith

theorem legal_full_weight_identity (w : Fin 21 → ℝ) :
    8*(∑ j : Fin 21, legalWeight j*w j) = Gamma w 0 := by
  rw [WuTarget.W03.Gamma_eq_weights,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [← mul_assoc,legal_weight_exact]

#print axioms high_density_integral
#print axioms first_three_high_weights
#print axioms fourth_high_weight
#print axioms high_loss_expansion
#print axioms legal_full_weight_identity
end WuSource.SrcSixthGain.Analytic
