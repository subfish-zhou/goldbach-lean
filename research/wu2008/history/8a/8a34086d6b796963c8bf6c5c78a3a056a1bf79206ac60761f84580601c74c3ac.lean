import SrcSixthGainReduction

noncomputable section
namespace WuSource.SrcSixthGain
open Real Set MeasureTheory QuarterTrim DirectFiniteF6 Wu08G6High
open Wu08G6TableGeometryRecovery Wu2008DoubleSieve NodeExtension
open scoped Classical BigOperators

def cellEnd (j : Fin 21) : ℝ := min (rNode (j.val+1)) endpoint
def g6Weight (j : Fin 21) : ℝ := ∫ s in rNode j.val..cellEnd j, density s

theorem scalar_bounds {s : ℝ} (hs : s ∈ Icc 2 endpoint) :
    1/2-alpha*s ∈ Icc (alpha+beta) (1/2-2*alpha) := by
  have he := (le_div_iff₀ alpha_pos).mp hs.2
  exact ⟨by linarith,by nlinarith [hs.1,alpha_pos]⟩

theorem density_nonneg {s : ℝ} (hs : s ∈ Icc 2 endpoint) : 0 ≤ density s := by
  have hg := slice_bounds (scalar_bounds hs)
  let z := 1/2-alpha*s
  change alpha ≤ upperX z ∧ 0 < z-upperX z ∧ 0 < z ∧ 0 < 1/2-z at hg
  have hden : 0 < alpha*(z-upperX z) := mul_pos alpha_pos hg.2.1
  have hratio : 1 ≤ upperX z*(z-alpha)/(alpha*(z-upperX z)) := by
    apply (le_div_iff₀ hden).mpr
    nlinarith [mul_nonneg hg.2.2.1.le (sub_nonneg.mpr hg.1)]
  unfold density
  dsimp [z] at hg
  exact div_nonneg (log_nonneg hratio)
    (mul_nonneg (by linarith [hs.1]) (by linarith [hg.2.2.1]))

theorem density_continuous : ContinuousOn density (Icc 2 endpoint) := by
  have hm : Continuous (fun s : ℝ => upperX (1/2-alpha*s)) := by
    unfold upperX
    fun_prop
  apply ContinuousOn.div
  · apply ContinuousOn.log
    · exact (hm.continuousOn.mul (by fun_prop)).div (by fun_prop)
        (fun s hs => (mul_pos alpha_pos (slice_bounds (scalar_bounds hs)).2.1).ne')
    · intro s hs
      have hg := slice_bounds (scalar_bounds hs)
      exact (div_pos (mul_pos (alpha_pos.trans_le hg.1)
        (by linarith [hg.1,hg.2.1]))
        (mul_pos alpha_pos hg.2.1)).ne'
  · fun_prop
  · intro s hs
    have hg := slice_bounds (scalar_bounds hs)
    exact (mul_pos (by linarith [hs.1]) (by linarith [hg.2.2.1])).ne'

theorem scalar_interval : (2 : ℝ) ≤ endpoint := by
  norm_num [endpoint,alpha,beta]

theorem density_integrable : IntervalIntegrable density volume 2 endpoint := by
  apply ContinuousOn.intervalIntegrable
  simpa only [uIcc_of_le scalar_interval] using density_continuous

theorem cell_bounds (j : Fin 21) :
    2 ≤ rNode j.val ∧ rNode j.val ≤ cellEnd j ∧ cellEnd j ≤ endpoint := by
  have hj : j.val ≤ 20 := by omega
  have h0 : (2 : ℝ) ≤ rNode j.val := by
    unfold rNode
    exact le_add_of_nonneg_right (by positivity)
  have hn := rNode_mono (show j.val ≤ j.val+1 by omega)
  have he : rNode j.val ≤ endpoint := by
    apply (rNode_mono hj).trans
    norm_num [rNode,endpoint,alpha,beta]
  exact ⟨h0,le_min hn he,min_le_right _ _⟩

theorem density_cell_integrable (j : Fin 21) :
    IntervalIntegrable density volume (rNode j.val) (cellEnd j) := by
  apply density_integrable.mono_set
  rw [uIcc_of_le scalar_interval,uIcc_of_le (cell_bounds j).2.1]
  exact Icc_subset_Icc (cell_bounds j).1 (cell_bounds j).2.2

theorem weight_nonneg (j : Fin 21) : 0 ≤ g6Weight j :=
  intervalIntegral.integral_nonneg (cell_bounds j).2.1
    (fun _ hs => density_nonneg
      ⟨(cell_bounds j).1.trans hs.1,hs.2.trans (cell_bounds j).2.2⟩)

theorem cell_intersection (j : Fin 21) :
    Ioc (2 : ℝ) endpoint ∩ Ioc (rNode j.val) (rNode (j.val+1)) =
      Ioc (rNode j.val) (cellEnd j) := by
  ext s
  simp only [mem_inter_iff,mem_Ioc,cellEnd,le_min_iff]
  constructor
  · rintro ⟨hs,hj⟩
    exact ⟨hj.1,hj.2,hs.2⟩
  · rintro ⟨hj,hjs,he⟩
    exact ⟨⟨(cell_bounds j).1.trans_lt hj,he⟩,hj,hjs⟩

theorem basis_density_integral (j : Fin 21) :
    (∫ s in (2 : ℝ)..endpoint, density s * profile (WuTarget.W03.basis j) s) =
      g6Weight j := by
  have he : (fun s => density s * profile (WuTarget.W03.basis j) s) =
      (Ioc (rNode j.val) (rNode (j.val+1))).indicator density := by
    funext s
    rw [WuTarget.W03.profile_basis]
    by_cases hc : WuTarget.W03.cell j s
    · rw [if_pos hc,indicator_of_mem
        (show s ∈ Ioc (rNode j.val) (rNode (j.val+1)) from hc),mul_one]
    · rw [if_neg hc,indicator_of_notMem
        (show s ∉ Ioc (rNode j.val) (rNode (j.val+1)) from hc),mul_zero]
  rw [he,intervalIntegral.integral_of_le scalar_interval,
    setIntegral_indicator measurableSet_Ioc,cell_intersection]
  exact (intervalIntegral.integral_of_le (cell_bounds j).2.1).symm

theorem published_basis (j : Fin 21) :
    published (WuTarget.W03.basis j) = 8*g6Weight j := by
  rw [published_density_integral,basis_density_integral]

theorem masked_expansion (w : Fin 21 → ℝ) (v : ℝ × ℝ) :
    masked publishedReducedDomain w v =
      ∑ j : Fin 21, w j * masked publishedReducedDomain (WuTarget.W03.basis j) v := by
  unfold masked
  by_cases hv : v ∈ publishedReducedDomain
  · simp only [if_pos hv,kernel,WuTarget.W03.profile_expansion w,Finset.sum_div,mul_div_assoc]
  · simp [hv]

theorem published_twentyone (w : Fin 21 → ℝ) :
    published w = 8*∑ j : Fin 21, g6Weight j * w j := by
  unfold published
  simp_rw [masked_expansion w]
  rw [integral_finsetSum _ (fun j _ => (published_integrable (WuTarget.W03.basis j)).const_mul (w j))]
  simp only [integral_const_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have h := published_basis j
  unfold published at h
  have hh := congrArg (fun t : ℝ => w j*t) h
  nlinarith only [hh]

theorem cell_end_full (j : Fin 21) (hj : j.val < 20) :
    cellEnd j = rNode (j.val+1) := by
  apply min_eq_left
  apply (rNode_mono (show j.val+1 ≤ 20 by omega)).trans
  norm_num [rNode,endpoint,alpha,beta]

theorem cell_end_last : cellEnd (20 : Fin 21) = endpoint := by
  apply min_eq_right
  norm_num [rNode,endpoint,alpha,beta]

theorem first_fourteen (j : Fin 21) (hj : j.val < 14) :
    g6Weight j = ∫ s in rNode j.val..rNode (j.val+1), lowerKernel s := by
  rw [g6Weight,cell_end_full j (by omega)]
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le (rNode_mono (show j.val ≤ j.val+1 by omega))] at hs
  apply density_lower
  apply (hs.2.trans (rNode_mono (show j.val+1 ≤ 14 by omega))).trans
  norm_num [rNode,split,alpha,beta]

theorem middle_five (j : Fin 21) (hj : 15 ≤ j.val) (hj20 : j.val < 20) :
    g6Weight j = ∫ s in rNode j.val..rNode (j.val+1), upperKernel s := by
  rw [g6Weight,cell_end_full j hj20]
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le (rNode_mono (show j.val ≤ j.val+1 by omega))] at hs
  apply density_upper
  apply le_trans (b := rNode 15) _ ((rNode_mono hj).trans hs.1)
  norm_num [rNode,split,alpha,beta]

theorem last_truncated :
    g6Weight (20 : Fin 21) = ∫ s in (4 : ℝ)..endpoint, upperKernel s := by
  rw [g6Weight,cell_end_last]
  norm_num only [rNode,Fin.val_natCast,Nat.cast_ofNat]
  norm_num
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le (show (4 : ℝ) ≤ endpoint by norm_num [endpoint,alpha,beta])] at hs
  apply density_upper
  exact le_trans (by norm_num [split,alpha,beta] : split ≤ 4) hs.1

theorem fifteenth_crossing :
    g6Weight (14 : Fin 21) =
      (∫ s in (34/10 : ℝ)..split, lowerKernel s) +
        ∫ s in split..(35/10 : ℝ), upperKernel s := by
  have hs : (34/10 : ℝ) ≤ split := breakpoints.2.2.1.le
  have ht : split ≤ (35/10 : ℝ) := breakpoints.2.2.2.1.le
  have hi (a b : ℝ) (ha : 2 ≤ a) (hab : a ≤ b) (hb : b ≤ endpoint) :
      IntervalIntegrable density volume a b := by
    apply density_integrable.mono_set
    rw [uIcc_of_le scalar_interval,uIcc_of_le hab]
    exact Icc_subset_Icc ha hb
  have hl := hi (34/10) split (by norm_num) hs
    (by norm_num [split,endpoint,alpha,beta])
  have hr := hi split (35/10) (by norm_num [split,alpha,beta]) ht
    (by norm_num [endpoint,alpha,beta])
  rw [g6Weight,cell_end_full (14 : Fin 21) (by norm_num)]
  have he1 : rNode (14 : Fin 21).val = (34/10 : ℝ) := by norm_num [rNode]
  have he2 : rNode ((14 : Fin 21).val+1) = (35/10 : ℝ) := by norm_num [rNode]
  rw [he1,he2,← intervalIntegral.integral_add_adjacent_intervals hl hr]
  congr 1
  · apply intervalIntegral.integral_congr
    intro s h
    rw [uIcc_of_le hs] at h
    exact density_lower h.2
  · apply intervalIntegral.integral_congr
    intro s h
    rw [uIcc_of_le ht] at h
    exact density_upper h.1

#print axioms published_twentyone
#print axioms first_fourteen
#print axioms fifteenth_crossing
#print axioms middle_five
#print axioms last_truncated
end WuSource.SrcSixthGain
