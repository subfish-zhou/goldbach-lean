import SrcSixthGainWeights
import W01WeightedGain

noncomputable section
namespace WuSource.SrcSixthGain
open Real Set MeasureTheory QuarterTrim DirectFiniteF6 Wu08G6High
open Wu08G6TableGeometryRecovery Wu2008DoubleSieve NodeExtension
open scoped Classical BigOperators

def paperKernel (p : ℝ → ℝ) (t s : ℝ) : ℝ :=
  p s/(t*s*(1-2*t-2*alpha*s))

def paperG6 (p : ℝ → ℝ) : ℝ :=
  8*(∫ t in alpha..beta,
      ∫ s in ((2*beta-t)/alpha)..((1/2-beta-t)/alpha), paperKernel p t s) +
  8*(∫ t in alpha..(3*alpha/2),
      ∫ s in ((3*alpha-t)/alpha)..((2*beta-t)/alpha), paperKernel p t s)

def rectangleG6 (p : ℝ → ℝ) : ℝ :=
  4*(∫ t in alpha..beta,
      ∫ y in beta..(1/2-2*beta), kernel p t y) +
  4*(∫ t in alpha..(3*alpha/2),
      ∫ y in (1/2-2*beta)..(1/2-3*alpha), kernel p t y)

theorem paper_inner (p : ℝ → ℝ) (t a b : ℝ) :
    2*(∫ s in ((1/2-t-b)/alpha)..((1/2-t-a)/alpha), paperKernel p t s) =
      ∫ y in a..b, kernel p t y := by
  have ha : alpha ≠ 0 := alpha_pos.ne'
  have h := intervalIntegral.integral_comp_sub_div (paperKernel p t) ha ((1/2-t)/alpha)
    (a := a) (b := b)
  rw [show (1/2-t)/alpha-b/alpha=(1/2-t-b)/alpha by ring,
    show (1/2-t)/alpha-a/alpha=(1/2-t-a)/alpha by ring,smul_eq_mul] at h
  have hk : (fun y => paperKernel p t ((1/2-t)/alpha-y/alpha)) =
      fun y => (alpha/2)*kernel p t y := by
    funext y
    rw [show (1/2-t)/alpha-y/alpha=(1/2-t-y)/alpha by ring]
    unfold paperKernel kernel u
    rw [show 1-2*t-2*alpha*((1/2-t-y)/alpha)=2*y by field_simp [ha]; ring]
    field_simp [ha]
  rw [hk,intervalIntegral.integral_const_mul] at h
  apply mul_left_cancel₀ ha
  linarith only [h]

theorem paper_eq_rectangles (p : ℝ → ℝ) : paperG6 p = rectangleG6 p := by
  have hA (t : ℝ) := paper_inner p t beta (1/2-2*beta)
  have hB (t : ℝ) := paper_inner p t (1/2-2*beta) (1/2-3*alpha)
  simp_rw [show ∀ t : ℝ, (1/2-t-(1/2-2*beta))/alpha=(2*beta-t)/alpha by
    intro t; ring] at hA hB
  simp_rw [show ∀ t : ℝ, (1/2-t-(1/2-3*alpha))/alpha=(3*alpha-t)/alpha by
    intro t; ring] at hB
  simp_rw [show ∀ t : ℝ, (1/2-t-beta)/alpha=(1/2-beta-t)/alpha by
    intro t; ring] at hA
  have hAi := intervalIntegral.integral_congr (μ := volume) (a := alpha) (b := beta) (fun t _ => hA t)
  have hBi := intervalIntegral.integral_congr (μ := volume) (a := alpha) (b := 3*alpha/2) (fun t _ => hB t)
  rw [intervalIntegral.integral_const_mul] at hAi hBi
  unfold paperG6 rectangleG6
  linarith only [hAi,hBi]

theorem profile_actual {w : Fin 21 → ℝ} {delta s : ℝ}
    (hd : 0 < delta) (hdhi : delta ≤ 1/10)
    (hw : ∀ j, w j ≤ wuImprovementLimit false delta (rNode (j.val+1)))
    (hs : s ∈ Icc 2 endpoint) :
    profile w s ≤ wuImprovementLimit false delta s := by
  have hm : AntitoneOn (wuImprovementLimit false delta) (Icc 2 (41/10)) :=
    (wuImprovementLimit_lower_antitone hd hdhi).mono
      (Icc_subset_Icc le_rfl (by norm_num))
  have hse : endpoint ≤ (41/10 : ℝ) := breakpoints.2.2.2.2.2.le
  apply StaircaseShrink.eval_le_of_nodes (rows w) _ hm
    ?_ ⟨hs.1,hs.2.trans hse⟩ le_rfl
    (wuImprovementLimit_nonneg false hd (by linarith) (by linarith [hs.1])
      (by linarith [hs.2]))
  intro r hr
  refine ⟨row_endpoint w hr,?_⟩
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp hr
  change w j ≤ wuImprovementLimit false delta (originalRow j).2.1
  rw [originalRow_node]
  exact hw j

def originalReduced (delta : ℝ) : ℝ :=
  8*∫ s in (2 : ℝ)..endpoint, density s * wuImprovementLimit false delta s

theorem original_reduced_lower {w : Fin 21 → ℝ} {delta : ℝ}
    (hd : 0 < delta) (hdhi : delta ≤ 1/10)
    (hw : ∀ j, w j ≤ wuImprovementLimit false delta (rNode (j.val+1))) :
    8*(∑ j : Fin 21, g6Weight j*w j) ≤ originalReduced delta := by
  have hm := (wuImprovementLimit_lower_antitone hd hdhi).mono
    (show Icc 2 endpoint ⊆ Icc (2 : ℝ) 10 from
      Icc_subset_Icc le_rfl (by norm_num [endpoint,alpha,beta]))
  have hm' : AntitoneOn (wuImprovementLimit false delta) (uIcc 2 endpoint) := by
    simpa only [uIcc_of_le scalar_interval] using hm
  have hi : IntervalIntegrable (wuImprovementLimit false delta) volume 2 endpoint :=
    hm'.intervalIntegrable
  have hp : IntervalIntegrable (fun s => density s*wuImprovementLimit false delta s)
      volume 2 endpoint := by
    have h := hi.mul_continuousOn
      (show ContinuousOn density (uIcc 2 endpoint) by
        simpa only [uIcc_of_le scalar_interval] using density_continuous)
    simpa only [mul_comm] using h
  have hb (j : Fin 21) : IntervalIntegrable
      (fun s => density s * profile (WuTarget.W03.basis j) s) volume 2 endpoint := by
    have h := density_integrable.indicator (s := Ioc (rNode j.val) (rNode (j.val+1)))
      measurableSet_Ioc
    apply h.congr
    intro s _
    rw [WuTarget.W03.profile_basis]
    by_cases hc : WuTarget.W03.cell j s
    · rw [if_pos hc,indicator_of_mem
        (show s ∈ Ioc (rNode j.val) (rNode (j.val+1)) from hc),mul_one]
    · rw [if_neg hc,indicator_of_notMem
        (show s ∉ Ioc (rNode j.val) (rNode (j.val+1)) from hc),mul_zero]
  have hwInt : IntervalIntegrable (fun s => density s*profile w s) volume 2 endpoint := by
    have hiw := IntervalIntegrable.sum (s := Finset.univ)
      (fun j _ => (hb j).const_mul (w j))
    apply hiw.congr
    intro s _
    rw [WuTarget.W03.profile_expansion w,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [← published_twentyone,published_density_integral]
  exact mul_le_mul_of_nonneg_left
    (intervalIntegral.integral_mono_on scalar_interval hwInt hp
      (fun s hs => mul_le_mul_of_nonneg_left (profile_actual hd hdhi hw hs) (density_nonneg hs)))
    (by norm_num)

#print axioms paper_eq_rectangles
#print axioms profile_actual
#print axioms original_reduced_lower
#check SixthSlotAssembly.SixthLower
#print Wu08TerminalAlignment.sixthMain
end WuSource.SrcSixthGain
