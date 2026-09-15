import RMapMSixthGainReduction

noncomputable section
namespace WuPaper.RMapMSixth
open Real Set MeasureTheory QuarterTrim Wu2008DoubleSieve NodeExtension
open WuSource.SrcSixthGain
open scoped Interval BigOperators

theorem g6_kernel_factors {s : ℝ} (hs : s ∈ Icc 2 endpoint) :
    0 < s ∧ 0 < 1-2*alpha*s ∧
      2*beta ≤ 1-2*alpha-2*alpha*s ∧
      2*alpha ≤ 1-2*beta-2*alpha*s := by
  have hb : 0 < beta := by norm_num [beta]
  have ht := (le_div_iff₀ alpha_pos).mp hs.2
  refine ⟨by linarith [hs.1],by linarith [alpha_pos],by linarith,by linarith⟩

theorem g6_kernel_nonnegative {s : ℝ} (hs : s ∈ Icc 2 endpoint) :
    0 ≤ lowerKernel s ∧ 0 ≤ upperKernel s := by
  have hg := g6_kernel_factors hs
  have ha := alpha_pos
  have hb : 0 < beta := by norm_num [beta]
  have hp : 0 < 1-2*beta-2*alpha*s := (by positivity : (0 : ℝ) < 2*alpha).trans_le hg.2.2.2
  have hq : 0 < 1-2*alpha-2*alpha*s := (by positivity : (0 : ℝ) < 2*beta).trans_le hg.2.2.1
  have hl : 1 ≤ beta*(1-2*alpha-2*alpha*s)/(alpha*(1-2*beta-2*alpha*s)) := by
    apply (le_div_iff₀ (mul_pos alpha_pos hp)).mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr envelope_bounds.1) hg.2.1.le]
  have hu : 1 ≤ (1-2*alpha-2*alpha*s)*(1-2*beta-2*alpha*s)/(4*alpha*beta) := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 4*alpha*beta)).mpr
    have h := mul_le_mul hg.2.2.1 hg.2.2.2 (by positivity : (0 : ℝ) ≤ 2*alpha) hq.le
    nlinarith only [h]
  exact ⟨div_nonneg (log_nonneg hl) (mul_pos hg.1 hg.2.1).le,
    div_nonneg (log_nonneg hu) (mul_pos hg.1 hg.2.1).le⟩

theorem g6_cells_cover {s : ℝ} (hs : s ∈ Ioc 2 endpoint) :
    ∃! j : Fin 21, s ∈ Ioc (rNode j.val) (cellEnd j) := by
  classical
  have he : s ≤ rNode (20+1) := hs.2.trans (by norm_num [endpoint,rNode,alpha,beta])
  have hex : ∃ n : ℕ, s ≤ rNode (n+1) := ⟨20,he⟩
  let n := Nat.find hex
  have hn : n ≤ 20 := Nat.find_min' hex he
  have hlow : rNode n < s := by
    by_cases hn0 : n = 0
    · simpa only [hn0,rNode,Nat.cast_zero,zero_div,add_zero] using hs.1
    · have hfail := Nat.find_min hex (show n-1 < n by omega)
      rw [Nat.sub_add_cancel (show 1 ≤ n by omega)] at hfail
      exact lt_of_not_ge hfail
  let j : Fin 21 := ⟨n,by omega⟩
  have hj : s ∈ Ioc (rNode j.val) (cellEnd j) :=
    ⟨hlow,le_min (Nat.find_spec hex) hs.2⟩
  refine ⟨j,hj,?_⟩
  intro k hk
  exact WuTarget.W03.cell_unique
    ⟨hk.1,hk.2.trans (min_le_left _ _)⟩
    ⟨hj.1,hj.2.trans (min_le_left _ _)⟩

theorem g6_twentyone_chain {w : Fin 21 → ℝ} {delta : ℝ}
    (hd : 0 < delta) (hdhi : delta ≤ 1/10)
    (hw : ∀ j, w j ≤ wuImprovementLimit false delta (rNode (j.val+1))) :
    8*(∑ j : Fin 21, g6Weight j*w j) ≤ originalReduced delta ∧
      originalReduced delta ≤ paperG6 (wuImprovementLimit false delta) :=
  ⟨original_reduced_lower hd hdhi hw,g6_original_reduced_le_whole hd hdhi⟩

theorem g6_directed_weight_node_errors {a e b d : Fin 21 → ℝ} {delta : ℝ}
    (hd : 0 < delta) (hdhi : delta ≤ 1/10)
    (he : ∀ j, |g6Weight j-a j| ≤ e j)
    (hn : ∀ j, 0 ≤ b j-d j)
    (hb : ∀ j, b j-d j ≤ wuImprovementLimit false delta (rNode (j.val+1))) :
    8*(∑ j : Fin 21, (a j-e j)*(b j-d j)) ≤
      paperG6 (wuImprovementLimit false delta) := by
  have hw (j : Fin 21) : a j-e j ≤ g6Weight j := by
    have h := (abs_le.mp (he j)).1
    linarith only [h]
  have hsum := Finset.sum_le_sum (s := Finset.univ)
    (fun j _ => mul_le_mul_of_nonneg_right (hw j) (hn j))
  have hchain := g6_twentyone_chain hd hdhi hb
  exact (mul_le_mul_of_nonneg_left hsum (by norm_num : (0 : ℝ) ≤ 8)).trans
    (hchain.1.trans hchain.2)

theorem g6_fifteenth_error {qLeft qRight eLeft eRight : ℝ}
    (hl : |(∫ s in (34/10 : ℝ)..split, lowerKernel s)-qLeft| ≤ eLeft)
    (hr : |(∫ s in split..(35/10 : ℝ), upperKernel s)-qRight| ≤ eRight) :
    |g6Weight (14 : Fin 21)-(qLeft+qRight)| ≤ eLeft+eRight := by
  rw [fifteenth_crossing]
  have h := abs_add_le
    ((∫ s in (34/10 : ℝ)..split, lowerKernel s)-qLeft)
    ((∫ s in split..(35/10 : ℝ), upperKernel s)-qRight)
  rw [show
    ((∫ s in (34/10 : ℝ)..split, lowerKernel s)-qLeft) +
      ((∫ s in split..(35/10 : ℝ), upperKernel s)-qRight) =
    ((∫ s in (34/10 : ℝ)..split, lowerKernel s) +
      (∫ s in split..(35/10 : ℝ), upperKernel s))-(qLeft+qRight) by ring] at h
  exact h.trans (add_le_add hl hr)

#check @g6_kernel_factors
#check @g6_kernel_nonnegative
#check @g6_cells_cover
#check @g6_twentyone_chain
#check @g6_directed_weight_node_errors
#check @g6_fifteenth_error
#print axioms g6_kernel_factors
#print axioms g6_kernel_nonnegative
#print axioms g6_cells_cover
#print axioms g6_twentyone_chain
#print axioms g6_directed_weight_node_errors
#print axioms g6_fifteenth_error
end WuPaper.RMapMSixth
