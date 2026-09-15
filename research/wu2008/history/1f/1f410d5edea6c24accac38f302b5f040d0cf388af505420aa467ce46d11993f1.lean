import WRMapMSigmaKernel
import NodeTransfer

noncomputable section
namespace WuPaper.RMapMSigma
open Real Set MeasureTheory NodeExtension Wu2008DoubleSieve
open scoped Interval BigOperators

def coefficientLeft (i : ℕ) : ℝ := if i = 2 then 1 else rNode (i - 1)

def sourceCoefficient (i j : ℕ) : ℝ :=
  ∫ t in coefficientLeft i..rNode i, upperKernel (rNode j) t

theorem sourceCoefficient_first (j : ℕ) :
    sourceCoefficient 2 j =
      ∫ t in (1 : ℝ)..rNode 2,
        sigma0 t / t * log (4 / (rNode j - 1)) +
          (Icc (rNode j - 2) 3).indicator (fun _ => (1 : ℝ)) t / t *
            log ((t + 1) / (rNode j - 1)) := by
  simp only [sourceCoefficient, coefficientLeft, ite_true, upperKernel]

theorem sourceCoefficient_other {i : ℕ} (hi : 3 ≤ i) (j : ℕ) :
    sourceCoefficient i j =
      ∫ t in rNode (i - 1)..rNode i,
        sigma0 t / t * log (4 / (rNode j - 1)) +
          (Icc (rNode j - 2) 3).indicator (fun _ => (1 : ℝ)) t / t *
            log ((t + 1) / (rNode j - 1)) := by
  simp only [sourceCoefficient, coefficientLeft, if_neg (by omega : i ≠ 2), upperKernel]

theorem coefficient_cell_bounds {i : ℕ} (hi : 2 ≤ i) (hi10 : i ≤ 10) :
    1 ≤ coefficientLeft i ∧ coefficientLeft i ≤ rNode i ∧ rNode i ≤ 3 := by
  have hr := rNode_mono hi10
  norm_num [rNode] at hr
  refine ⟨?_, ?_, hr⟩
  · unfold coefficientLeft
    split_ifs
    · exact le_rfl
    · exact (rNode_bounds (show i - 1 ≤ 29 by omega)).1
  · unfold coefficientLeft
    split_ifs
    · exact (rNode_bounds (show i ≤ 29 by omega)).1
    · exact rNode_mono (by omega)

theorem extension_node_bounds {j : ℕ} (hj : 11 ≤ j) (hj29 : j ≤ 29) :
    rNode j ∈ Icc 3 5 := by
  have hlo := rNode_mono (show 10 ≤ j by omega)
  norm_num [rNode] at hlo
  exact ⟨hlo, (rNode_bounds hj29).2⟩

theorem sourceCoefficient_nonneg {i j : ℕ} (hi : 2 ≤ i) (hi10 : i ≤ 10)
    (hj : 11 ≤ j) (hj29 : j ≤ 29) : 0 ≤ sourceCoefficient i j := by
  have hb := coefficient_cell_bounds hi hi10
  apply intervalIntegral.integral_nonneg hb.2.1
  intro t ht
  exact upperKernel_nonneg (extension_node_bounds hj hj29)
    ⟨hb.1.trans ht.1, ht.2.trans hb.2.2⟩

theorem coefficient_integral_partition {f : ℝ → ℝ}
    (hf : IntervalIntegrable f volume 1 3) :
    (∑ i ∈ Finset.Icc 2 10, ∫ t in coefficientLeft i..rNode i, f t) =
      ∫ t in (1 : ℝ)..3, f t := by
  have h23 : rNode 2 ≤ (3 : ℝ) := by norm_num [rNode]
  have h12 : (1 : ℝ) ≤ rNode 2 := by norm_num [rNode]
  have h10 : rNode 10 = (3 : ℝ) := by norm_num [rNode]
  have subint (a b : ℝ) (ha : 1 ≤ a) (hab : a ≤ b) (hb : b ≤ 3) :
      IntervalIntegrable f volume a b := by
    apply hf.mono_set
    rw [uIcc_of_le hab, uIcc_of_le (by norm_num : (1 : ℝ) ≤ 3)]
    exact Icc_subset_Icc ha hb
  have hsum := grid_integral_sum (f := f) (a := 2) (n := 10) (by omega)
    (fun i hi hi10 => subint _ _ h12 (rNode_mono hi)
      (by have h := rNode_mono hi10; simpa only [h10] using h))
  have hset : Finset.Icc (2 : ℕ) 10 = insert 2 (Finset.Icc 3 10) := by
    ext i
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  rw [hset, Finset.sum_insert (by norm_num : (2 : ℕ) ∉ Finset.Icc 3 10)]
  have he : (∑ i ∈ Finset.Icc 3 10, ∫ t in coefficientLeft i..rNode i, f t) =
      ∑ i ∈ Finset.Icc 3 10, ∫ t in rNode (i - 1)..rNode i, f t := by
    apply Finset.sum_congr rfl
    intro i hi
    simp only [coefficientLeft, if_neg (by have := (Finset.mem_Icc.mp hi).1; omega : i ≠ 2)]
  rw [he, hsum, h10]
  simp only [coefficientLeft, ite_true]
  exact intervalIntegral.integral_add_adjacent_intervals
    (subint _ _ le_rfl h12 h23) (subint _ _ h12 h23 le_rfl)

theorem coefficient_cell_lower {δ : ℝ} (hd : 0 < δ) (hdhi : δ ≤ 1 / 10)
    {i j : ℕ} (hi : 2 ≤ i) (hi10 : i ≤ 10) (hj : 11 ≤ j) (hj29 : j ≤ 29) :
    sourceCoefficient i j * wuImprovementLimit true δ (rNode i) ≤
      ∫ t in coefficientLeft i..rNode i,
        wuImprovementLimit true δ t * upperKernel (rNode j) t := by
  have hb := coefficient_cell_bounds hi hi10
  have hs := extension_node_bounds hj hj29
  have hiH := upperKernel_integrable
    (wuImprovementLimit_intervalIntegrable true hd (by linarith : δ < 1 / 2)
      (by norm_num) (by norm_num) (by norm_num)) hs
  have hiK : IntervalIntegrable (upperKernel (rNode j)) volume 1 3 := by
    simpa only [one_mul] using upperKernel_integrable
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume 1 3) hs
  have hsub : uIcc (coefficientLeft i) (rNode i) ⊆ uIcc (1 : ℝ) 3 := by
    rw [uIcc_of_le hb.2.1, uIcc_of_le (by norm_num : (1 : ℝ) ≤ 3)]
    exact Icc_subset_Icc hb.1 hb.2.2
  rw [sourceCoefficient, ← intervalIntegral.integral_mul_const]
  apply intervalIntegral.integral_mono_on hb.2.1
    ((hiK.mono_set hsub).mul_const _) (hiH.mono_set hsub)
  intro t ht
  rw [mul_comm (upperKernel _ _)]
  apply mul_le_mul_of_nonneg_right
  · exact wuImprovementLimit_upper_antitone hd hdhi
      ⟨hb.1.trans ht.1, ht.2.trans (hb.2.2.trans (by norm_num))⟩
      ⟨hb.1.trans hb.2.1, hb.2.2.trans (by norm_num)⟩ ht.2
  · exact upperKernel_nonneg hs ⟨hb.1.trans ht.1, ht.2.trans hb.2.2⟩

theorem equation310 {δ : ℝ} (hd : 0 < δ) (hdhi : δ ≤ 1 / 10)
    {j : ℕ} (hj : 11 ≤ j) (hj29 : j ≤ 29) :
    (∑ i ∈ Finset.Icc 2 10, sourceCoefficient i j *
      wuImprovementLimit true δ (rNode i)) ≤ wuImprovementLimit true δ (rNode j) := by
  have hm := Finset.sum_le_sum (s := Finset.Icc 2 10) (fun i hi =>
    coefficient_cell_lower hd hdhi (Finset.mem_Icc.mp hi).1
      (Finset.mem_Icc.mp hi).2 hj hj29)
  rw [coefficient_integral_partition (upperKernel_integrable
    (wuImprovementLimit_intervalIntegrable true hd (by linarith : δ < 1 / 2)
      (by norm_num) (by norm_num) (by norm_num)) (extension_node_bounds hj hj29))] at hm
  exact hm.trans (lemma62 hd hdhi (extension_node_bounds hj hj29))

theorem equation310_input_lower {δ : ℝ} (hd : 0 < δ) (hdhi : δ ≤ 1 / 10)
    {Y : ℕ → ℝ} (hY : ∀ i, 2 ≤ i → i ≤ 10 →
      Y i ≤ wuImprovementLimit true δ (rNode i))
    {j : ℕ} (hj : 11 ≤ j) (hj29 : j ≤ 29) :
    (∑ i ∈ Finset.Icc 2 10, sourceCoefficient i j * Y i) ≤
      wuImprovementLimit true δ (rNode j) := by
  apply le_trans _ (equation310 hd hdhi hj hj29)
  apply Finset.sum_le_sum
  intro i hi
  have hb := Finset.mem_Icc.mp hi
  exact mul_le_mul_of_nonneg_left (hY i hb.1 hb.2)
    (sourceCoefficient_nonneg hb.1 hb.2 hj hj29)

theorem equation310_uniform :
    ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 10 → ∀ j : ℕ, 11 ≤ j → j ≤ 29 →
      (∑ i ∈ Finset.Icc 2 10, sourceCoefficient i j *
        wuImprovementLimit true δ (rNode i)) ≤ wuImprovementLimit true δ (rNode j) :=
  fun _ hd hdhi _ hj hj29 => equation310 hd hdhi hj hj29

end WuPaper.RMapMSigma

#check @WuPaper.RMapMSigma.coefficientLeft
#check @WuPaper.RMapMSigma.sourceCoefficient
#check @WuPaper.RMapMSigma.sourceCoefficient_first
#check @WuPaper.RMapMSigma.sourceCoefficient_other
#check @WuPaper.RMapMSigma.coefficient_cell_bounds
#check @WuPaper.RMapMSigma.extension_node_bounds
#check @WuPaper.RMapMSigma.sourceCoefficient_nonneg
#check @WuPaper.RMapMSigma.coefficient_integral_partition
#check @WuPaper.RMapMSigma.coefficient_cell_lower
#check @WuPaper.RMapMSigma.equation310
#check @WuPaper.RMapMSigma.equation310_input_lower
#check @WuPaper.RMapMSigma.equation310_uniform
#print axioms WuPaper.RMapMSigma.coefficientLeft
#print axioms WuPaper.RMapMSigma.sourceCoefficient
#print axioms WuPaper.RMapMSigma.sourceCoefficient_first
#print axioms WuPaper.RMapMSigma.sourceCoefficient_other
#print axioms WuPaper.RMapMSigma.coefficient_cell_bounds
#print axioms WuPaper.RMapMSigma.extension_node_bounds
#print axioms WuPaper.RMapMSigma.sourceCoefficient_nonneg
#print axioms WuPaper.RMapMSigma.coefficient_integral_partition
#print axioms WuPaper.RMapMSigma.coefficient_cell_lower
#print axioms WuPaper.RMapMSigma.equation310
#print axioms WuPaper.RMapMSigma.equation310_input_lower
#print axioms WuPaper.RMapMSigma.equation310_uniform
