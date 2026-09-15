import SrcFourEnclosureCertificate

noncomputable section
namespace WuSource.SrcFourEnclosure

theorem sum_four_blocks (f : ℕ → ℝ) :
    (∑ i ∈ Finset.range 64, f i) =
      (∑ i ∈ Finset.range 16, f (0+i))+
      (∑ i ∈ Finset.range 16, f (16+i))+
      (∑ i ∈ Finset.range 16, f (32+i))+
      (∑ i ∈ Finset.range 16, f (48+i)) := by
  have h1 := Finset.sum_range_add f 48 16
  have h2 := Finset.sum_range_add f 32 16
  have h3 := Finset.sum_range_add f 16 16
  norm_num only at h1 h2 h3
  simp only [Nat.zero_add]
  linarith only [h1,h2,h3]

theorem smallLower_sum_0 :
    (∑ i ∈ Finset.range 16, smallLower (0+i)) = (2537788632/100000000 : ℝ) := by
  norm_num [Finset.sum_range_succ,smallLower]

theorem smallLower_sum_16 :
    (∑ i ∈ Finset.range 16, smallLower (16+i)) = (13993389479/100000000 : ℝ) := by
  norm_num [Finset.sum_range_succ,smallLower]

theorem smallLower_sum_32 :
    (∑ i ∈ Finset.range 16, smallLower (32+i)) = (29273562903/100000000 : ℝ) := by
  norm_num [Finset.sum_range_succ,smallLower]

theorem smallLower_sum_48 :
    (∑ i ∈ Finset.range 16, smallLower (48+i)) = (43982892303/100000000 : ℝ) := by
  norm_num [Finset.sum_range_succ,smallLower]

theorem smallLower_sum :
    (∑ i ∈ Finset.range 64, smallLower i) = (89787633317/100000000 : ℝ) := by
  rw [sum_four_blocks,smallLower_sum_0,smallLower_sum_16,smallLower_sum_32,smallLower_sum_48]
  norm_num

theorem smallUpper_sum_0 :
    (∑ i ∈ Finset.range 16, smallUpper (0+i)) = (2537790071/100000000 : ℝ) := by
  norm_num [Finset.sum_range_succ,smallUpper]

theorem smallUpper_sum_16 :
    (∑ i ∈ Finset.range 16, smallUpper (16+i)) = (13993391559/100000000 : ℝ) := by
  norm_num [Finset.sum_range_succ,smallUpper]

theorem smallUpper_sum_32 :
    (∑ i ∈ Finset.range 16, smallUpper (32+i)) = (29273563751/100000000 : ℝ) := by
  norm_num [Finset.sum_range_succ,smallUpper]

theorem smallUpper_sum_48 :
    (∑ i ∈ Finset.range 16, smallUpper (48+i)) = (43982892525/100000000 : ℝ) := by
  norm_num [Finset.sum_range_succ,smallUpper]

theorem smallUpper_sum :
    (∑ i ∈ Finset.range 64, smallUpper i) = (89787637906/100000000 : ℝ) := by
  rw [sum_four_blocks,smallUpper_sum_0,smallUpper_sum_16,smallUpper_sum_32,smallUpper_sum_48]
  norm_num

theorem largeLower_sum_0 :
    (∑ i ∈ Finset.range 16, largeLower (0+i)) = (55447477172/100000000 : ℝ) := by
  norm_num [Finset.sum_range_succ,largeLower]

theorem largeLower_sum_16 :
    (∑ i ∈ Finset.range 16, largeLower (16+i)) = (63476676911/100000000 : ℝ) := by
  norm_num [Finset.sum_range_succ,largeLower]

theorem largeLower_sum_32 :
    (∑ i ∈ Finset.range 16, largeLower (32+i)) = (68877450989/100000000 : ℝ) := by
  norm_num [Finset.sum_range_succ,largeLower]

theorem largeLower_sum_48 :
    (∑ i ∈ Finset.range 16, largeLower (48+i)) = (71729057684/100000000 : ℝ) := by
  norm_num [Finset.sum_range_succ,largeLower]

theorem largeLower_sum :
    (∑ i ∈ Finset.range 64, largeLower i) = (259530662756/100000000 : ℝ) := by
  rw [sum_four_blocks,largeLower_sum_0,largeLower_sum_16,largeLower_sum_32,largeLower_sum_48]
  norm_num

theorem largeUpper_sum_0 :
    (∑ i ∈ Finset.range 16, largeUpper (0+i)) = (55447477231/100000000 : ℝ) := by
  norm_num [Finset.sum_range_succ,largeUpper]

theorem largeUpper_sum_16 :
    (∑ i ∈ Finset.range 16, largeUpper (16+i)) = (63476676934/100000000 : ℝ) := by
  norm_num [Finset.sum_range_succ,largeUpper]

theorem largeUpper_sum_32 :
    (∑ i ∈ Finset.range 16, largeUpper (32+i)) = (68877451005/100000000 : ℝ) := by
  norm_num [Finset.sum_range_succ,largeUpper]

theorem largeUpper_sum_48 :
    (∑ i ∈ Finset.range 16, largeUpper (48+i)) = (71729057700/100000000 : ℝ) := by
  norm_num [Finset.sum_range_succ,largeUpper]

theorem largeUpper_sum :
    (∑ i ∈ Finset.range 64, largeUpper i) = (259530662870/100000000 : ℝ) := by
  rw [sum_four_blocks,largeUpper_sum_0,largeUpper_sum_16,largeUpper_sum_32,largeUpper_sum_48]
  norm_num

end WuSource.SrcFourEnclosure
