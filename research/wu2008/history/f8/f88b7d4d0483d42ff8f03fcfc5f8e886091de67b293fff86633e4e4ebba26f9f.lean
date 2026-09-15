import WRMapMFirstConstants

noncomputable section
open Real Set MeasureTheory
open scoped Interval
open Wu2008DoubleSieve Wu08OriginalFirstSteps

namespace WuPaper.RMapMFirst

def lowKernel (t : ℝ) : ℝ := 1 / denominator t

def middleKernel (t : ℝ) : ℝ :=
  (1 + ∫ u in (2 : ℝ)..(t - 1), log (u - 1) / u) / denominator t

def highKernel (t : ℝ) : ℝ :=
  (1 + (∫ u in (2 : ℝ)..(t - 1), log (u - 1) / u) +
    (∫ u in (4 : ℝ)..(t - 1),
      (∫ v in (3 : ℝ)..(u - 1),
        (∫ w in (2 : ℝ)..(v - 1), log (w - 1) / w) / v) / u)) / denominator t

def lowPiece : ℝ := ∫ t in bottom..(3 : ℝ), lowKernel t
def middlePiece : ℝ := ∫ t in (3 : ℝ)..5, middleKernel t
def highPiece : ℝ := ∫ t in (5 : ℝ)..top, highKernel t

theorem kernel_low {t : ℝ} (ht : t ∈ Icc bottom 3) :
    originalKernel t = lowKernel t := by
  unfold originalKernel lowKernel
  rw [wuUpperCoefficient,
    jr1965F_normalized_initial (by norm_num [bottom] at *; linarith [ht.1]) ht.2]

theorem kernel_middle {t : ℝ} (ht : t ∈ Icc 3 5) :
    originalKernel t = middleKernel t := by
  unfold originalKernel middleKernel
  rw [A_middle_original ht.1 ht.2]

theorem kernel_high {t : ℝ} (ht : t ∈ Icc 5 top) :
    originalKernel t = highKernel t := by
  unfold originalKernel highKernel
  rw [A_high_original ht.1 (by norm_num [top] at *; linarith [ht.2])]

theorem original_piece_integrable :
    IntervalIntegrable lowKernel volume bottom 3 ∧
    IntervalIntegrable middleKernel volume 3 5 ∧
    IntervalIntegrable highKernel volume 5 top := by
  refine ⟨?_, ?_, ?_⟩
  · apply IntervalIntegrable.congr _
      (kernel_integrable le_rfl (by norm_num [bottom]) (by norm_num [top]))
    intro t ht
    rw [uIoc_of_le (by norm_num [bottom] : bottom ≤ 3)] at ht
    exact kernel_low ⟨ht.1.le, ht.2⟩
  · apply IntervalIntegrable.congr _
      (kernel_integrable (by norm_num [bottom]) (by norm_num : (3 : ℝ) ≤ 5)
        (by norm_num [top]))
    intro t ht
    rw [uIoc_of_le (by norm_num : (3 : ℝ) ≤ 5)] at ht
    exact kernel_middle ⟨ht.1.le, ht.2⟩
  · apply IntervalIntegrable.congr _
      (kernel_integrable (by norm_num [bottom]) (by norm_num [top] : (5 : ℝ) ≤ top)
        le_rfl)
    intro t ht
    rw [uIoc_of_le (by norm_num [top] : (5 : ℝ) ≤ top)] at ht
    exact kernel_high ⟨ht.1.le, ht.2⟩

theorem original_piece_equalities :
    (∫ t in bottom..(3 : ℝ), originalKernel t) = lowPiece ∧
    (∫ t in (3 : ℝ)..5, originalKernel t) = middlePiece ∧
    (∫ t in (5 : ℝ)..top, originalKernel t) = highPiece := by
  refine ⟨?_, ?_, ?_⟩
  · apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le (by norm_num [bottom] : bottom ≤ 3)] at ht
    exact kernel_low ht
  · apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le (by norm_num : (3 : ℝ) ≤ 5)] at ht
    exact kernel_middle ht
  · apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le (by norm_num [top] : (5 : ℝ) ≤ top)] at ht
    exact kernel_high ht

theorem C3_partition : C3 = 8 * (lowPiece + middlePiece + highPiece) := by
  have h0 := kernel_integrable (l := bottom) (r := 3) le_rfl
    (by norm_num [bottom]) (by norm_num [top])
  have h1 := kernel_integrable (l := 3) (r := 5) (by norm_num [bottom])
    (by norm_num) (by norm_num [top])
  have h2 := kernel_integrable (l := 5) (r := top) (by norm_num [bottom])
    (by norm_num [top]) le_rfl
  have h01 := intervalIntegral.integral_add_adjacent_intervals h0 h1
  have h012 := intervalIntegral.integral_add_adjacent_intervals (h0.trans h1) h2
  rw [original_piece_equalities.1, original_piece_equalities.2.1] at h01
  rw [original_piece_equalities.2.2, ← h01] at h012
  exact congrArg (fun x : ℝ => 8 * x) h012.symm

theorem C4_partition : C4 = 8 * (middlePiece + highPiece) := by
  have h1 := kernel_integrable (l := 3) (r := 5) (by norm_num [bottom])
    (by norm_num) (by norm_num [top])
  have h2 := kernel_integrable (l := 5) (r := top) (by norm_num [bottom])
    (by norm_num [top]) le_rfl
  have h12 := intervalIntegral.integral_add_adjacent_intervals h1 h2
  rw [original_piece_equalities.2.1, original_piece_equalities.2.2] at h12
  exact congrArg (fun x : ℝ => 8 * x) h12.symm

theorem C34_exact_combination :
    C3 + C4 = 8 * lowPiece + 16 * (middlePiece + highPiece) := by
  rw [C3_partition, C4_partition]
  ring

theorem kernel_join_values :
    lowKernel 3 = middleKernel 3 ∧ middleKernel 5 = highKernel 5 := by
  constructor
  · exact (kernel_low (by norm_num [bottom])).symm.trans
      (kernel_middle (by norm_num))
  · exact (kernel_middle (by norm_num)).symm.trans
      (kernel_high (by norm_num [top]))

theorem piece_nonnegative : 0 ≤ lowPiece ∧ 0 ≤ middlePiece ∧ 0 ≤ highPiece := by
  rw [← original_piece_equalities.1, ← original_piece_equalities.2.1,
    ← original_piece_equalities.2.2]
  refine ⟨?_, ?_, ?_⟩
  · exact intervalIntegral.integral_nonneg (by norm_num [bottom])
      (fun t ht => kernel_nonnegative ⟨ht.1, ht.2.trans (by norm_num [top])⟩)
  · exact intervalIntegral.integral_nonneg (by norm_num)
      (fun t ht => kernel_nonnegative
        ⟨(by norm_num [bottom] : bottom ≤ 3).trans ht.1,
          ht.2.trans (by norm_num [top])⟩)
  · exact intervalIntegral.integral_nonneg (by norm_num [top])
      (fun t ht => kernel_nonnegative
        ⟨(by norm_num [bottom] : bottom ≤ 5).trans ht.1, ht.2⟩)

#check @lowKernel
#print axioms lowKernel
#check @middleKernel
#print axioms middleKernel
#check @highKernel
#print axioms highKernel
#check @lowPiece
#print axioms lowPiece
#check @middlePiece
#print axioms middlePiece
#check @highPiece
#print axioms highPiece
#check @kernel_low
#print axioms kernel_low
#check @kernel_middle
#print axioms kernel_middle
#check @kernel_high
#print axioms kernel_high
#check @original_piece_integrable
#print axioms original_piece_integrable
#check @original_piece_equalities
#print axioms original_piece_equalities
#check @C3_partition
#print axioms C3_partition
#check @C4_partition
#print axioms C4_partition
#check @C34_exact_combination
#print axioms C34_exact_combination
#check @kernel_join_values
#print axioms kernel_join_values
#check @piece_nonnegative
#print axioms piece_nonnegative

end WuPaper.RMapMFirst
