import WRMapMFirstPartition

noncomputable section
open Real Set MeasureTheory
open scoped Interval
open Wu2008DoubleSieve

namespace WuPaper.RMapMFirst

theorem low_primitive_derivative {t : ℝ} (ht : t ∈ Icc bottom 3) :
    HasDerivAt (fun x : ℝ => log x - log (1 - 2 * alpha * x)) (lowKernel t) t := by
  have hd := denominator_positive ⟨ht.1, ht.2.trans (by norm_num [top])⟩
  have h := (hasDerivAt_log hd.1.ne').sub
    ((((hasDerivAt_id t).const_mul (2 * alpha)).const_sub 1).log hd.2.1.ne')
  have ht0 := hd.1.ne'
  have hf := hd.2.1.ne'
  have hf' : 1 - t * 2 * alpha ≠ 0 := by
    convert hf using 1
    ring
  convert h using 1 <;>
    first | rfl | (dsimp [lowKernel, denominator]; field_simp [ht0, hf, hf']; ring)

theorem lowPiece_exact_log : lowPiece = log (1200 / 727 : ℝ) := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := bottom) (b := (3 : ℝ))
    (fun t ht => low_primitive_derivative
      (by rwa [uIcc_of_le (by norm_num [bottom] : bottom ≤ 3)] at ht))
    original_piece_integrable.1
  change lowPiece = _ at h
  have hd3 : (0 : ℝ) < 1 - 2 * alpha * 3 := by
    norm_num [alpha, truncatedSixthLowerAlpha]
  have hdb : (0 : ℝ) < 1 - 2 * alpha * bottom := by
    norm_num [alpha, bottom, truncatedSixthLowerAlpha]
  have hb : (0 : ℝ) < bottom := by norm_num [bottom]
  calc
    lowPiece = (log 3 - log (1 - 2 * alpha * 3)) -
        (log bottom - log (1 - 2 * alpha * bottom)) := h
    _ = log ((3 / (1 - 2 * alpha * 3)) /
        (bottom / (1 - 2 * alpha * bottom))) := by
      rw [log_div (div_pos (by norm_num) hd3).ne' (div_pos hb hdb).ne',
        log_div (by norm_num : (3 : ℝ) ≠ 0) hd3.ne', log_div hb.ne' hdb.ne']
    _ = log (1200 / 727 : ℝ) := by
      congr 1
      norm_num [alpha, bottom, truncatedSixthLowerAlpha]

theorem C3_minus_C4_original : C3 - C4 = 8 * log (1200 / 727 : ℝ) := by
  rw [C3_partition, C4_partition, lowPiece_exact_log]
  ring

#check @low_primitive_derivative
#print axioms low_primitive_derivative
#check @lowPiece_exact_log
#print axioms lowPiece_exact_log
#check @C3_minus_C4_original
#print axioms C3_minus_C4_original

end WuPaper.RMapMFirst
