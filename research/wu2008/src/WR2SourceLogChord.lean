import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

noncomputable section
namespace WuPaper.SourceLogChord
open Real Set MeasureTheory
open scoped Interval

/-- Endpoint log bounds interpolate below the original logarithm. -/
theorem chord_le_log {a b c t A B : ℝ} (ha : 0 < a) (hab : a < b)
    (hc : 0 < c) (ht : t ∈ Icc a b)
    (hA : A ≤ log ((a+1)/c)) (hB : B ≤ log ((b+1)/c)) :
    ((b-t)*A+(t-a)*B)/(b-a) ≤ log ((t+1)/c) := by
  have hw : 0 < b-a := sub_pos.mpr hab
  have hu : 0 ≤ (b-t)/(b-a) := div_nonneg (by linarith [ht.2]) hw.le
  have hv : 0 ≤ (t-a)/(b-a) := div_nonneg (by linarith [ht.1]) hw.le
  have hs : (b-t)/(b-a)+(t-a)/(b-a)=1 := by field_simp; ring
  have h := strictConcaveOn_log_Ioi.concaveOn.2
    (show (a+1)/c ∈ Ioi (0:ℝ) by exact div_pos (by linarith) hc)
    (show (b+1)/c ∈ Ioi (0:ℝ) by exact div_pos (by linarith) hc) hu hv hs
  simp only [smul_eq_mul] at h
  have he : (b-t)/(b-a)*((a+1)/c)+(t-a)/(b-a)*((b+1)/c)=(t+1)/c := by
    field_simp
    ring
  rw [he] at h
  have hp := add_le_add (mul_le_mul_of_nonneg_left hA hu)
    (mul_le_mul_of_nonneg_left hB hv)
  calc
    _ = (b-t)/(b-a)*A+(t-a)/(b-a)*B := by ring
    _ ≤ _ := hp.trans h

/-- A reciprocal tangent is positive throughout a positive interval. -/
theorem reciprocal_tangent {a b t : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (ht : t ∈ Icc a b) :
    0 ≤ 4*(a+b-t)/(a+b)^2 ∧ 4*(a+b-t)/(a+b)^2 ≤ 1/t := by
  have hs : 0 < a+b := by linarith
  have htp : 0 < t := ha.trans_le ht.1
  refine ⟨div_nonneg (by linarith [ht.2]) (sq_nonneg _), ?_⟩
  apply (div_le_div_iff₀ (sq_pos_of_pos hs) htp).mpr
  nlinarith [sq_nonneg (a+b-2*t)]

/-- Product of the log chord and reciprocal tangent bounds the tail kernel. -/
theorem kernel_lower {a b c t A B : ℝ} (ha : 0 < a) (hab : a < b)
    (hc : 0 < c) (ht : t ∈ Icc a b) (hA0 : 0 ≤ A) (hB0 : 0 ≤ B)
    (hA : A ≤ log ((a+1)/c)) (hB : B ≤ log ((b+1)/c)) :
    (((b-t)*A+(t-a)*B)/(b-a))*(4*(a+b-t)/(a+b)^2) ≤ log ((t+1)/c)/t := by
  have hch : 0 ≤ ((b-t)*A+(t-a)*B)/(b-a) :=
    div_nonneg (add_nonneg (mul_nonneg (by linarith [ht.2]) hA0)
      (mul_nonneg (by linarith [ht.1]) hB0)) (sub_pos.mpr hab).le
  have hrec := reciprocal_tangent ha hab.le ht
  have hlog := chord_le_log ha hab hc ht hA hB
  have h := mul_le_mul hlog hrec.2 hrec.1 (hch.trans hlog)
  simpa only [div_eq_mul_inv, one_mul] using h

end WuPaper.SourceLogChord
#print axioms WuPaper.SourceLogChord.kernel_lower
