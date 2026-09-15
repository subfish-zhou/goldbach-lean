import MathlibNt.Wu2008DoubleSieve.ImprovementIntegrals

/-!
# Closed source indicators in the first feedback kernel

Wu04 (6.2), (6.3), and (3.21) use closed intervals. Each term is
transported separately; no false pointwise disjointness at a shared
endpoint is used. The zero-length interval is covered as well.
-/

namespace Wu2008DoubleSieve

open Set MeasureTheory
open scoped Interval

theorem firstFeedback_indicator_integral (f : ℝ → ℝ) {a b : ℝ}
    (ha : 1 ≤ a) (hab : a ≤ b) (hb : b ≤ 3) :
    (∫ x in (1 : ℝ)..3, (Icc a b).indicator f x) =
      ∫ x in a..b, f x := by
  have hsub : Icc a b ⊆ Icc (1 : ℝ) 3 :=
    fun _ hx => ⟨ha.trans hx.1, hx.2.trans hb⟩
  rw [intervalIntegral.integral_of_le (by norm_num : (1 : ℝ) ≤ 3),
    ← integral_Icc_eq_integral_Ioc, setIntegral_indicator measurableSet_Icc,
    inter_eq_right.mpr hsub, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hab]

theorem firstFeedback_indicator_intervalIntegrable {f : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hf : IntervalIntegrable f volume a b) :
    IntervalIntegrable ((Icc a b).indicator f) volume 1 3 := by
  have hi : IntegrableOn f (Icc a b) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp hf
  exact ((integrable_indicator_iff measurableSet_Icc).mpr hi).intervalIntegrable

end Wu2008DoubleSieve
