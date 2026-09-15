import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiFiniteAbel
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

open MeasureTheory Set
open scoped Interval

namespace MathlibNt.SieveTheory.LinearSieve

noncomputable def M (z x : ℝ) := Real.log z / Real.log x
noncomputable def dens (z x : ℝ) := Real.log z / (x * (Real.log x)^2)

lemma deriv_M {z x : ℝ} (hx : 1 < x) :
    HasDerivAt (M z) (- dens z x) x := by
  have hx0 : x ≠ 0 := ne_of_gt (zero_lt_one.trans hx)
  have hl : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx)
  have h := (Real.hasDerivAt_log hx0).inv hl |>.const_mul (Real.log z)
  have hd : Real.log z * (-x⁻¹ / Real.log x ^ 2) =
      -(Real.log z / (x * Real.log x ^ 2)) := by
    field_simp
  exact_mod_cast h.congr_deriv hd

lemma dens_continuousOn {z x y : ℝ} (hx : 1 < x) (hxy : x ≤ y) :
    ContinuousOn (dens z) (uIcc x y) := by
  rw [uIcc_of_le hxy]
  intro t ht
  have ht1 : 1 < t := hx.trans_le ht.1
  have ht0 : t ≠ 0 := ne_of_gt (zero_lt_one.trans ht1)
  have hlt : Real.log t ≠ 0 := ne_of_gt (Real.log_pos ht1)
  apply ContinuousAt.continuousWithinAt
  exact continuousAt_const.div
    (continuousAt_id.mul ((Real.continuousAt_log ht0).pow 2))
    (mul_ne_zero ht0 (pow_ne_zero 2 hlt))

lemma M_sub_M_eq_integral {z x y : ℝ} (hx : 1 < x) (hxy : x ≤ y) :
    M z x - M z y = ∫ t in x..y, dens z t := by
  have hderiv : ∀ t ∈ uIcc x y, HasDerivAt (M z) (- dens z t) t := by
    intro t ht
    rw [uIcc_of_le hxy] at ht
    exact deriv_M (hx.trans_le ht.1)
  have hint : IntervalIntegrable (fun t => - dens z t) volume x y :=
    (dens_continuousOn hx hxy).neg.intervalIntegrable
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [intervalIntegral.integral_neg] at h
  linarith

lemma integrand_intervalIntegrable {z x y : ℝ} {g : ℝ → ℝ}
    (hx : 1 < x) (hxy : x ≤ y) (hg : MonotoneOn g (Icc x y)) :
    IntervalIntegrable (fun t => g t * dens z t) volume x y := by
  apply (show IntervalIntegrable g volume x y by
    apply MonotoneOn.intervalIntegrable
    simpa [uIcc_of_le hxy] using hg).mul_continuousOn
  exact dens_continuousOn hx hxy

lemma local_mainRatio_le_integral {z x y : ℝ} {g : ℝ → ℝ}
    (hx : 1 < x) (hxy : x ≤ y) (hz : 1 < z)
    (hg : MonotoneOn g (Icc x y)) :
    g x * (M z x - M z y) ≤ ∫ t in x..y, g t * dens z t := by
  rw [M_sub_M_eq_integral hx hxy, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_mono_on hxy
  · exact (dens_continuousOn hx hxy).const_mul (g x) |>.intervalIntegrable
  · exact integrand_intervalIntegrable hx hxy hg
  · intro t ht
    apply mul_le_mul_of_nonneg_right (hg (left_mem_Icc.mpr hxy) ht ht.1)
    exact div_nonneg (Real.log_pos hz).le
      (mul_nonneg (by linarith [hx, ht.1]) (sq_nonneg (Real.log t)))


/-- A finite left-node Stieltjes sum for `log z / log x` is bounded by the
corresponding continuous main integral.  The list includes the genuine
endpoints, and only sortedness and monotonicity are used. -/
theorem finiteNodeMainRatioSum_le_integral
    {w z : ℝ} (g : ℝ → ℝ) (interior : List ℝ)
    (hw : 1 < w) (hwz : w ≤ z)
    (hnodes : (w :: interior ++ [z]).Pairwise (· ≤ ·))
    (hg : MonotoneOn g (Icc w z)) :
    finiteNodeMainRatioSum z g (w :: interior ++ [z]) ≤
      ∫ x in w..z, g x * (Real.log z / (x * (Real.log x) ^ 2)) := by
  change finiteNodeStieltjesSum (M z) g (w :: interior ++ [z]) ≤
    ∫ x in w..z, g x * dens z x
  have hz : 1 < z := hw.trans_le hwz
  induction interior generalizing w with
  | nil =>
      simpa [finiteNodeStieltjesSum] using
        local_mainRatio_le_integral hw hwz hz hg
  | cons x xs ih =>
      have hnodes' := hnodes
      change (w :: (x :: (xs ++ [z]))).Pairwise (· ≤ ·) at hnodes'
      rw [List.pairwise_cons] at hnodes'
      have hwx : w ≤ x := hnodes'.1 x (by simp)
      have htail : (x :: xs ++ [z]).Pairwise (· ≤ ·) := hnodes'.2
      have htail' := htail
      change (x :: (xs ++ [z])).Pairwise (· ≤ ·) at htail'
      rw [List.pairwise_cons] at htail'
      have hxz : x ≤ z := htail'.1 z (by simp)
      have hx : 1 < x := hw.trans_le hwx
      have hgwx : MonotoneOn g (Icc w x) := by
        intro a ha b hb hab
        exact hg ⟨ha.1, ha.2.trans hxz⟩ ⟨hb.1, hb.2.trans hxz⟩ hab
      have hgxz : MonotoneOn g (Icc x z) := by
        intro a ha b hb hab
        exact hg ⟨hwx.trans ha.1, ha.2⟩ ⟨hwx.trans hb.1, hb.2⟩ hab
      calc
        finiteNodeStieltjesSum (M z) g (w :: x :: xs ++ [z]) =
            g w * (M z w - M z x) +
              finiteNodeStieltjesSum (M z) g (x :: xs ++ [z]) := rfl
        _ ≤ (∫ t in w..x, g t * dens z t) +
              (∫ t in x..z, g t * dens z t) :=
          add_le_add (local_mainRatio_le_integral hw hwx hz hgwx)
            (ih hx hxz htail hgxz)
        _ = ∫ t in w..z, g t * dens z t :=
          intervalIntegral.integral_add_adjacent_intervals
            (integrand_intervalIntegrable hw hwx hgwx)
            (integrand_intervalIntegrable hx hxz hgxz)

end MathlibNt.SieveTheory.LinearSieve
