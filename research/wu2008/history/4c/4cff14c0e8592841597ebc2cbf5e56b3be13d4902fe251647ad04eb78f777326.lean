import MathlibNt.Wu2008DoubleSieve.FirstFeedbackKernelXi
import MathlibNt.Wu2008DoubleSieve.FirstFeedbackParameters
import MathlibNt.Wu2008DoubleSieve.FirstFeedbackScalar

/-!
# Exact integral assembly for Wu04 Proposition 3

Author TeX lines 2614--2619 combine (6.2) and (6.3). This is the exact
integral identity preceding that comparison. The actual limiting gain
is only assumed through its proved interval integrability. Each closed
indicator is transported separately, including coincident endpoints.
-/

namespace Wu2008DoubleSieve

open Set Real MeasureTheory
open scoped Interval

theorem wuImprovementLimit_firstFeedback_middle_intervalIntegrable {δ s t : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10)
    (hs : 2 ≤ s) (hs3 : s ≤ 3) (ht : 3 ≤ t) (ht5 : t ≤ 5)
    (hratio : 2 ≤ t - t / s) :
    IntervalIntegrable (fun x => wuImprovementLimit true δ x / x *
      log ((x + 1) / ((s - 1) * (t - 1 - x))))
      volume (t - t / s - 1) (t - 2) := by
  obtain ⟨ha, hab, hb⟩ := firstFeedbackXi_interval_endpoints hs hs3 ht ht5 hratio
  have hH := wuImprovementLimit_intervalIntegrable true hδ
    (by linarith : δ < 1 / 2) ha hab (by linarith : t - 2 ≤ 10)
  have hc : ContinuousOn (fun x : ℝ => 1 / (2 * x) *
      log ((x + 1) / ((s - 1) * (t - 1 - x))))
      (uIcc (t - t / s - 1) (t - 2)) := by
    rw [uIcc_of_le hab]
    exact firstFeedbackXi_middle_continuousOn (by linarith) hratio
  convert (hH.mul_continuousOn hc).const_mul 2 using 1
  ext x
  ring

/-- The exact fixed-delta identity used to assemble Wu04 Proposition 3. -/
theorem wuImprovementLimit_firstFeedback_assembly_integral {δ s t : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10)
    (hs : 2 ≤ s) (hs3 : s ≤ 3) (ht : 3 ≤ t) (ht5 : t ≤ 5)
    (hratio : 2 ≤ t - t / s) :
    (∫ x in (1 : ℝ)..3, wuImprovementLimit true δ x * firstFeedbackXi x s t) =
      (∫ x in (1 : ℝ)..3,
        wuImprovementLimit true δ x * firstFeedbackSigmaZero x / x) *
          log (4 / (t - 1)) +
      (∫ x in (t - 2)..3,
        wuImprovementLimit true δ x / x * log ((x + 1) / (t - 1))) +
      (1 / 2) * (log ((t - 1) / (s - 1)) *
        ((∫ x in (1 : ℝ)..3,
          wuImprovementLimit true δ x * firstFeedbackSigmaZero x / x) +
          ∫ x in (t - 2)..3, wuImprovementLimit true δ x / x) +
        ∫ x in (t - t / s - 1)..(t - 2),
          wuImprovementLimit true δ x / x *
            log ((x + 1) / ((s - 1) * (t - 1 - x)))) := by
  obtain ⟨ha, hab, hb⟩ := firstFeedbackXi_interval_endpoints hs hs3 ht ht5 hratio
  have hb1 : 1 ≤ t - 2 := by linarith
  let H := wuImprovementLimit true δ
  let S := fun x => H x * firstFeedbackSigmaZero x / x
  let U := fun x => H x / x
  let T := fun x => U x * log ((x + 1) / (t - 1))
  let M := fun x => U x * log ((x + 1) / ((s - 1) * (t - 1 - x)))
  let A := log (4 / (t - 1))
  let L := log ((t - 1) / (s - 1))
  have hS : IntervalIntegrable S volume 1 3 :=
    firstFeedbackSigmaZero_gain_intervalIntegrable true hδ (by linarith)
  have hU : IntervalIntegrable U volume 1 3 :=
    wuImprovementLimit_div_intervalIntegrable true hδ (by linarith)
      (by norm_num) (by norm_num) (by norm_num)
  have hT : IntervalIntegrable T volume (t - 2) 3 :=
    (firstFeedback_source64 hU ht ht5).2.1
  have hUtail : IntervalIntegrable U volume (t - 2) 3 :=
    wuImprovementLimit_div_intervalIntegrable true hδ (by linarith)
      hb1 hb (by norm_num)
  have hM : IntervalIntegrable M volume (t - t / s - 1) (t - 2) :=
    wuImprovementLimit_firstFeedback_middle_intervalIntegrable
      hδ hδhi hs hs3 ht ht5 hratio
  have hTi := firstFeedback_indicator_intervalIntegrable hb hT
  have hUi := firstFeedback_indicator_intervalIntegrable hb hUtail
  have hMi := firstFeedback_indicator_intervalIntegrable hab hM
  have hcoeffS : log (16 / ((s - 1) * (t - 1))) = 2 * A + L := by
    have h := firstFeedback_sigma_log_coefficient
      (by linarith : 1 < s) (by linarith : 1 < t)
    dsimp only [A, L]
    linarith
  have heq (x : ℝ) (hx : x ∈ Icc (1 : ℝ) 3) :
      H x * firstFeedbackXi x s t =
        S x * A + (Icc (t - 2) 3).indicator T x +
        (1 / 2) * (L * (S x + (Icc (t - 2) 3).indicator U x) +
          (Icc (t - t / s - 1) (t - 2)).indicator M x) := by
    have hcoeffT : log ((x + 1) ^ 2 / ((s - 1) * (t - 1))) =
        2 * log ((x + 1) / (t - 1)) + L := by
      have h := firstFeedback_tail_log_coefficient
        (by linarith : 1 < s) (by linarith : 1 < t)
        (by linarith [hx.1] : -1 < x)
      dsimp only [L]
      linarith
    dsimp only [firstFeedbackXi]
    rw [hcoeffS, hcoeffT]
    simp only [indicator]
    split_ifs <;> dsimp only [S, U, T, M] <;> ring
  calc
    _ = ∫ x in (1 : ℝ)..3,
        S x * A + (Icc (t - 2) 3).indicator T x +
        (1 / 2) * (L * (S x + (Icc (t - 2) 3).indicator U x) +
          (Icc (t - t / s - 1) (t - 2)).indicator M x) := by
      apply intervalIntegral.integral_congr
      rw [uIcc_of_le (by norm_num : (1 : ℝ) ≤ 3)]
      exact heq
    _ = _ := by
      rw [intervalIntegral.integral_add ((hS.mul_const A).add hTi)
          (((hS.add hUi).const_mul L).add hMi |>.const_mul (1 / 2)),
        intervalIntegral.integral_add (hS.mul_const A) hTi,
        intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_add ((hS.add hUi).const_mul L) hMi,
        intervalIntegral.integral_const_mul, intervalIntegral.integral_add hS hUi,
        firstFeedback_indicator_integral T hb1 hb (by norm_num),
        firstFeedback_indicator_integral U hb1 hb (by norm_num),
        firstFeedback_indicator_integral M ha hab hb]

end Wu2008DoubleSieve
