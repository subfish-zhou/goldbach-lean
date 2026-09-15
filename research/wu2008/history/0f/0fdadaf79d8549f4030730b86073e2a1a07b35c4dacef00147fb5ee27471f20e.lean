import MathlibNt.Wu2008DoubleSieve.TableFeedbackGeometry

/-!
# The literal upper-tail kernel of Wu04 (6.2)

The closed indicator is handled by the accepted interval-integrability
API. No continuity of the actual improvement function is required.
-/

namespace Wu2008DoubleSieve

open Set Real MeasureTheory
open scoped Interval

noncomputable def tableGainKernel (v x : ℝ) : ℝ :=
  firstFeedbackSigmaZero x / x * log (4 / (v - 1)) +
    (Icc (v - 2) 3).indicator (fun _ : ℝ => (1 : ℝ)) x / x *
      log ((x + 1) / (v - 1))

theorem tableGainKernel_nonneg {v x : ℝ}
    (hv : 3 ≤ v) (hv5 : v ≤ 5) (hx : x ∈ Icc (1 : ℝ) 3) :
    0 ≤ tableGainKernel v x := by
  have hx0 : 0 < x := by linarith [hx.1]
  have hv0 : 0 < v - 1 := by linarith
  unfold tableGainKernel
  apply add_nonneg
  · apply mul_nonneg (div_nonneg (firstFeedbackSigmaZero_nonneg hx) hx0.le)
    exact Real.log_nonneg ((le_div_iff₀ hv0).mpr (by linarith))
  · by_cases hm : x ∈ Icc (v - 2) 3
    · rw [indicator_of_mem hm]
      apply mul_nonneg (div_nonneg (by norm_num) hx0.le)
      exact Real.log_nonneg ((le_div_iff₀ hv0).mpr (by linarith [hm.1]))
    · simp only [indicator_of_notMem hm, zero_div, zero_mul, le_refl]

theorem tableGainKernel_tail_continuousOn {v : ℝ} (hv : 3 ≤ v) :
    ContinuousOn (fun x : ℝ => 1 / x * log ((x + 1) / (v - 1))) (Icc (1 : ℝ) 3) := by
  apply ContinuousOn.mul
  · exact continuousOn_const.div continuousOn_id (fun x hx => by
      change x ≠ 0
      linarith [hx.1])
  · apply ContinuousOn.log
    · exact (continuousOn_id.add continuousOn_const).div_const _
    · intro x hx
      exact div_ne_zero (by linarith [hx.1]) (by linarith)

theorem tableGainKernel_mul_intervalIntegrable {v : ℝ} {f : ℝ → ℝ}
    (hv : 3 ≤ v) (hv5 : v ≤ 5) (hf : IntervalIntegrable f volume 1 3) :
    IntervalIntegrable (fun x => f x * tableGainKernel v x) volume 1 3 := by
  have hc : ContinuousOn (fun x => firstFeedbackSigmaZero x / x *
      log (4 / (v - 1))) (uIcc (1 : ℝ) 3) := by
    rw [uIcc_of_le (by norm_num : (1 : ℝ) ≤ 3)]
    exact firstFeedbackSigmaZero_div_continuousOn.mul_const _
  have hbase := hf.mul_continuousOn hc
  have htail := firstFeedbackKernel_indicator_mul_intervalIntegrable hf
    (a := v - 2) (b := 3) (by linarith) (by linarith) le_rfl
    ((tableGainKernel_tail_continuousOn hv).mono (fun x hx =>
      ⟨by linarith [hx.1], hx.2⟩))
  convert hbase.add htail using 1
  ext x
  dsimp [tableGainKernel]
  ring

theorem tableGainKernel_intervalIntegrable {v : ℝ}
    (hv : 3 ≤ v) (hv5 : v ≤ 5) :
    IntervalIntegrable (tableGainKernel v) volume 1 3 := by
  simpa only [one_mul] using tableGainKernel_mul_intervalIntegrable
    hv hv5 (f := fun _ => 1) intervalIntegrable_const

theorem tableGainKernel_actual_intervalIntegrable {δ v : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) (hv : 3 ≤ v) (hv5 : v ≤ 5) :
    IntervalIntegrable (fun x => wuImprovementLimit true δ x * tableGainKernel v x)
      volume 1 3 :=
  tableGainKernel_mul_intervalIntegrable hv hv5
    (wuImprovementLimit_intervalIntegrable true hδ (by linarith)
      (by norm_num) (by norm_num) (by norm_num))

end Wu2008DoubleSieve
