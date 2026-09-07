import MathlibNt.SieveTheory.LiLiuGoldbachG67ActualIntegral

open Set MeasureTheory
open scoped Interval
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
open LiLiuGoldbachIdealPairKernel

noncomputable section
namespace G67ElementaryIntegral

/-- The constructed upper delay function dominates its initial reciprocal globally. -/
theorem upper_reciprocal_lower {s : ℝ} (hs : 0 < s) :
    2 * Real.exp Real.eulerMascheroniConstant / s ≤ jr1965F s := by
  exact div_le_div_of_nonneg_right
    (delayInitial_le_delayWeight (by positivity) false s) hs.le

/-- The elementary logarithmic lower bound follows from the actual delay recurrence.
It holds on the whole half-line, hence in particular up to 37/8. -/
theorem lower_log {s : ℝ} (hs : 2 ≤ s) :
    2 * Real.exp Real.eulerMascheroniConstant * Real.log (s - 1) / s ≤ jr1965f s := by
  let A : ℝ := 2 * Real.exp Real.eulerMascheroniConstant
  have hc : ContinuousOn (fun t : ℝ => A / (t - 1)) (Icc 2 s) :=
    continuousOn_const.div (continuousOn_id.sub continuousOn_const)
      (by intro t ht; linarith [ht.1])
  have hF : ContinuousOn (fun t : ℝ => jr1965F (t - 1)) (Icc 2 s) :=
    continuousOn_jr1965F.comp (continuousOn_id.sub continuousOn_const)
      (by intro t ht; change 0 < t - 1; linarith [ht.1])
  have hi : (∫ t in (2 : ℝ)..s, A / (t - 1)) = A * Real.log (s - 1) := by
    have hd : ∀ t ∈ uIcc (2 : ℝ) s,
        HasDerivAt (fun t : ℝ => A * Real.log (t - 1)) (A / (t - 1)) t := by
      intro t ht
      have ht' : t ∈ Icc (2 : ℝ) s := by simpa [uIcc_of_le hs] using ht
      convert! (((hasDerivAt_id t).sub_const 1).log (by change t - 1 ≠ 0; linarith [ht'.1])).const_mul A using 1 ; simp [div_eq_mul_inv]
    convert intervalIntegral.integral_eq_sub_of_hasDerivAt hd
      (hc.intervalIntegrable_of_Icc hs) using 1
    norm_num
  have hm := intervalIntegral.integral_mono_on (μ := volume) hs (hc.intervalIntegrable_of_Icc hs)
    (hF.intervalIntegrable_of_Icc hs) (fun t ht => upper_reciprocal_lower (by linarith [ht.1]))
  have hr := jr1965f_integral_recurrence (v := 2) le_rfl hs
  rw [jr1965f_initial le_rfl, mul_zero, zero_add] at hr
  rw [hi, ← hr] at hm
  exact (div_le_iff₀ (by linarith : 0 < s)).2 (by simpa [A, mul_comm s] using hm)

/-- The literal explicit logarithmic kernel, not a replacement definition of C67. -/
def elementaryKernel (x : ℝ × ℝ) : ℝ :=
  max 0 (Real.log ((1/2 - x.1 - x.2 - (4/53 : ℝ))/(4/53 : ℝ)) /
    (1/2 - x.1 - x.2))

/-- Geometry of the full union, including every point of the square diagonal. -/
theorem domain_bounds {u v : ℝ} (hu : u ∈ Icc (4/53 : ℝ) (4/33 : ℝ))
    (hv : v ∈ Icc (4/53 : ℝ) (3/11 : ℝ)) :
    0 < u ∧ 0 < v ∧ 0 < 1/2-u-v ∧ 0 < (1/2-u-v-(4/53 : ℝ))/(4/53 : ℝ) ∧
      (1/2-u-v)/(4/53 : ℝ) ≤ 37/8 := by
  rcases hu with ⟨hu,hU⟩
  rcases hv with ⟨hv,hV⟩
  norm_num at *
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

/-- Pointwise comparison with the actual zero-truncation JR kernel. -/
theorem kernel_lower {u v : ℝ} (hu : u ∈ Icc (4/53 : ℝ) (4/33 : ℝ))
    (hv : v ∈ Icc (4/53 : ℝ) (3/11 : ℝ)) :
    (2 * Real.exp Real.eulerMascheroniConstant * (4/53 : ℝ)) * elementaryKernel (u,v) ≤
      kernel 0 (u,v) := by
  obtain ⟨_,_,hD,hL,_⟩ := domain_bounds hu hv
  let s : ℝ := (1/2-u-v)/(4/53 : ℝ)
  have he : (1/2-u-v-(4/53 : ℝ))/(4/53 : ℝ) = s-1 := by dsimp [s]; ring
  have hA : 0 < 2 * Real.exp Real.eulerMascheroniConstant * (4/53 : ℝ) := by positivity
  unfold elementaryKernel kernel
  simp only [sub_zero]
  rw [he]
  by_cases hs : 2 ≤ s
  · have hl : 0 ≤ Real.log (s-1) := Real.log_nonneg (by linarith)
    rw [max_eq_right (div_nonneg hl hD.le)]
    have heq : (2 * Real.exp Real.eulerMascheroniConstant * (4/53 : ℝ)) *
        (Real.log (s-1)/(1/2-u-v)) =
        2 * Real.exp Real.eulerMascheroniConstant * Real.log (s-1)/s := by
      dsimp [s]
      field_simp
    rw [heq]
    exact (lower_log hs).trans (le_max_right _ _)
  · have hl : Real.log (s-1) ≤ 0 := Real.log_nonpos (by rw [he] at hL; exact hL.le) (by linarith)
    rw [max_eq_left (div_nonpos_of_nonpos_of_nonneg hl hD.le), mul_zero]
    exact le_max_left _ _

end G67ElementaryIntegral
