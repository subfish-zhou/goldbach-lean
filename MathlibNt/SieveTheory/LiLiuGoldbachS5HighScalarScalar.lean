import MathlibNt.SieveTheory.LiLiuGoldbachS5HighScalarChange
import MathlibNt.SieveTheory.LiLiuGoldbachS5HighScalarPolynomial
open MeasureTheory Set
open scoped Interval
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
noncomputable section

theorem high_integral_enclosure :
    goldbachB9HighMainIntegral ≤ highH (7/27)-highH 0 ∧
    highH (7/27)-highH 0 ≤ goldbachB9HighMainIntegral + (7/27)/10000000 := by
  have hpoly : Continuous (fun x : ℝ => highL x*highG x) := by
    unfold highL highG
    fun_prop
  have hpi := hpoly.intervalIntegrable (μ := volume) (a := (0 : ℝ)) (b := 7/27)
  have hfi : IntervalIntegrable highF volume 0 (7/27) := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 7/27)]
    exact highF_continuous
  have hmono := intervalIntegral.integral_mono_on
    (by norm_num : (0 : ℝ) ≤ 7/27) hfi hpi (fun x hx => (highF_enclosure hx).1)
  have hmono' := intervalIntegral.integral_mono_on
    (by norm_num : (0 : ℝ) ≤ 7/27) hpi
    (hfi.add (intervalIntegrable_const (c := (1/10000000 : ℝ))))
    (fun x hx => (highF_enclosure hx).2)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x (_hx : x ∈ uIcc (0 : ℝ) (7/27)) => highH_deriv x) hpi
  rw [hftc, ← high_change_integral] at hmono
  rw [hftc, intervalIntegral.integral_add hfi (intervalIntegrable_const),
    ← high_change_integral, intervalIntegral.integral_const] at hmono'
  constructor
  · exact hmono
  · norm_num at hmono' ⊢
    exact hmono'

/-- The actual high double integral, not the full G9 integral. -/
theorem goldbachB9HighMainIntegral_eight_mul_le_392796161 :
    8*goldbachB9HighMainIntegral ≤ (392796161/100000000 : ℝ) := by
  exact (mul_le_mul_of_nonneg_left high_integral_enclosure.1
    (by norm_num : (0 : ℝ) ≤ 8)).trans highH_endpoint

/-- Complete one-sided budget includes the analytic remainder and upward rounding. -/
theorem goldbachB9HighMainIntegral_scalar_accuracy :
    0 ≤ (392796161/100000000 : ℝ)-8*goldbachB9HighMainIntegral ∧
    (392796161/100000000 : ℝ)-8*goldbachB9HighMainIntegral ≤ 1/1000000 := by
  have hu := goldbachB9HighMainIntegral_eight_mul_le_392796161
  have he := high_integral_enclosure.2
  have hr := highH_rounding
  dsimp [highScalarU] at hr
  constructor <;> linarith

/-- Literal high-S5 consumer: epsilon domain, cutoff, threshold, and scale unchanged.
There is no (1-epsilon) factor in the high producer. -/
theorem goldbachS5HighFirstClosed_normalized_upper_392796161
    (δ ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε) (hεu : ε < (2 : ℝ)/15) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
      (goldbachS5Closed (goldbachDifferenceCarrier N ε) N
        ((N : ℝ) ^ (1/10 : ℝ)) ((N : ℝ) ^ (1/3 : ℝ)) : ℝ) ≤
      ((392796161/100000000 : ℝ)+δ)*
        (SingularSeries.liuSingularSeries N*(N : ℝ)/Real.log (N : ℝ)^2) := by
  obtain ⟨N₀,hN₀,h⟩ :=
    goldbachS5HighFirstClosed_normalized_upper_integral δ ε hδ hε hεu
  refine ⟨N₀,hN₀,fun N hN hEven => ?_⟩
  have hscale : 0 ≤ SingularSeries.liuSingularSeries N*(N : ℝ)/Real.log (N : ℝ)^2 :=
    div_nonneg (mul_nonneg (SingularSeries.liuSingularSeries_pos N).le
      (Nat.cast_nonneg N)) (sq_nonneg _)
  exact (h N hN hEven).trans (mul_le_mul_of_nonneg_right
    (add_le_add goldbachB9HighMainIntegral_eight_mul_le_392796161 (le_refl δ)) hscale)

end
end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig