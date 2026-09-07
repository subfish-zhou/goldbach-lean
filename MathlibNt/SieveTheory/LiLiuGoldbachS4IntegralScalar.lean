import MathlibNt.SieveTheory.LiLiuGoldbachB8IntegralReduction
import MathlibNt.SieveTheory.LiLiuGoldbachS4IntegralUpper
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

open MeasureTheory Set
open scoped Interval
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
noncomputable section

/- Fixed analytic degrees, selected without parameter search: y is in [0,1/4].
The Mathlib logarithm remainder after the ninth power is at most
(32/15)*y^11. The reciprocal remainder after degree 9 is at most
(4/3)*y^10. Both are whole-interval geometric estimates. -/
private def s4LogPoly (y : ℝ) : ℝ :=
  2*y + 2/3*y^3 + 2/5*y^5 + 2/7*y^7 + 2/9*y^9 + 32/15*y^11

private def s4GeomPoly (y : ℝ) : ℝ :=
  1+y+y^2+y^3+y^4+y^5+y^6+y^7+y^8+y^9+4/3*y^10

private lemma s4Log_bound {y : ℝ} (hy : y ∈ Icc (0 : ℝ) (1/4)) :
    Real.log ((1+y)/(1-y)) ≤ s4LogPoly y := by
  have hy2 : y^2 ≤ (1/16 : ℝ) := by nlinarith [mul_nonneg hy.1 (sub_nonneg.mpr hy.2)]
  have hp : 0 < 1-y^2 := by linarith
  have hb : y^11 / (1-y^2) ≤ 16/15*y^11 := by
    apply (div_le_iff₀ hp).2
    nlinarith [mul_nonneg (pow_nonneg hy.1 11) (show 0 ≤ 1/16-y^2 by linarith)]
  have h := Real.log_div_le_sum_range_add hy.1 (by linarith [hy.2]) 5
  norm_num [Finset.sum_range_succ] at h
  dsimp [s4LogPoly]
  linarith

private lemma s4Geom_bound {y : ℝ} (hy : y ∈ Icc (0 : ℝ) (1/4)) :
    1/(1-y) ≤ s4GeomPoly y := by
  have hp : 0 < 1-y := by linarith [hy.2]
  apply (div_le_iff₀ hp).2
  have hi : s4GeomPoly y * (1-y) - 1 = y^10*(1-4*y)/3 := by
    dsimp [s4GeomPoly]; ring
  have hn : 0 ≤ y^10*(1-4*y)/3 := by
    apply div_nonneg (mul_nonneg (pow_nonneg hy.1 _) (by linarith [hy.2])) (by norm_num)
  linarith

private lemma s4LogPoly_nonneg {y : ℝ} (hy : 0 ≤ y) : 0 ≤ s4LogPoly y := by
  dsimp [s4LogPoly]; positivity

private lemma s4Change_deriv {y : ℝ} (hy : y ∈ Icc (0 : ℝ) (1/4)) :
    HasDerivAt (fun y : ℝ => 2/(1-y)) (2/(1-y)^2) y := by
  have hp : 1-y ≠ 0 := by linarith [hy.2]
  convert! (((hasDerivAt_id y).const_sub 1).inv hp).const_mul 2 using 1
  norm_num [id, one_div, div_eq_mul_inv]

private lemma s4Change_maps {y : ℝ} (hy : y ∈ Icc (0 : ℝ) (1/4)) :
    2/(1-y) ∈ Icc (2 : ℝ) (8/3) := by
  have hp : 0 < 1-y := by linarith [hy.2]
  constructor
  · apply (le_div_iff₀ hp).2; linarith [hy.1]
  · apply (div_le_iff₀ hp).2; linarith [hy.2]

private lemma s4Change_integral :
    goldbachB8MainIntegral =
      ∫ y in (0 : ℝ)..(1/4), Real.log ((1+y)/(1-y))/(1-y) := by
  have hderiv : ∀ y ∈ uIcc (0 : ℝ) (1/4),
      HasDerivAt (fun y : ℝ => 2/(1-y)) (2/(1-y)^2) y := by
    intro y hy
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1/4)] at hy
    exact s4Change_deriv hy
  have hjac : ContinuousOn (fun y : ℝ => 2/(1-y)^2) (uIcc (0 : ℝ) (1/4)) := by
    apply continuousOn_const.div ((continuousOn_const.sub continuousOn_id).pow 2)
    intro y hy
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1/4)] at hy
    exact pow_ne_zero 2 (by change 1-y ≠ 0; linarith [hy.2])
  have hcont : ContinuousOn (fun t : ℝ => Real.log (t-1)/t)
      ((fun y : ℝ => 2/(1-y)) '' uIcc (0 : ℝ) (1/4)) := by
    apply continuousOn_goldbachB8TransformedIntegrand.mono
    rintro t ⟨y, hy, rfl⟩
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1/4)] at hy
    exact s4Change_maps hy
  have h := intervalIntegral.integral_comp_mul_deriv' hderiv hjac hcont
  norm_num only at h
  rw [goldbachB8MainIntegral_eq_transformedIntegral, ← h]
  apply intervalIntegral.integral_congr
  intro y hy
  rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1/4)] at hy
  have hp : 1-y ≠ 0 := by linarith [hy.2]
  have he : 2/(1-y)-1 = (1+y)/(1-y) := by field_simp; ring
  dsimp only [Function.comp_apply]
  rw [he]
  field_simp [hp]

private def s4Primitive (y : ℝ) : ℝ :=
    (1/1 : ℝ)*y^2 +
    (2/3 : ℝ)*y^3 +
    (2/3 : ℝ)*y^4 +
    (8/15 : ℝ)*y^5 +
    (23/45 : ℝ)*y^6 +
    (46/105 : ℝ)*y^7 +
    (44/105 : ℝ)*y^8 +
    (352/945 : ℝ)*y^9 +
    (563/1575 : ℝ)*y^10 +
    (1126/3465 : ℝ)*y^11 +
    (502/945 : ℝ)*y^12 +
    (1168/4095 : ℝ)*y^13 +
    (619/2205 : ℝ)*y^14 +
    (958/4725 : ℝ)*y^15 +
    (25/126 : ℝ)*y^16 +
    (832/5355 : ℝ)*y^17 +
    (431/2835 : ℝ)*y^18 +
    (106/855 : ℝ)*y^19 +
    (82/675 : ℝ)*y^20 +
    (32/315 : ℝ)*y^21 +
    (64/495 : ℝ)*y^22

private lemma s4Primitive_deriv (y : ℝ) :
    HasDerivAt s4Primitive (s4LogPoly y * s4GeomPoly y) y := by
  unfold s4Primitive
  convert! (((((((((((((((((((((((hasDerivAt_id y).pow 2).const_mul (1/1 : ℝ)).add (((hasDerivAt_id y).pow 3).const_mul (2/3 : ℝ))).add (((hasDerivAt_id y).pow 4).const_mul (2/3 : ℝ))).add (((hasDerivAt_id y).pow 5).const_mul (8/15 : ℝ))).add (((hasDerivAt_id y).pow 6).const_mul (23/45 : ℝ))).add (((hasDerivAt_id y).pow 7).const_mul (46/105 : ℝ))).add (((hasDerivAt_id y).pow 8).const_mul (44/105 : ℝ))).add (((hasDerivAt_id y).pow 9).const_mul (352/945 : ℝ))).add (((hasDerivAt_id y).pow 10).const_mul (563/1575 : ℝ))).add (((hasDerivAt_id y).pow 11).const_mul (1126/3465 : ℝ))).add (((hasDerivAt_id y).pow 12).const_mul (502/945 : ℝ))).add (((hasDerivAt_id y).pow 13).const_mul (1168/4095 : ℝ))).add (((hasDerivAt_id y).pow 14).const_mul (619/2205 : ℝ))).add (((hasDerivAt_id y).pow 15).const_mul (958/4725 : ℝ))).add (((hasDerivAt_id y).pow 16).const_mul (25/126 : ℝ))).add (((hasDerivAt_id y).pow 17).const_mul (832/5355 : ℝ))).add (((hasDerivAt_id y).pow 18).const_mul (431/2835 : ℝ))).add (((hasDerivAt_id y).pow 19).const_mul (106/855 : ℝ))).add (((hasDerivAt_id y).pow 20).const_mul (82/675 : ℝ))).add (((hasDerivAt_id y).pow 21).const_mul (32/315 : ℝ))).add (((hasDerivAt_id y).pow 22).const_mul (64/495 : ℝ))) using 1
  norm_num [id, s4LogPoly, s4GeomPoly]
  ring

private lemma s4Primitive_endpoint :
    8*(s4Primitive (1/4)-s4Primitive 0) ≤ (60962/100000 : ℝ) := by
  norm_num [s4Primitive]

/-- Pure analytic scalar estimate for the actual production double integral I8. -/
theorem goldbachB8MainIntegral_eight_mul_le_60962 :
    8 * goldbachB8MainIntegral ≤ (60962/100000 : ℝ) := by
  have hpoly : Continuous (fun y : ℝ => s4LogPoly y * s4GeomPoly y) := by
    unfold s4LogPoly s4GeomPoly
    fun_prop
  have hpi := hpoly.intervalIntegrable (μ := volume) (a := (0 : ℝ)) (b := 1/4)
  have hlog : ContinuousOn (fun y : ℝ => Real.log ((1+y)/(1-y))/(1-y))
      (Icc (0 : ℝ) (1/4)) := by
    have hp : ∀ y ∈ Icc (0 : ℝ) (1/4), 1-y ≠ 0 := by
      intro y hy; linarith [hy.2]
    apply ContinuousOn.div
      (((continuousOn_const.add continuousOn_id).div
        (continuousOn_const.sub continuousOn_id) hp).log ?_)
      (continuousOn_const.sub continuousOn_id) hp
    intro y hy
    change (1+y)/(1-y) ≠ 0
    exact div_ne_zero (by linarith [hy.1]) (hp y hy)
  have hli : IntervalIntegrable
      (fun y : ℝ => Real.log ((1+y)/(1-y))/(1-y)) volume 0 (1/4) := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1/4)]
    exact hlog
  have hmono := intervalIntegral.integral_mono_on
    (by norm_num : (0 : ℝ) ≤ 1/4) hli hpi (fun y hy => by
      have hp : 0 ≤ 1/(1-y) := by
        apply div_nonneg (by norm_num); linarith [hy.2]
      calc
        Real.log ((1+y)/(1-y))/(1-y) =
            Real.log ((1+y)/(1-y)) * (1/(1-y)) := by ring
        _ ≤ s4LogPoly y * (1/(1-y)) :=
          mul_le_mul_of_nonneg_right (s4Log_bound hy) hp
        _ ≤ s4LogPoly y * s4GeomPoly y :=
          mul_le_mul_of_nonneg_left (s4Geom_bound hy) (s4LogPoly_nonneg hy.1))
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun y (_hy : y ∈ uIcc (0 : ℝ) (1/4)) => s4Primitive_deriv y) hpi
  rw [hftc, ← s4Change_integral] at hmono
  exact (mul_le_mul_of_nonneg_left hmono (by norm_num : (0 : ℝ) ≤ 8)).trans
    s4Primitive_endpoint

/-- The unchanged actual S4 count, with all upstream analytic errors already paid. -/
theorem goldbachS4_normalized_upper_60962
    (δ ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε) (hεu : ε < (2 : ℝ)/15) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
      (goldbachS4 (goldbachDifferenceCarrier N ε) N ((N : ℝ) ^ (3/11 : ℝ)) : ℝ) ≤
        ((60962/100000 : ℝ) + δ) *
          (SingularSeries.liuSingularSeries N * (N : ℝ) / Real.log (N : ℝ)^2) := by
  obtain ⟨N₀, hN₀, hS⟩ := goldbachS4_normalized_upper_integral δ ε hδ hε hεu
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN hEven
  have hscale : 0 ≤ SingularSeries.liuSingularSeries N * (N : ℝ) /
      Real.log (N : ℝ)^2 :=
    div_nonneg (mul_nonneg (SingularSeries.liuSingularSeries_pos N).le
      (Nat.cast_nonneg N)) (sq_nonneg _)
  exact (hS N hN hEven).trans (mul_le_mul_of_nonneg_right
    (add_le_add goldbachB8MainIntegral_eight_mul_le_60962 (le_rfl : δ ≤ δ)) hscale)

end
end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig