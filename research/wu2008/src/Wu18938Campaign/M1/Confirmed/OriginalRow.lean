import Wu18938Campaign.M1.Confirmed.SecondFiniteUpdate
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalCoupledRows

noncomputable section

namespace Wu18938Campaign.M1.Confirmed

open Wu2008DoubleSieve MotherPair Finset Real MeasureTheory
open scoped Classical Interval

theorem rectangle_area_le_integral {p : SecondFunctionalParameters} (hp : AnalyticParameters p)
    {j : Term} (r : GainRectangle p j) :
    (r.B - r.A) * (r.D - r.C) ≤ rectIntegral r.A r.B r.C r.D := by
  have hA : 1 / 10 ≤ r.A := by linarith [(parameter_order hp).1,r.lowerP_lt_A]
  have hD : r.D < 1 / 2 := by linarith [r.twiceD_lt_one]
  have hc := packing_smooth_continuous hD
  have ho : Continuous (fun t : ℝ => ∫ u in r.C..r.D, packingSmooth r.D (t,u)) := by
    apply gamma5Gain_moving_integral
    · exact hc.comp (by fun_prop)
    · fun_prop
    · fun_prop
  have hl (t : ℝ) (ht : t ∈ Set.Icc r.A r.B) :
      r.D - r.C ≤ ∫ u in r.C..r.D, packingSmooth r.D (t,u) := by
    have huInt : IntervalIntegrable (fun u : ℝ => packingSmooth r.D (t,u)) volume r.C r.D :=
      (hc.comp (by fun_prop)).intervalIntegrable _ _
    have hh := intervalIntegral.integral_mono_on r.C_lt_D.le
      (intervalIntegrable_const (c := (1 : ℝ))) huInt (fun u hu => by
        have ht0 : 0 < t := by linarith [ht.1]
        have hu0 : 0 < u := by linarith [hu.1,r.A_lt_B,r.B_lt_C]
        have htD : t ≤ r.D := ht.2.trans (r.B_lt_C.le.trans r.C_lt_D.le)
        have hp : 0 < t * u * (1 - t - u) :=
          mul_pos (mul_pos ht0 hu0) (by linarith [hu.2])
        have hprod : t * u * (1 - t - u) ≤ 1 := by
          have hab : t * u ≤ (1 : ℝ) :=
            (mul_le_mul (by linarith : t ≤ 1) (by linarith [hu.2] : u ≤ 1)
              hu0.le (by norm_num)).trans_eq (one_mul 1)
          have hh := mul_le_mul hab (show 1 - t - u ≤ 1 by linarith)
            (show 0 ≤ 1 - t - u by linarith [hu.2]) (show (0 : ℝ) ≤ 1 by norm_num)
          simpa only [one_mul] using hh
        rw [packing_smooth_eq ⟨hA.trans ht.1,htD⟩
          ⟨hA.trans (r.A_lt_B.le.trans (r.B_lt_C.le.trans hu.1)),hu.2⟩,gamma5MassKernel]
        exact (le_div_iff₀ hp).mpr (by simpa only [one_mul] using hprod))
    simpa only [intervalIntegral.integral_const,smul_eq_mul,mul_one] using hh
  have hh := intervalIntegral.integral_mono_on r.A_lt_B.le
    (intervalIntegrable_const (c := r.D - r.C)) (ho.intervalIntegrable (μ := volume) _ _) hl
  rw [intervalIntegral.integral_const,smul_eq_mul] at hh
  exact hh.trans_eq (packing_smooth_rectangle_eq hA r.A_lt_B.le r.B_lt_C.le r.C_lt_D.le le_rfl)

def originalRow1Rectangle : GainRectangle SecondFunctionalParameters.row1 .gammaFive where
  A := 1 / 4
  B := 13 / 50
  C := 27 / 100
  D := 7 / 25
  sample := 13 / 5
  lowerP_lt_A := by norm_num [SecondFunctionalParameters.row1]
  A_lt_B := by norm_num
  B_lt_C := by norm_num
  C_lt_D := by norm_num
  B_lt_upperP := by norm_num [upperP,SecondFunctionalParameters.row1]
  lowerQ_lt_C := by norm_num [lowerQ,SecondFunctionalParameters.row1]
  D_lt_upperQ := by norm_num [upperQ,SecondFunctionalParameters.row1]
  twiceD_lt_one := by norm_num
  D_twiceB_lt_one := by norm_num
  sample_lower := by norm_num
  sample_upper := by norm_num
  ratio_lt_sample := by norm_num [Hratio,SecondFunctionalParameters.row1]

theorem originalRow1Rectangle_positive :
    0 < HighSixPhase7.seed * rectIntegral originalRow1Rectangle.A originalRow1Rectangle.B
      originalRow1Rectangle.C originalRow1Rectangle.D := by
  have hh := rectangle_area_le_integral SecondFunctionalCoupled.row1_analytic originalRow1Rectangle
  have hpos : 0 < (originalRow1Rectangle.B - originalRow1Rectangle.A) *
      (originalRow1Rectangle.D - originalRow1Rectangle.C) := by norm_num [originalRow1Rectangle]
  exact mul_pos HighSixPhase7.seed_pos (hpos.trans_le hh)

theorem original_row1_finite_update (m : ℕ) {η δ τ ε : ℝ}
    (hη : 0 < η) (hδ : 0 < δ) (hδhi : δ ≤ 1 / 100) (hτ : 0 < τ) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      let p := SecondFunctionalParameters.row1
      5 * wuBoxPhi N δ (convolutionWuWindows N Δ V) p.s ≤
        (4 * wuUpperCoefficient p.S + wuUpperCoefficient p.kappa1 -
          (∫ u in (1 - 1 / p.s)..(1 - 1 / p.S), log (p.S * u - 1) / (u * (1 - u))) -
          (∫ u in (1 - 1 / p.kappa2)..(1 - 1 / p.S), log (p.S * u - 1) / (u * (1 - u))) -
          (∫ u in (1 - 1 / p.kappa3)..(1 - 1 / p.S), log (p.S * u - 1) / (u * (1 - u))) +
          (1 + τ) ^ 2 * (∑ k : Term, Pair.classicalIntegral p k) -
          HighSixPhase7.seed * rectIntegral (1 / 4) (13 / 50) (27 / 100) (7 / 25) +
          (2 / (1 - 2 * δ)) * (omega3XIntegralEnvelope p.kappa3 p.kappa1 +
            SecondFunctionalCoupled.jointSup p) + ε) *
          boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  exact roughBox_second_finite_update SecondFunctionalParameters.row1
    SecondFunctionalCoupled.row1_analytic (by norm_num [SecondFunctionalParameters.row1])
    .gammaFive originalRow1Rectangle le_rfl m hη hδ hδhi hτ he

end Wu18938Campaign.M1.Confirmed
