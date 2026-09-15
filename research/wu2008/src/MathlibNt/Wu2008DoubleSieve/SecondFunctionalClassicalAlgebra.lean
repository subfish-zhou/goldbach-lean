import MathlibNt.Wu2008DoubleSieve.FourthRowClassicalCoefficient

/-! General classical algebra with three distinct Omega2 parameters.
All triangles are the existing actual double integrals. Identification with
parameterized Gamma masses is a separate producer obligation. -/
namespace Wu2008DoubleSieve
namespace SecondFunctionalClassicalAlgebra

/-- In particular, e need not equal s and L(c) retains its oriented interval. -/
theorem coefficient_eq {s S B c e : ℝ}
    (hs : 2 ≤ s) (hs3 : s ≤ 3) (hB : 3 ≤ B) (hBS : B ≤ S) (hS5 : S ≤ 5)
    (hc : 2 < c) (hcS : c ≤ S) (he : 2 < e) (heB : e ≤ B) :
    (5 * wuUpperCoefficient s - 4 * wuUpperCoefficient S - wuUpperCoefficient B +
      fourthRowClassicalJ s S + fourthRowClassicalJ c S + fourthRowClassicalJ e S -
      fourthRowClassicalTriangle S c -
      (fourthRowClassicalTriangle S e - fourthRowClassicalTriangle B e)) / 5 =
      -(2 / 5) * fourthRowClassicalL S - (2 / 5) * fourthRowClassicalL B -
      (1 / 5) * fourthRowClassicalL c + (1 / 5) * fourthRowClassicalJ s S +
      (1 / 5) * fourthRowClassicalJ e B := by
  have hAS := firstFunctionalGain_coefficient_eq_log hs hs3 (hB.trans hBS) hS5
  have hAB := firstFunctionalGain_coefficient_eq_log hs hs3 hB (hBS.trans hS5)
  change wuUpperCoefficient s - wuUpperCoefficient S = -fourthRowClassicalL S at hAS
  change wuUpperCoefficient s - wuUpperCoefficient B = -fourthRowClassicalL B at hAB
  rw [fourthRowClassical_triangle_eq_log hcS hc,
    fourthRowClassical_triangle_eq_log (heB.trans hBS) he,
    fourthRowClassical_triangle_eq_log heB he]
  linarith

/-- Regression consumes the actual four Gamma-mass/triangle identities. -/
theorem fourth_row :
    (5 * wuUpperCoefficient (5 / 2) - 4 * wuUpperCoefficient (103 / 25) -
      wuUpperCoefficient (89 / 25) + 2 * fourthRowClassicalJ (5 / 2) (103 / 25) +
      fourthRowClassicalJ (291 / 100) (103 / 25) - gamma5MassC5 - gamma6BaseC6 -
      gamma78GainC true - gamma78GainC false) / 5 =
      -(2 / 5) * fourthRowClassicalL (103 / 25) - (2 / 5) * fourthRowClassicalL (89 / 25) -
      (1 / 5) * fourthRowClassicalL (291 / 100) +
      (1 / 5) * fourthRowClassicalJ (5 / 2) (103 / 25) +
      (1 / 5) * fourthRowClassicalJ (5 / 2) (89 / 25) := by
  have h := coefficient_eq (s := 5 / 2) (S := 103 / 25) (B := 89 / 25)
    (c := 291 / 100) (e := 5 / 2) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  linarith [fourthRowClassical_C5_triangle, fourthRowClassical_C678_triangle]

end SecondFunctionalClassicalAlgebra
end Wu2008DoubleSieve
