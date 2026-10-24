import MathlibNt.SieveTheory.LiLiuGoldbachS3PolynomialCertificate
import MathlibNt.SieveTheory.LiLiuGoldbachS3IntegralScalarTables

open scoped BigOperators
open Finset
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem s3pCoeffs_eq (z : ℝ) : s3eval s3pCoeffs z = goldbachS3_innerPolynomial 24 48 z := by
  have hc : s3pCoeffs = S3Polynomial.innerCoeffs 24 48 := by decide +kernel
  rw [hc]
  exact S3Polynomial.eval_innerCoeffs 24 48 z

theorem s3q0_eq (y : ℝ) :
    s3eval s3q0 y = (s3eval s3pCoeffs (0+y) + (0+y)/10^9) *
      (-8/(3-0)*(∑ k ∈ range 64, (y/(3-0))^k) +
       360/(29-45*0)*((∑ k ∈ range 64, (45*y/(29-45*0))^k) + (5/2 : ℝ)*(3/5)^64)) := by
  have hc : s3q0 = S3Polynomial.segmentCoeffs s3pCoeffs 0 := by decide +kernel
  rw [hc]
  simpa only [Rat.cast_zero] using S3Polynomial.eval_segmentCoeffs s3pCoeffs 0 y

theorem s3q1_eq (y : ℝ) :
    s3eval s3q1 y = (s3eval s3pCoeffs ((1/3)+y) + ((1/3)+y)/10^9) *
      (-8/(3-(1/3))*(∑ k ∈ range 64, (y/(3-(1/3)))^k) +
       360/(29-45*(1/3))*((∑ k ∈ range 64, (45*y/(29-45*(1/3)))^k) + (5/2 : ℝ)*(3/5)^64)) := by
  have hc : s3q1 = S3Polynomial.segmentCoeffs s3pCoeffs (1/3) := by decide +kernel
  rw [hc]
  simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using
    S3Polynomial.eval_segmentCoeffs s3pCoeffs (1/3) y

theorem s3q2_eq (y : ℝ) :
    s3eval s3q2 y = (s3eval s3pCoeffs ((1/2)+y) + ((1/2)+y)/10^9) *
      (-8/(3-(1/2))*(∑ k ∈ range 64, (y/(3-(1/2)))^k) +
       360/(29-45*(1/2))*((∑ k ∈ range 64, (45*y/(29-45*(1/2)))^k) + (5/2 : ℝ)*(3/5)^64)) := by
  have hc : s3q2 = S3Polynomial.segmentCoeffs s3pCoeffs (1/2) := by decide +kernel
  rw [hc]
  simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using
    S3Polynomial.eval_segmentCoeffs s3pCoeffs (1/2) y

theorem s3j0_value : s3prim s3q0 (1/3) - s3prim s3q0 0 = (s3j0 : ℝ) := by
  norm_num [s3prim, s3primAux, s3q0, s3j0]

theorem s3j0b_value : s3prim s3q0 (1/3) - s3prim s3q0 (1/177) = (s3j0b : ℝ) := by
  norm_num [s3prim, s3primAux, s3q0, s3j0b]

theorem s3j1_value : s3prim s3q1 (1/6) - s3prim s3q1 0 = (s3j1 : ℝ) := by
  norm_num [s3prim, s3primAux, s3q1, s3j1]

theorem s3j2_value : s3prim s3q2 (5/74) - s3prim s3q2 0 = (s3j2 : ℝ) := by
  norm_num [s3prim, s3primAux, s3q2, s3j2]

theorem s3B4_arithmetic : (s3Base4 : ℝ) + s3j0 + s3j1 + s3j2 < s3B4 := by
  norm_num [s3Base4, s3j0, s3j0b, s3j1, s3j2, s3B4]

theorem s3B5_arithmetic : (s3Base5 : ℝ) + s3j0b + s3j1 + s3j2 < s3B5 := by
  norm_num [s3Base5, s3j0, s3j0b, s3j1, s3j2, s3B5]

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig