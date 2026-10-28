import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryDirectPayMainNormalize

noncomputable section
open Classical Finset
namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

/-- Exact exponent bookkeeping for the squared, normalized main contribution. -/
theorem directPayMain_global_square {C L x T R S ρ p η : ℝ}
    (hC : 0 ≤ C) (hL : 0 ≤ L) (hx : 0 < x) (hT : 0 ≤ T) (hR : 0 ≤ R) :
    25165824*(C*x^ρ)*(L*x^p)*(x^η)^7*T^(5/2 : ℝ)*R^(7/2 : ℝ)*S^4/x^2 =
      (Real.sqrt (25165824*C*L)*x^((ρ+p+7*η)/2)*
        (T^(5/4 : ℝ)*R^(7/4 : ℝ)*S^2/x))^2 := by
  have hxpow : (x^((ρ+p+7*η)/2))^2 = x^ρ*x^p*(x^η)^7 := by
    rw [← Real.rpow_mul_natCast hx.le, ← Real.rpow_mul_natCast hx.le]
    norm_num only [Nat.cast_ofNat]
    rw [show ((ρ+p+7*η)/2)*2 = ρ+p+η*7 by ring,
      Real.rpow_add hx, Real.rpow_add hx]
  have hTpow : (T^(5/4 : ℝ))^2 = T^(5/2 : ℝ) := by
    rw [← Real.rpow_mul_natCast hT]; norm_num
  have hRpow : (R^(7/4 : ℝ))^2 = R^(7/2 : ℝ) := by
    rw [← Real.rpow_mul_natCast hR]; norm_num
  simp only [mul_pow, div_pow, Real.sq_sqrt (show 0 ≤ 25165824*C*L by positivity),
    hxpow, hTpow, hRpow]
  ring


end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
