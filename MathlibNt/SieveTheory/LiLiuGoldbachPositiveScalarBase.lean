import MathlibNt.SieveTheory.LiLiuGoldbachWeightFiveNegativeScalars
import MathlibNt.SieveTheory.LiLiuGoldbachS3IntegralScalarPolynomial

open Set MeasureTheory Finset
open MathlibNt.SieveTheory.SwitchingPrinciple
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- Exact cancellation of the Euler normalization, without an estimate for gamma. -/
theorem goldbachPositiveScalar_exp_cancel (x : ℝ) :
    Real.exp (-Real.eulerMascheroniConstant) * (Real.exp Real.eulerMascheroniConstant * x) = x := by
  rw [← mul_assoc, ← Real.exp_add]
  simp

/-- Literal change of variables used only on the existing lower-factor domain. -/
theorem goldbachPositiveScalar_change (v : ℝ) (hv : 3 ≤ v) :
    let z := (v-3)/(v-1)
    0 ≤ z ∧ z < 1 ∧ (3-z)/(1-z) = v ∧
      (1/(1-z)-1/(3-z))*(2/(v-1)^2) = 1/v := by
  dsimp
  have h1 : 0 < v-1 := by linarith
  have h0 : v ≠ 0 := by linarith
  have hz : (v-3)/(v-1) < 1 := (div_lt_iff₀ h1).2 (by linarith)
  have hn : 1-(v-3)/(v-1) ≠ 0 := by linarith
  have h3 : 3-(v-3)/(v-1) ≠ 0 := by linarith
  refine ⟨div_nonneg (by linarith) h1.le, hz, ?_, ?_⟩
  · field_simp
    ring
  · field_simp [h0]
    ring_nf
    simp [h0]
    ring

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig