import FirstCRationalCoefficients

noncomputable section
open Real Set MeasureTheory
open scoped Interval
open FirstIntegralRecovery
namespace FirstCRationalPayment

/-- The same prescribed kernel at the original fixed parameter, with no new cut. -/
def literalKernel (u : ℝ) : ℝ :=
  (2*((u-2)/(u+2))+2*((u-2)/(u+2))^3/3+
    (2*((u-2)/(3*u-2))+2*((u-2)/(3*u-2))^3/3))/u *
  (2*((927/200-u)/(3*u+1727/200))+2*((927/200-u)/(3*u+1727/200))^3/3+
    (2*((927/200-u)/(u+3581/200))+2*((927/200-u)/(u+3581/200))^3/3))

theorem cLowerKernel_literal {u : ℝ} (hu : u ∈ Icc 2 (927/200)) :
    cLowerKernel (1327/200) u = literalKernel u := by
  have h1 : 1 ≤ u-1 := by linarith [hu.1]
  have hr : 1 ≤ ((1327:ℝ)/200-1)/(u+1) :=
    ratio_ge_one (show u ∈ Icc 2 ((1327:ℝ)/200-2) by constructor <;> linarith [hu.1,hu.2])
  have hn : u+1 ≠ 0 := by linarith [hu.1]
  have hn3 : 3*u+1727/200 ≠ 0 := by linarith [hu.1]
  have hn4 : u+3581/200 ≠ 0 := by linarith [hu.1]
  unfold cLowerKernel
  rw [splitL_rational h1,splitL_rational hr]
  have hA : (((1327:ℝ)/200-1)/(u+1)-1)/(((1327:ℝ)/200-1)/(u+1)+3) =
      (927/200-u)/(3*u+1727/200) := by field_simp; ring
  have hB : (((1327:ℝ)/200-1)/(u+1)-1)/(3*(((1327:ℝ)/200-1)/(u+1))+1) =
      (927/200-u)/(u+3581/200) := by field_simp; ring
  rw [hA,hB]
  have hC : u-1-1 = u-2 := by ring
  have hD : u-1+3 = u+2 := by ring
  have hE : 3*(u-1)+1 = 3*u-2 := by ring
  rw [hC,hD,hE]
  rfl

theorem literalKernel_principalParts {u : ℝ} (hu : 2 ≤ u) :
    literalKernel u = fixedKernel u := by
  have h0 : u ≠ 0 := by linarith
  have h1 : u+2 ≠ 0 := by linarith
  have h2 : 3*u-2 ≠ 0 := by linarith
  have h3 : 3*u+1727/200 ≠ 0 := by linarith
  have h4 : u+3581/200 ≠ 0 := by linarith
  have h5 : u-2/3 ≠ 0 := by linarith
  have h6 : u-(-1727/600) ≠ 0 := by linarith
  unfold literalKernel fixedKernel part0 part1 part2 part3 part4 poleKernel
  field_simp (disch := (first | positivity | linarith))
  ring

end FirstCRationalPayment
