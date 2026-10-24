import MathlibNt.Wu2008DoubleSieve.SecondFunctionalPositiveMatrix
import MathlibNt.Wu2008DoubleSieve.MotherPairClassicalTriangles

namespace Wu2008DoubleSieve.SecondFunctionalSignedCore
open Set MeasureTheory MotherPair SecondFunctionalPositive
open scoped Interval

/-- Join the actual three rectangles before removing the upper triangle. -/
theorem classical_strip {p : SecondFunctionalParameters} (hp : AnalyticParameters p) :
    classicalIntegral p .gammaSeven + classicalIntegral p .gammaEight +
      classicalIntegral p .gammaSix =
    ∫ t in (1/p.S)..(1/p.kappa1), ∫ u in t..(1/p.kappa3), gamma5MassKernel t u := by
  linarith only [classical_gammaSixSevenEight_strip hp]

/-- Actual four-rectangle producer; no mass or integrability premise. -/
theorem classical_eq_triangles {p : SecondFunctionalParameters} (hp : AnalyticParameters p) :
    SecondFunctionalCoupledFeedback.classical p =
      fourthRowClassicalTriangle p.S p.kappa2 + fourthRowClassicalTriangle p.S p.kappa3 -
        fourthRowClassicalTriangle p.kappa1 p.kappa3 := by
  unfold SecondFunctionalCoupledFeedback.classical
  have h5 := classical_gammaFive_triangle hp
  have h678 := classical_gammaSixSevenEight_triangles hp
  linarith only [h5,h678]

theorem original_classical_eq_triangles (i : Fin 4) :
    SecondFunctionalCoupledFeedback.classical (parameters i) =
      fourthRowClassicalTriangle (parameters i).S (parameters i).kappa2 +
      fourthRowClassicalTriangle (parameters i).S (parameters i).kappa3 -
      fourthRowClassicalTriangle (parameters i).kappa1 (parameters i).kappa3 :=
  classical_eq_triangles (parameters_analytic i)

end Wu2008DoubleSieve.SecondFunctionalSignedCore
