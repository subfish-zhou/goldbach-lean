import MathlibNt.SieveTheory.Distribution.LiuPan.LiuPanUnweightedToWeighted
import MathlibNt.SieveTheory.Distribution.LiuPan.LiuPanConvolutionSourceCount
import MathlibNt.SieveTheory.Distribution.LiuPan.LiuPanLiMainTermEnvelope

open Finset
open scoped BigOperators
namespace MathlibNt.SieveTheory.LiuWeight

/-- q=1 retains the canonical residue 0 in the actual maximum. -/
theorem liuPanActualError_one (κ : ℝ) (N : ℕ) (B : ℝ) :
    liuPanActualError κ N B 1 =
      |liuMainPanCoprimeIntervalSum (liuLogarithmicIntegral κ) N
        (liuPanSourceIntervalLower N B) (liuPanSourceIntervalUpper N) 1 0
        (liuWeight N (liuSourceZ10 N) (liuSourceY3 N))| := by
  simp [liuPanActualError, liuMainPanCoprimeIntervalMaxL,
    AnalyticNumberTheory.Sieve.unitResidues]

/-- q=0 vanishes both in the source residue maximum and in the weight. -/
theorem liuPanActualError_zero (κ : ℝ) (N : ℕ) (B : ℝ) :
    liuPanActualError κ N B 0 = 0 ∧
      (((ArithmeticFunction.moebius 0 : ℤ) : ℝ) ^ 2) = 0 := by
  simp [liuPanActualError, liuMainPanCoprimeIntervalMaxL]

/-- Genuine original consumer, with precisely the single unweighted analytic input. -/
theorem LiuPanUnweightedTheorem2Specialization.to_canonicalCoprimeTheorem
    (h : LiuPanUnweightedTheorem2Specialization) : LiuPanCanonicalCoprimeTheorem :=
  h.to_corollary230.to_canonicalCoprimeTheorem


end MathlibNt.SieveTheory.LiuWeight
