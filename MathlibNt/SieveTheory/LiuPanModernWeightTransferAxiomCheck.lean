import MathlibNt.SieveTheory.LiuPanUnweightedToWeighted
import MathlibNt.SieveTheory.LiuPanConvolutionSourceCount
import MathlibNt.SieveTheory.LiuPanLiMainTermEnvelope

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

#print axioms modulus_mul_abs_liuMainPanCoprimeIntervalSum_le
#print axioms modulus_mul_liuMainPanCoprimeIntervalMaxL_le
#print axioms exists_liuPanWeightedSum_sq_le_unweighted
#print axioms LiuPanUnweightedTheorem2Specialization.to_corollary230
#print axioms LiuPanUnweightedTheorem2Specialization.to_canonicalCoprimeTheorem
#print axioms liuPanActualError_one
#print axioms liuPanActualError_zero
#check LiuPanUnweightedTheorem2Specialization.to_corollary230
#print LiuPanUnweightedTheorem2Specialization

end MathlibNt.SieveTheory.LiuWeight

#print axioms MathlibNt.SieveTheory.LiuWeight.liuActualEnvelopeConstant_pos

#print axioms MathlibNt.SieveTheory.LiuWeight.liuCoprimeIntervalCount_nonneg

#print axioms MathlibNt.SieveTheory.LiuWeight.modulus_mul_liuCoprimeIntervalCount_le

#print axioms MathlibNt.SieveTheory.LiuWeight.liuMainPanCoprimeIntervalMaxL_nonneg

#print axioms MathlibNt.SieveTheory.LiuWeight.liuPanActualError_nonneg

#print axioms MathlibNt.SieveTheory.LiuWeight.liuPanWeightedSum_eq_squarefree

#print axioms MathlibNt.SieveTheory.LiuWeight.panSourceStrictModulusCutoff_mem_le

#print axioms MathlibNt.SieveTheory.LiuWeight.liuPanSquarefreeCarrier_subset

#print axioms MathlibNt.SieveTheory.LiuWeight.liuPanSquarefreeErrorSum_le_unweighted