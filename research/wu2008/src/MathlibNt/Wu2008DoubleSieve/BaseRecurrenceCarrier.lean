import MathlibNt.Wu2008DoubleSieve.BaseRecurrenceCount

namespace Wu2008DoubleSieve.BaseRecurrenceLower

/-- The carrier allows the complement 1. It has no lower bound on factor sizes. -/
theorem complement_one_allowed {p : ℕ} (hp : Nat.Prime p) :
    p ∈ MathlibNt.Wu2008DoubleSieve.wuPrimeComplements (p+1) := by
  simp [MathlibNt.Wu2008DoubleSieve.wuPrimeComplements,hp]

/-- Complement zero is excluded by positivity, not by a convention about its factors. -/
theorem complement_zero_excluded (N : ℕ) :
    N ∉ MathlibNt.Wu2008DoubleSieve.wuPrimeComplements N := by
  simp [MathlibNt.Wu2008DoubleSieve.wuPrimeComplements]

/-- Literal full K: original positive weights, both G terms and all negative weights. -/
theorem literal_complete_coefficient_gt_newBalance :
    newBalance <
      24*wuLowerCoefficient (1/(2*truncatedSixthLowerAlpha))+
      8*wuLowerCoefficient (1/(2*truncatedSixthLowerBeta))+fifthPairFlin+
      truncatedSixthLowerF6lin+47/481250-
      SingleUpperClassicalLimit.Glin (1/3)-
      SingleUpperClassicalLimit.Glin truncatedSixthLowerSigma-8*J9-
      16*SeventhEighth.J7-8*SeventhEighth.J8-
      8*FourRoughClosedMass.I10-8*FourRoughClosedMass.I11 :=
  complete_coefficient_gt_newBalance

#print axioms complement_one_allowed
#print axioms complement_zero_excluded
#print axioms literal_complete_coefficient_gt_newBalance
end Wu2008DoubleSieve.BaseRecurrenceLower
