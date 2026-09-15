import Wu18938Campaign.M1.PointWeights

namespace Wu18938Campaign.M1

open Finset Wu2008DoubleSieve WuPaper.R2Mother
open scoped Classical

theorem pointOrdinary_sum (N : ℕ) :
    (∑ p ∈ range (N + 1), pointOrdinary N p) =
      ((MathlibNt.Wu2008DoubleSieve.wuPrimeComplements N).card : ℤ) := by
  unfold pointOrdinary
  rw [sum_boole]
  congr 2
  ext p
  simp only [mem_filter]
  constructor
  · exact And.right
  · intro hp
    exact ⟨mem_range.mpr (Nat.lt_succ_of_le
      (MathlibNt.Wu2008DoubleSieve.mem_wuPrimeComplements.mp hp).1), hp⟩

theorem pointLower_sum (N : ℕ) (z w : ℝ) :
    (∑ p ∈ range (N + 1), pointLower N p z w) = lowerWeightRHS N z w := by
  rw [lowerWeightRHS_eq_sum]
  unfold pointLower
  rw [← sum_filter]
  congr 1
  ext p
  simp only [mem_filter, sieveCarrier]
  tauto

theorem pointS4_sum (N : ℕ) (z w : ℝ) :
    (∑ p ∈ range (N + 1), pointS4 N p z w) = positiveS4 N z w := by
  unfold pointS4 positiveS4 s3PositiveTripleTerm
  rw [sum_comm]
  simp only [pointSieve_sum]

theorem pointRetained_sum (N : ℕ) (z w u v : ℝ) :
    (∑ p ∈ range (N + 1), pointRetained N p z w u v) =
      s3RetainedTripleMass N z w u v := by
  simp only [pointRetained, s3RetainedTripleMass, s3LeftoverTripleMass,
    s3TripleModulusGain, s3ThirdCutoffGain, s3PositiveTripleTerm,
    sum_add_distrib, sum_sub_distrib,
    sum_comm (s := range (N + 1)), pointSieve_sum]

theorem pointPairBudget_sum (N : ℕ) (w u : ℝ) :
    (∑ p ∈ range (N + 1), pointPairBudget N p w u) =
      s3PairRepeatedBudget N w u := by
  unfold pointPairBudget s3PairRepeatedBudget
  rw [sum_comm]
  apply sum_congr rfl
  intro t _
  rw [sum_boole]
  congr 2
  ext p
  simp only [mem_filter]
  constructor
  · exact And.right
  · intro hp
    exact ⟨mem_range.mpr (Nat.lt_succ_of_le (mem_sieveEndpointLoss.mp hp).1), hp⟩

theorem pointVariableSlack_sum (N : ℕ) (w u : ℝ) :
    (∑ p ∈ range (N + 1), pointVariableSlack N p w u) =
      s3VariableSlack N w u := by
  simp only [pointVariableSlack, s3VariableSlack, variableS3Main, variableS3Triples,
    lowerS3, sum_add_distrib, sum_sub_distrib,
    sum_comm (s := range (N + 1)), pointSieve_sum, pointPairBudget_sum]

theorem pointOuterSlack_sum (N : ℕ) (z w : ℝ) :
    ((∑ p ∈ range (N + 1), pointOuterSlack N p z w : ℤ) : ℝ) =
      lowerWeightOuterSlack N z w -
        (4 * (N : ℝ) / z + 2 * (Real.sqrt N + 1)) := by
  simp only [pointOuterSlack, sum_sub_distrib, ← mul_sum, pointOrdinary_sum,
    pointLower_sum, Int.cast_sub, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast,
    lowerWeightOuterSlack]
  ring

theorem pointGains_sum (N : ℕ) (z w u v : ℝ) :
    ((∑ p ∈ range (N + 1), pointGains N p z w u v : ℤ) : ℝ) =
      quotientAssemblyGains N z w u v -
        (4 * (N : ℝ) / w + 2 * (Real.sqrt N + 1)) -
        (4 * (N : ℝ) / z + 2 * (Real.sqrt N + 1)) := by
  simp only [pointGains, sum_add_distrib, Int.cast_add,
    pointRetained_sum, pointS4_sum, pointVariableSlack_sum, pointOuterSlack_sum,
    quotientAssemblyGains]
  ring

theorem pointExcess_sum (N : ℕ) (z w u V : ℝ) :
    (∑ p ∈ range (N + 1), pointExcess N p z w u V) =
      quotientExcess N z w u V := by
  unfold pointExcess quotientExcess fourQuotientTerm
  rw [sum_comm]
  simp only [pointSieve_sum]

theorem full_signed_residual_sum (N : ℕ) (z w u v V : ℝ) :
    (quotientExcess N z w u V : ℝ) - quotientAssemblyGains N z w u v =
      ((∑ p ∈ range (N + 1),
        (pointExcess N p z w u V - pointGains N p z w u v) : ℤ) : ℝ) -
        (4 * (N : ℝ) / w + 2 * (Real.sqrt N + 1)) -
        (4 * (N : ℝ) / z + 2 * (Real.sqrt N + 1)) := by
  rw [sum_sub_distrib, Int.cast_sub, pointExcess_sum, pointGains_sum]
  ring

end Wu18938Campaign.M1
