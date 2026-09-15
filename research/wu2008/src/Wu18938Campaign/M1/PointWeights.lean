import WR2MotherMovingRange

namespace Wu18938Campaign.M1

open Finset Wu2008DoubleSieve WuPaper.R2Mother
open scoped Classical

noncomputable def pointSieve (N p d M : ℕ) (y : ℝ) : ℤ :=
  if p ∈ sieveCarrier N d M y then 1 else 0

noncomputable def pointOrdinary (N p : ℕ) : ℤ :=
  if p ∈ MathlibNt.Wu2008DoubleSieve.wuPrimeComplements N then 1 else 0

noncomputable def pointLower (N p : ℕ) (z w : ℝ) : ℤ :=
  if p ∈ sieveCarrier N 1 N z then lowerWeight N N (N - p) z w else 0

noncomputable def pointS4 (N p : ℕ) (z w : ℝ) : ℤ :=
  ∑ t ∈ orderedTriples (primeWindow N z w),
    pointSieve N p (t.1 * t.2.1 * t.2.2) (N * t.1) (t.2.1 : ℝ)

noncomputable def pointRetained (N p : ℕ) (z w u v : ℝ) : ℤ :=
  (∑ t ∈ orderedTriples (primeWindow N z v) \
      (orderedTriples (primeWindow N z w) ∪ s3SecondRange N z w u ∪
        s3ThirdRange N w u),
    pointSieve N p (t.1 * t.2.1 * t.2.2) (N * t.1) (t.2.1 : ℝ)) +
  (∑ t ∈ orderedTriples (primeWindow N z w),
    (pointSieve N p (t.1 * t.2.1 * t.2.2) (N * t.1) (t.2.1 : ℝ) -
      pointSieve N p (t.1 * t.2.1 * t.2.2) N (t.2.1 : ℝ))) +
  (∑ t ∈ s3SecondRange N z w u,
    (pointSieve N p (t.1 * t.2.1 * t.2.2) (N * t.1) (t.2.1 : ℝ) -
      pointSieve N p (t.1 * t.2.1 * t.2.2) N (t.2.1 : ℝ))) +
  ∑ t ∈ s3ThirdRange N w u,
    (pointSieve N p (t.1 * t.2.1 * t.2.2) (N * t.1) (t.2.1 : ℝ) -
      pointSieve N p (t.1 * t.2.1 * t.2.2) (N * t.1) (t.2.2 : ℝ))

noncomputable def pointPairBudget (N p : ℕ) (w u : ℝ) : ℤ :=
  ∑ t ∈ lowerPairs N N w u,
    if p ∈ sieveEndpointLoss N (t.1 * t.2) (N * t.1) (t.2 : ℝ) then 1 else 0

noncomputable def pointVariableSlack (N p : ℕ) (w u : ℝ) : ℤ :=
  (∑ t ∈ (lowerPairs N N w u).filter (fun t => (t.1 : ℝ) < u),
    pointSieve N p (t.1 * t.2) (N * t.1)
      (Real.sqrt ((N : ℝ) / ((t.1 : ℝ) * t.2)))) +
  (∑ t ∈ (lowerPairs N N w u).filter (fun t => (t.1 : ℝ) < u),
    ∑ c ∈ (primeWindow N (t.2 : ℝ)
        (Real.sqrt ((N : ℝ) / ((t.1 : ℝ) * t.2)))).filter (fun c => t.2 < c),
      pointSieve N p (t.1 * t.2 * c) (N * t.1) (c : ℝ)) +
  pointPairBudget N p w u -
  ∑ t ∈ (lowerPairs N N w u).filter (fun t => (t.1 : ℝ) < u),
    pointSieve N p (t.1 * t.2) (N * t.1) (t.2 : ℝ)

noncomputable def pointOuterSlack (N p : ℕ) (z w : ℝ) : ℤ :=
  2 * pointOrdinary N p - pointLower N p z w

noncomputable def pointGains (N p : ℕ) (z w u v : ℝ) : ℤ :=
  pointRetained N p z w u v + pointS4 N p w u +
    pointVariableSlack N p w u + pointOuterSlack N p w u +
    pointOuterSlack N p z v

noncomputable def pointExcess (N p : ℕ) (z w u V : ℝ) : ℤ :=
  ∑ t ∈ s3Upsilon11Excess N z w u V,
    pointSieve N p (t.1 * t.2.1 * t.2.2.1 * t.2.2.2) N (t.2.1 : ℝ)

theorem pointSieve_nonneg (N p d M : ℕ) (y : ℝ) :
    0 ≤ pointSieve N p d M y := by
  unfold pointSieve
  split_ifs <;> omega

theorem pointSieve_sum (N d M : ℕ) (y : ℝ) :
    (∑ p ∈ range (N + 1), pointSieve N p d M y) = sieveCount N d M y := by
  unfold pointSieve sieveCount
  rw [sum_boole]
  congr 2
  ext p
  simp only [mem_filter, sieveCarrier]
  tauto

theorem pointS4_eq_firstTwo {N p : ℕ} {z w : ℝ}
    (hp : p ∈ sieveCarrier N 1 N z) :
    pointS4 N p z w = ((firstTwoTriples
      (divisorsIn (primeWindow N z w) (N - p))).card : ℤ) := by
  unfold pointS4 pointSieve
  rw [firstTwoTriples_divisorsIn, ← sum_boole]
  apply sum_congr rfl
  rintro ⟨a, b, c⟩ ht
  have hc := tripleCarrier_eq N 1 N ht
  simp only [one_mul] at hc
  have hm := congrArg (fun S : Finset ℕ => p ∈ S) hc
  simp only [mem_filter, hp, true_and, Nat.div_one] at hm
  simp only [← hm]

theorem pointSieve_zero_of_not_dvd {N p d M : ℕ} (y : ℝ)
    (hd : ¬d ∣ N - p) : pointSieve N p d M y = 0 := by
  apply if_neg
  intro hp
  exact hd (mem_filter.mp hp).2.2.1

end Wu18938Campaign.M1
