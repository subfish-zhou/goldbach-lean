import MathlibNt.SieveTheory.LiLiuGoldbachB9MainGate

open scoped BigOperators
open MathlibNt.SieveTheory.LiuWeight
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

#check goldbachB9PlusLiWeight
#check goldbachB9PlusMainMass
#check goldbachB9PlusMainMass_eq_pair_sum
#check goldbachB9ProductSupport_bounds
#check goldbachB9PlusLiWeight_bounds_eventually
#check goldbachB9PlusMainMass_nonneg_eventually
#check goldbachB9PlusLiWeight_sum_gateLoss_le_logCube
#check goldbachB9PlusLiWeight_sum_gateLoss_log_saving_one
#check goldbachB9PlusLiWeight_sum_gateLoss_log_saving

#print axioms goldbachB9PlusLiWeight
#print axioms goldbachB9PlusMainMass
#print axioms goldbachB9PlusMainMass_eq_pair_sum
#print axioms goldbachB9ProductSupport_bounds
#print axioms goldbachB9PlusLiWeight_bounds_eventually
#print axioms goldbachB9PlusMainMass_nonneg_eventually
#print axioms goldbachB9PlusLiWeight_sum_gateLoss_le_logCube
#print axioms goldbachB9PlusLiWeight_sum_gateLoss_log_saving_one
#print axioms goldbachB9PlusLiWeight_sum_gateLoss_log_saving

example (N m : ℕ) :
    goldbachB9PlusLiWeight N m =
      liuLogarithmicIntegral (2 / Real.log 2) ((N : ℝ) / (m : ℝ)) := rfl

example (N : ℕ) :
    goldbachB9PlusMainMass N =
      ∑ m ∈ goldbachC10ProductSupport N ((N : ℝ) ^ (4 / 53 : ℝ))
        ((N : ℝ) ^ (1 / 3 : ℝ)), goldbachB9PlusLiWeight N m := rfl

example :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      ∀ m ∈ goldbachC10ProductSupport N ((N : ℝ) ^ (4 / 53 : ℝ))
          ((N : ℝ) ^ (1 / 3 : ℝ)),
        2 ≤ (N : ℝ) / m ∧ 0 ≤ goldbachB9PlusLiWeight N m ∧
          |goldbachB9PlusLiWeight N m| ≤ 2 * (N : ℝ) / m :=
  goldbachB9PlusLiWeight_bounds_eventually

example :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → ∀ Q : ℕ, Q ≤ N →
      ∑ d ∈ Finset.Icc 1 Q,
        gateLoss N ((N : ℝ) ^ (4 / 53 : ℝ)) ((N : ℝ) ^ (1 / 3 : ℝ))
          (goldbachB9PlusLiWeight N) d ≤
        (4 * 2 * (N : ℝ) / (N : ℝ) ^ (4 / 53 : ℝ)) *
          (1 + Real.log (N : ℝ)) ^ 3 :=
  goldbachB9PlusLiWeight_sum_gateLoss_le_logCube

example (U : ℝ) (hU : 0 < U) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, 4 ≤ N₀ ∧
      ∀ N : ℕ, N₀ ≤ N → ∀ Q : ℕ, Q ≤ N →
        ∑ d ∈ Finset.Icc 1 Q,
          gateLoss N ((N : ℝ) ^ (4 / 53 : ℝ)) ((N : ℝ) ^ (1 / 3 : ℝ))
            (goldbachB9PlusLiWeight N) d ≤ C * (N : ℝ) / Real.log (N : ℝ) ^ U :=
  goldbachB9PlusLiWeight_sum_gateLoss_log_saving U hU