import MathlibNt.SieveTheory.LiLiuGoldbachB9HighFirstNormalized

open scoped BigOperators
open Finset
open MathlibNt.SieveTheory.LiuWeight

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

#print axioms goldbachC10HighFirstPairs_eq_filter
#print axioms goldbachS5HighFirstActualAtoms
#print axioms goldbachS5HighFirstClosed_eq_card
#print axioms goldbachB9HighFirstAtoms_eq_filter
#print axioms goldbachB9HighFirstSiftedAtoms_eq_filter
#print axioms goldbachS5HighFirstSwitch_mem
#print axioms goldbachS5HighFirstClosed_le_sifted
#print axioms goldbachS5HighFirstClosed_le_sifted_normalized
#print axioms goldbachB9HighFirstSupport
#print axioms goldbachX9High
#print axioms goldbachK9High
#print axioms goldbachB9HighFirstSupport_subset
#print axioms goldbachX9High_eq_pair_sum
#print axioms goldbachK9High_eq_support_sum
#print axioms goldbachB9HighFirstLiWeight_bounds_eventually
#print axioms goldbachX9High_nonneg_eventually
#print axioms goldbachB9HighFirst_gate_le_full
#print axioms goldbachB9HighFirst_gate_log_saving
#print axioms goldbachK9High_nonneg
#print axioms goldbachB9HighFirst_proxy_eq
#print axioms goldbachX9High_le_kernel_eventually
#print axioms goldbachB9HighFirstDivCount
#print axioms goldbachX9HighGated
#print axioms goldbachX9HighDeleted
#print axioms goldbachB9HighFirstGatedRemainder
#print axioms goldbachB9HighFirstCommonRemainder
#print axioms goldbachX9High_eq_gated_add_deleted
#print axioms goldbachB9HighFirstCommonRemainder_eq
#print axioms goldbachB9HighFirstCommonRemainder_one
#print axioms goldbachB9HighFirstSupport_eventually_panInterval
#print axioms goldbachB9HighFirstDivCount_eq_product_sum
#print axioms goldbachB9HighFirstGatedRemainder_eq_panError
#print axioms goldbachB9HighFirstGatedRemainder_log_saving
#print axioms abs_goldbachB9HighFirstCommonRemainder_le
#print axioms goldbachB9HighFirstCommonRemainder_log_saving
#print axioms goldbachB9HighFirstBoundingSieve_rem_eq
#print axioms goldbachB9HighFirst_upperErrSum_log_saving
#print axioms goldbachB9HighFirstSiftedCount_normalized_kernel
#print axioms goldbachS5HighFirstClosed_normalized_upper

example (N : ℕ) :
    goldbachX9High N =
      ∑ m ∈ goldbachC10ProductSupport N ((N : ℝ) ^ (1 / 10 : ℝ))
        ((N : ℝ) ^ (1 / 3 : ℝ)),
        liuLogarithmicIntegral (2 / Real.log 2) ((N : ℝ) / m) := rfl

example (N : ℕ) :
    goldbachK9High N =
      ∑ rs ∈ goldbachC10Pairs N ((N : ℝ) ^ (1 / 10 : ℝ)) ((N : ℝ) ^ (1 / 3 : ℝ)),
        1 / ((rs.1 * rs.2 : ℕ) *
          (1 - Real.log (rs.1 * rs.2 : ℕ) / Real.log (N : ℝ))) := rfl

private theorem highFirstAudit_mother_iff (N : ℕ) (hN : 2 ≤ N)
    (x : Σ _rs : ℕ × ℕ, ℕ) :
    x ∈ goldbachB10Atoms N 0 ((N : ℝ) ^ (1 / 10 : ℝ)) ((N : ℝ) ^ (1 / 3 : ℝ)) ↔
      x.1 ∈ goldbachC10Pairs N ((N : ℝ) ^ (1 / 10 : ℝ)) ((N : ℝ) ^ (1 / 3 : ℝ)) ∧
        x.2.Prime ∧ goldbachC10Prod x.1 * x.2 < N := by
  classical
  rw [goldbachB9HighFirstAtoms_eq_filter N hN, mem_filter,
    mem_goldbachB9PlusAtoms_iff, goldbachC10HighFirstPairs_eq_filter N hN, mem_filter]
  change ((_ ∧ _ ∧ goldbachC10Prod x.1 * x.2 < N) ∧ _) ↔ _
  tauto

example (N : ℕ) (hN : 2 ≤ N) (rs : ℕ × ℕ)
    (hrs : rs ∈ goldbachC10Pairs N ((N : ℝ) ^ (1 / 10 : ℝ)) ((N : ℝ) ^ (1 / 3 : ℝ)))
    (hprod : goldbachC10Prod rs * rs.1 < N) :
    (⟨rs, rs.1⟩ : Σ _rs : ℕ × ℕ, ℕ) ∈ goldbachB10Atoms N 0
      ((N : ℝ) ^ (1 / 10 : ℝ)) ((N : ℝ) ^ (1 / 3 : ℝ)) :=
  (highFirstAudit_mother_iff N hN _).mpr
    ⟨hrs, (mem_goldbachC10Pairs_iff.mp hrs).1, hprod⟩

example (N : ℕ) (hN : 2 ≤ N) (r q : ℕ)
    (hrs : (r, r) ∈ goldbachC10Pairs N
      ((N : ℝ) ^ (1 / 10 : ℝ)) ((N : ℝ) ^ (1 / 3 : ℝ)))
    (hq : q.Prime) (hprod : r * r * q < N) :
    (⟨(r, r), q⟩ : Σ _rs : ℕ × ℕ, ℕ) ∈ goldbachB10Atoms N 0
      ((N : ℝ) ^ (1 / 10 : ℝ)) ((N : ℝ) ^ (1 / 3 : ℝ)) :=
  (highFirstAudit_mother_iff N hN _).mpr ⟨hrs, hq, hprod⟩

example (N : ℕ) (hN : 2 ≤ N) (rs : ℕ × ℕ)
    (hrs : rs ∈ goldbachC9Pairs N) (hedge : (rs.1 : ℝ) = (N : ℝ) ^ (1 / 10 : ℝ)) :
    rs ∈ goldbachC10Pairs N ((N : ℝ) ^ (1 / 10 : ℝ)) ((N : ℝ) ^ (1 / 3 : ℝ)) := by
  classical
  rw [goldbachC10HighFirstPairs_eq_filter N hN]
  exact mem_filter.mpr ⟨hrs, hedge.ge⟩

example (N : ℕ) (hN : 2 ≤ N) (m : ℕ) (hm : m ∈ goldbachB9HighFirstSupport N) :
    (N : ℝ) ^ (65 / 159 : ℝ) ≤ m ∧ (m : ℝ) ≤ (N : ℝ) ^ (2 / 3 : ℝ) :=
  goldbachB9ProductSupport_pan_bounds hN (goldbachB9HighFirstSupport_subset N hN hm)

example (N m : ℕ) :
    |goldbachC10CoeffReal N ((N : ℝ) ^ (1 / 10 : ℝ)) ((N : ℝ) ^ (1 / 3 : ℝ)) m| ≤ 1 :=
  abs_goldbachC10CoeffReal_le_one N _ _ m

example (N : ℕ) (hN : 2 ≤ N) (m q : ℕ) (hm : m ∈ goldbachB9HighFirstSupport N) :
    m * q < N ↔ m * q ≤ N :=
  goldbachB9Product_mul_lt_iff_le (goldbachB9HighFirstSupport_subset N hN hm)

example (N : ℕ) :
    goldbachX9HighDeleted N 1 = 0 ∧
      goldbachB9HighFirstCommonRemainder N 1 = goldbachB9HighFirstGatedRemainder N 1 :=
  goldbachB9HighFirstCommonRemainder_one N

example (N d : ℕ) (hEven : Even N) (Z : ℝ) (hd : d ∣ goldbachB10ProdPrimes N Z) :
    (goldbachB10BoundingSieve N hEven 0 ((N : ℝ) ^ (1 / 10 : ℝ))
      ((N : ℝ) ^ (1 / 3 : ℝ)) Z
      (∑ m ∈ goldbachC10ProductSupport N ((N : ℝ) ^ (1 / 10 : ℝ))
        ((N : ℝ) ^ (1 / 3 : ℝ)),
        liuLogarithmicIntegral (2 / Real.log 2) ((N : ℝ) / m))).rem d =
      goldbachB9HighFirstCommonRemainder N d :=
  goldbachB9HighFirstBoundingSieve_rem_eq hEven hd

theorem goldbachS5HighFirst_actual_instance
    (δ ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε) (hεu : ε < (2 : ℝ) / 15) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
      (goldbachS5Closed (goldbachDifferenceCarrier N ε) N
        ((N : ℝ) ^ (1 / 10 : ℝ)) ((N : ℝ) ^ (1 / 3 : ℝ)) : ℝ) ≤
        ((8 + δ) *
          (∑ rs ∈ goldbachC10Pairs N ((N : ℝ) ^ (1 / 10 : ℝ)) ((N : ℝ) ^ (1 / 3 : ℝ)),
            1 / ((rs.1 * rs.2 : ℕ) *
              (1 - Real.log (rs.1 * rs.2 : ℕ) / Real.log (N : ℝ)))) + δ) *
          (SingularSeries.liuSingularSeries N * (N : ℝ) / Real.log (N : ℝ) ^ 2) :=
  goldbachS5HighFirstClosed_normalized_upper δ ε hδ hε hεu

#print axioms goldbachS5HighFirst_actual_instance

example (δ : ℝ) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
      (goldbachS5Closed (goldbachDifferenceCarrier N (1 / 15)) N
        ((N : ℝ) ^ (1 / 10 : ℝ)) ((N : ℝ) ^ (1 / 3 : ℝ)) : ℝ) ≤
        ((8 + δ) * goldbachK9High N + δ) *
          (SingularSeries.liuSingularSeries N * (N : ℝ) / Real.log (N : ℝ) ^ 2) :=
  goldbachS5HighFirstClosed_normalized_upper δ (1 / 15) hδ (by norm_num) (by norm_num)

#check goldbachC10HighFirstPairs_eq_filter
#check goldbachS5HighFirstActualAtoms
#check goldbachS5HighFirstClosed_eq_card
#check goldbachB9HighFirstAtoms_eq_filter
#check goldbachB9HighFirstSiftedAtoms_eq_filter
#check goldbachS5HighFirstSwitch_mem
#check goldbachS5HighFirstClosed_le_sifted
#check goldbachS5HighFirstClosed_le_sifted_normalized
#check goldbachB9HighFirstSupport
#check goldbachX9High
#check goldbachK9High
#check goldbachB9HighFirstSupport_subset
#check goldbachX9High_eq_pair_sum
#check goldbachK9High_eq_support_sum
#check goldbachB9HighFirstLiWeight_bounds_eventually
#check goldbachX9High_nonneg_eventually
#check goldbachB9HighFirst_gate_le_full
#check goldbachB9HighFirst_gate_log_saving
#check goldbachK9High_nonneg
#check goldbachB9HighFirst_proxy_eq
#check goldbachX9High_le_kernel_eventually
#check goldbachB9HighFirstDivCount
#check goldbachX9HighGated
#check goldbachX9HighDeleted
#check goldbachB9HighFirstGatedRemainder
#check goldbachB9HighFirstCommonRemainder
#check goldbachX9High_eq_gated_add_deleted
#check goldbachB9HighFirstCommonRemainder_eq
#check goldbachB9HighFirstCommonRemainder_one
#check goldbachB9HighFirstSupport_eventually_panInterval
#check goldbachB9HighFirstDivCount_eq_product_sum
#check goldbachB9HighFirstGatedRemainder_eq_panError
#check goldbachB9HighFirstGatedRemainder_log_saving
#check abs_goldbachB9HighFirstCommonRemainder_le
#check goldbachB9HighFirstCommonRemainder_log_saving
#check goldbachB9HighFirstBoundingSieve_rem_eq
#check goldbachB9HighFirst_upperErrSum_log_saving
#check goldbachB9HighFirstSiftedCount_normalized_kernel
#check goldbachS5HighFirstClosed_normalized_upper
#check goldbachS5HighFirst_actual_instance

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig