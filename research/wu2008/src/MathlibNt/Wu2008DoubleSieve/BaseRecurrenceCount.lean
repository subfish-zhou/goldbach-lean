import MathlibNt.Wu2008DoubleSieve.BaseRecurrenceBalance

namespace Wu2008DoubleSieve.BaseRecurrenceLower
open Real SharpLogRecurrence

noncomputable def exactBalance : ℝ :=
  98697095732325861981554436884516820894316954154236270988608761224410668869899 /
    57260466202464827763752800279172533130654742579192222367595883791237146875000

theorem newBalance_eq_exact : newBalance = exactBalance := by
  norm_num [newBalance,newBase,exactBalance,
    RationalMovingSixth.rationalSixth,RationalMovingSixth.quadraticCoefficient,
    RationalMovingSixth.linearCoefficient,RationalMovingSixth.constantCoefficient,
    RationalMovingSixth.initialLogCoefficient,RationalMovingSixth.terminalLogCoefficient,
    RationalMovingSixth.e,SharpMassBalance.m,SharpMassBalance.lam,
    SharpMassBalance.a,SharpMassBalance.b,lowerLog,upperLog,
    VariableCoefficientBalance.rationalG,VariableGIntegral.logCoefficient,
    VariableGIntegral.linearCoefficient,VariableGIntegral.a,VariableGIntegral.s,VariableGIntegral.c,
    SharpSingleBalance.c,SharpSingleBalance.a,
    truncatedSixthLowerAlpha,truncatedSixthLowerBeta,truncatedSixthLowerSigma]

theorem newBalance_below_benchmark : newBalance < (899/250 : ℝ) := by
  rw [newBalance_eq_exact]
  norm_num [exactBalance]

theorem newBalance_pos : 0 < newBalance := by
  rw [newBalance_eq_exact]
  norm_num [exactBalance]

/-- One threshold serves BOTH formulations of the actual ordinary P2 count. -/
theorem actual_count_same_threshold :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (newBalance*wuSingularSeries N*N/log N^(2 : ℕ) ≤
        4*((MathlibNt.Wu2008DoubleSieve.wuPrimeComplements N).card : ℝ)) ∧
      ((newBalance/4)*wuSingularSeries N*N/log N^(2 : ℕ) ≤
        ((MathlibNt.Wu2008DoubleSieve.wuPrimeComplements N).card : ℝ)) := by
  have hε : 0 < TruncatedElevenClassicalCountLower.classicalCoefficient-newBalance :=
    sub_pos.mpr complete_coefficient_gt_newBalance
  obtain ⟨T,hT,hcount⟩ :=
    TruncatedElevenClassicalCountLower.actual_count_lower_full_coefficient hε
  refine ⟨T,hT,?_⟩
  intro N hN he
  have h := hcount N hN he
  change (TruncatedElevenClassicalCountLower.classicalCoefficient-
    (TruncatedElevenClassicalCountLower.classicalCoefficient-newBalance))*
    wuSingularSeries N*N/log N^(2 : ℕ) ≤
    4*((MathlibNt.Wu2008DoubleSieve.wuPrimeComplements N).card : ℝ) at h
  rw [sub_sub_cancel] at h
  refine ⟨h,?_⟩
  have hid : (newBalance/4)*wuSingularSeries N*N/log N^(2 : ℕ) =
      (newBalance*wuSingularSeries N*N/log N^(2 : ℕ))/4 := by ring
  rw [hid]
  exact (div_le_iff₀ (by norm_num : (0 : ℝ) < 4)).2 (by linarith only [h])

/-- The new rational coefficient is actually consumed, with no epsilon hypothesis. -/
theorem actual_count_exact_rational :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (98697095732325861981554436884516820894316954154236270988608761224410668869899 /
        229041864809859311055011201116690132522618970316768889470383535164948587500000 : ℝ)*
        wuSingularSeries N*N/log N^(2 : ℕ) ≤
          ((MathlibNt.Wu2008DoubleSieve.wuPrimeComplements N).card : ℝ) := by
  obtain ⟨T,hT,hcount⟩ := actual_count_same_threshold
  refine ⟨T,hT,?_⟩
  intro N hN he
  have h := (hcount N hN he).2
  have heq : newBalance/4 =
      (98697095732325861981554436884516820894316954154236270988608761224410668869899 /
        229041864809859311055011201116690132522618970316768889470383535164948587500000 : ℝ) := by
    rw [newBalance_eq_exact]
    norm_num [exactBalance]
  rw [heq] at h
  exact h

#print axioms newBalance_eq_exact
#print axioms actual_count_same_threshold
#print axioms actual_count_exact_rational
end Wu2008DoubleSieve.BaseRecurrenceLower
