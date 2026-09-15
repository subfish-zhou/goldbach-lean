import MathlibNt.Wu2008DoubleSieve.HighSixLowHMother

namespace Wu2008DoubleSieve.HighSixLowHMother
open Real SingleUpperClassicalLimit SingleUpperHIntegral
open TruncatedElevenClassicalCountLower

/-- Fixed delta: the low H integral and actual U3 local j6 integral are joined. -/
noncomputable def psiCoefficient (δ : ℝ) : ℝ :=
  24*wuLowerCoefficient (1/(2*truncatedSixthLowerAlpha)) +
    8*wuLowerCoefficient (1/(2*truncatedSixthLowerBeta)) + fifthPairFlin +
    truncatedSixthLowerF6lin + 47/481250 -
    Gdelta δ (1/3) - Gdelta δ truncatedSixthLowerSigma + gainH34 δ +
    4*firstFunctionalGainPsi δ HighSix.s HighSix.S*HighSix.primeIntegral δ - 8*J9 -
    16*SeventhEighth.J7 - 8*SeventhEighth.J8 -
    8*FourRoughClosedMass.I10 - 8*FourRoughClosedMass.I11

/-- Actual finite prime-complement cardinality, reassembled from actual counts. -/
theorem actual_count_lower {δ ε : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100) (hε : 0 < ε) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (psiCoefficient δ - ε) * wuSingularSeries N * N / log N ^ (2 : ℕ) ≤
        4 * ((MathlibNt.Wu2008DoubleSieve.wuPrimeComplements N).card : ℝ) := by
  obtain ⟨T1, hT1, hmain⟩ :=
    truncated_fixed_classical_lower hδ hδhi (half_pos hε)
  obtain ⟨T2, _, herror⟩ := exceptional_power_error_paid (half_pos hε)
  obtain ⟨T3, _, hcutoff⟩ := fixed_cutoff_eventually_admissible
  refine ⟨max T1 (max T2 T3), hT1.trans (le_max_left _ _), ?_⟩
  intro N hN he
  have hN1 : T1 ≤ N := (le_max_left _ _).trans hN
  have hN23 : max T2 T3 ≤ N := (le_max_right _ _).trans hN
  have hN2 : T2 ≤ N := (le_max_left _ _).trans hN23
  have hN3 : T3 ≤ N := (le_max_right _ _).trans hN23
  have hm := hmain N hN1 he
  change (psiCoefficient δ - ε / 2) * wuSingularSeries N * N /
    log N ^ (2 : ℕ) ≤ (truncatedSixthFixedExpression N : ℝ) at hm
  have hp := herror N hN2
  have hf := truncatedSixth_fixed_le_count (by omega : 4 ≤ N) he (hcutoff N hN3)
  ring_nf at hm hp ⊢
  linarith only [hm, hp, hf]

/-- Expanded source relation explicitly retains the fixed-delta X-integral penalty. -/
theorem psiCoefficient_source {δ : ℝ} (hδhi : δ ≤ 1/100) :
    psiCoefficient δ =
      24*wuLowerCoefficient (1/(2*truncatedSixthLowerAlpha)) +
        8*wuLowerCoefficient (1/(2*truncatedSixthLowerBeta)) + fifthPairFlin +
        truncatedSixthLowerF6lin + 47/481250 -
        Gdelta δ (1/3) - Gdelta δ truncatedSixthLowerSigma + gainH34 δ +
        4*firstFunctionalGainPsiOne HighSix.s HighSix.S*HighSix.primeIntegral δ -
        4*(2*δ/(1-2*δ))*omega3XIntegralEnvelope HighSix.s HighSix.S*HighSix.primeIntegral δ -
        8*J9 - 16*SeventhEighth.J7 - 8*SeventhEighth.J8 -
        8*FourRoughClosedMass.I10 - 8*FourRoughClosedMass.I11 := by
  unfold psiCoefficient
  rw [HighSix.psi_source_penalty hδhi]
  ring

/-- Identify the unchanged remainder of the complete signed mother. -/
theorem coefficient_eq_other (δ : ℝ) :
    psiCoefficient δ = TruncatedElevenHPackedCount.otherCoefficient -
      Gdelta δ (1/3) - Gdelta δ truncatedSixthLowerSigma + gainH34 δ +
      4*firstFunctionalGainPsi δ HighSix.s HighSix.S*HighSix.primeIntegral δ := by
  unfold psiCoefficient TruncatedElevenHPackedCount.otherCoefficient
  ring

/-- Division by four in ordinary-P2 units. Delta is fixed before the threshold. -/
theorem actual_count_quarter {δ ε : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100) (hε : 0 < ε) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ((TruncatedElevenHPackedCount.otherCoefficient -
        Gdelta δ (1/3) - Gdelta δ truncatedSixthLowerSigma + gainH34 δ)/4 +
        firstFunctionalGainPsi δ HighSix.s HighSix.S*HighSix.primeIntegral δ - ε)*
          truncatedSixthMassScale N ≤
            ((MathlibNt.Wu2008DoubleSieve.wuPrimeComplements N).card : ℝ) := by
  obtain ⟨T,hT,h⟩ := actual_count_lower hδ hδhi (show 0 < 4*ε by positivity)
  refine ⟨T,hT,?_⟩
  intro N hN he
  have hn := h N hN he
  rw [coefficient_eq_other] at hn
  unfold truncatedSixthMassScale
  ring_nf at hn ⊢
  linarith only [hn]

/-- Same threshold for the source notation and literal finite carrier. The
fixed-delta X penalty remains visible; no continuity or sign of H is used. -/
theorem actual_ordinaryP2_source_same_threshold {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1/100) (hε : 0 < ε) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      let C := (TruncatedElevenHPackedCount.otherCoefficient -
        Gdelta δ (1/3) - Gdelta δ truncatedSixthLowerSigma + gainH34 δ)/4 +
        firstFunctionalGainPsiOne HighSix.s HighSix.S*HighSix.primeIntegral δ -
        (2*δ/(1-2*δ))*omega3XIntegralEnvelope HighSix.s HighSix.S*HighSix.primeIntegral δ - ε
      (C*truncatedSixthMassScale N ≤
        ((MathlibNt.Wu2008DoubleSieve.wuPrimeComplements N).card : ℝ)) ∧
      (C*truncatedSixthMassScale N ≤
        ((Finset.filter (fun p => Nat.Prime p ∧ 0 < N-p ∧
          ArithmeticFunction.cardFactors (N-p) ≤ 2) (Finset.range (N+1))).card : ℝ)) := by
  obtain ⟨T,hT,h⟩ := actual_count_quarter hδ hδhi hε
  refine ⟨T,hT,?_⟩
  intro N hN he
  have hn := h N hN he
  have heq := HighSix.psi_source_penalty hδhi
  have hcoef : (TruncatedElevenHPackedCount.otherCoefficient -
      Gdelta δ (1/3) - Gdelta δ truncatedSixthLowerSigma + gainH34 δ)/4 +
      firstFunctionalGainPsiOne HighSix.s HighSix.S*HighSix.primeIntegral δ -
      (2*δ/(1-2*δ))*omega3XIntegralEnvelope HighSix.s HighSix.S*HighSix.primeIntegral δ - ε =
      (TruncatedElevenHPackedCount.otherCoefficient -
      Gdelta δ (1/3) - Gdelta δ truncatedSixthLowerSigma + gainH34 δ)/4 +
      firstFunctionalGainPsi δ HighSix.s HighSix.S*HighSix.primeIntegral δ - ε := by
    rw [heq]
    ring
  dsimp only
  rw [hcoef]
  exact ⟨hn,hn⟩

end Wu2008DoubleSieve.HighSixLowHMother
