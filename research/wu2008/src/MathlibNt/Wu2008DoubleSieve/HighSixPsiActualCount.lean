import MathlibNt.Wu2008DoubleSieve.HighSixPsiMother

namespace Wu2008DoubleSieve.HighSixPsiMother
open Real SingleUpperClassicalLimit
open TruncatedElevenClassicalCountLower

/-- Fixed delta: only the actual U3 local j6 integral is improved. -/
noncomputable def psiCoefficient (δ : ℝ) : ℝ :=
  24*wuLowerCoefficient (1/(2*truncatedSixthLowerAlpha)) +
    8*wuLowerCoefficient (1/(2*truncatedSixthLowerBeta)) + fifthPairFlin +
    truncatedSixthLowerF6lin + 47/481250 -
    Gdelta δ (1/3) - Gdelta δ truncatedSixthLowerSigma +
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
        Gdelta δ (1/3) - Gdelta δ truncatedSixthLowerSigma +
        4*firstFunctionalGainPsiOne HighSix.s HighSix.S*HighSix.primeIntegral δ -
        4*(2*δ/(1-2*δ))*omega3XIntegralEnvelope HighSix.s HighSix.S*HighSix.primeIntegral δ -
        8*J9 - 16*SeventhEighth.J7 - 8*SeventhEighth.J8 -
        8*FourRoughClosedMass.I10 - 8*FourRoughClosedMass.I11 := by
  unfold psiCoefficient
  rw [HighSix.psi_source_penalty hδhi]
  ring

end Wu2008DoubleSieve.HighSixPsiMother
