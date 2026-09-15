import W14PaymentV2

noncomputable section
open Real Wu2008DoubleSieve Wu08TerminalAlignment

namespace WuTarget.W14

theorem block_actual_count {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (block-ε)*wuSingularSeries N*N/log N^(2 : ℕ) ≤
        (sieveCount N 1 N ((N : ℝ)^truncatedSixthLowerBeta) : ℝ)+
          (fifthPairCount N : ℝ) := by
  obtain ⟨T2,hT2,h2⟩ := PositiveSecondPayment.second_actual_count (half_pos hε)
  obtain ⟨T5,_,h5⟩ := PositiveCoreResume.fifth_count (half_pos hε)
  refine ⟨max T2 T5, hT2.trans (le_max_left _ _), fun N hN he => ?_⟩
  have h2N := h2 N ((le_max_left _ _).trans hN) he
  have h5N := h5 N ((le_max_right _ _).trans hN) he
  change (secondMain+8*PositiveSecondPayment.secondGain-ε/2)*
    wuSingularSeries N*N/log N^(2 : ℕ) ≤
      (sieveCount N 1 N ((N : ℝ)^truncatedSixthLowerBeta) : ℝ) at h2N
  change (fifthMain+PositiveCoreResume.fifthGain-ε/2)*
    wuSingularSeries N*N/log N^(2 : ℕ) ≤ (fifthPairCount N : ℝ) at h5N
  unfold block
  ring_nf at h2N h5N ⊢
  linarith only [h2N, h5N]

theorem block_paid_count :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (535927/50000 : ℝ)*wuSingularSeries N*N/log N^(2 : ℕ) ≤
        (sieveCount N 1 N ((N : ℝ)^truncatedSixthLowerBeta) : ℝ)+
          (fifthPairCount N : ℝ) := by
  have hgap : 0 < block-535927/50000 := sub_pos.mpr block_gt
  have h := block_actual_count hgap
  have he : block-(block-535927/50000) = (535927/50000 : ℝ) := by ring
  simpa only [he] using h

def remainder : ℝ :=
  3*firstMain-thirdMain-fourthMain+sixthMain-
    2*seventhMain-eighthMain-ninthMain-
    Wu08OriginalFourWeights.original10-Wu08OriginalFourWeights.original11+
    FeedbackLimit.Cinf+4*Phase20.rawPsi+4*Phase18.g18

theorem original_decomposition : Wu08FourMother.Qoriginal = (remainder+block)/4 := by
  unfold Wu08FourMother.Qoriginal remainder block
  ring

theorem original_exact_lower : (remainder+exactLower)/4 ≤ Wu08FourMother.Qoriginal := by
  rw [original_decomposition]
  linarith only [block_lower]

def paidCoefficient : ℝ := (remainder+535927/50000)/4

theorem paid_coefficient_lt : paidCoefficient < Wu08FourMother.Qoriginal := by
  rw [original_decomposition]
  unfold paidCoefficient
  have h := block_gt
  change (535927/50000 : ℝ) < block at h
  linarith only [h]

theorem original_paid_count :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1/100 ∧
      ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
        paidCoefficient*U8CanonicalMother.M N ≤
          ((Finset.filter (fun p => Nat.Prime p ∧ 0 < N-p ∧
            ArithmeticFunction.cardFactors (N-p) ≤ 2) (Finset.range (N+1))).card : ℝ) := by
  have h := Wu08FourMother.ordinary_P2 (Wu08FourMother.Qoriginal-paidCoefficient)
    (sub_pos.mpr paid_coefficient_lt)
  have he : Wu08FourMother.Qoriginal-(Wu08FourMother.Qoriginal-paidCoefficient) =
      paidCoefficient := by ring
  simpa only [he] using h

end WuTarget.W14
