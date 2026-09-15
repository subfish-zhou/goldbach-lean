import WE09JointMainMajorPayment

noncomputable section
namespace WuTarget.E09JointMainMajor
open Wu2008DoubleSieve Wu08TerminalAlignment Wu08OriginalFourWeights

theorem new_w11_le_actual_core :
    W11CreditAccepted.paidCoefficient + E09JointMain.netGain + netGain ≤
      W14Accepted.paidCoefficient W04Accepted.enhanced := by
  have hp := payment_le_actual
  have hd := W12.weightedDebit_le_analyticUpper
  have hg := W02Accepted.nodeGain_le_full
  rw [W11CreditAccepted.paid_exact]
  unfold W12.weightedDebit at hd
  unfold W14Accepted.paidCoefficient W14Accepted.remainingCoefficient W14Accepted.signedCore
    W12Accepted.debitSlack W12.debitCeiling netGain E09JointMain.netGain E09JointMain.payment
  linarith only [hp, hd, hg]

def paidCoefficient : ℝ := E09JointMain.paidCoefficient + netGain

theorem paid_net :
    paidCoefficient - E09JointMain.paidCoefficient = netGain := by
  unfold paidCoefficient
  ring

theorem paid_strict : E09JointMain.paidCoefficient < paidCoefficient := by
  unfold paidCoefficient
  linarith only [netGain_pos]

theorem paid_exact :
    paidCoefficient =
      (payment + sixthMain - W13Tight.pairUpper + W02Accepted.nodeGain) / 4 +
        W14Accepted.retainedSlack + W12Accepted.debitSlack +
        535927 / 200000 + 2493 / 4000000 - 2956239 / 1000000 +
        W17Accepted.jointCredit := by
  unfold paidCoefficient
  rw [E09JointMain.paid_exact]
  unfold netGain
  ring

theorem paid_lt_actual :
    paidCoefficient < W01.ordinaryCoefficient W17Accepted.enhanced := by
  have hn := new_w11_le_actual_core
  have h4 := W14Accepted.paid_lt_actual W04Accepted.enhanced
  have h13 := W13TightAccepted.paid_le_previous
  unfold paidCoefficient E09JointMain.paidCoefficient W17Accepted.paidCoefficient
    W17Accepted.jointCredit
  linarith only [hn, h4, h13]

theorem ordinary_P2_paid {ε dmax : ℝ} (hε : 0 < ε) (hdmax : 0 < dmax) :
    ∃ δ : ℝ, 0 < δ ∧ δ < dmax ∧ δ ≤ 1 / 100 ∧
      ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
        (paidCoefficient - ε) * U8CanonicalMother.M N ≤
          ((Finset.filter (fun p => Nat.Prime p ∧ 0 < N - p ∧
            ArithmeticFunction.cardFactors (N - p) ≤ 2) (Finset.range (N + 1))).card : ℝ) := by
  obtain ⟨δ, hd, hm, hs, _, _, T, hT, hc⟩ :=
    W17Accepted.enhanced_ordinary_P2 hε hdmax
  refine ⟨δ, hd, hm, hs, T, hT, ?_⟩
  intro N hN he
  have hM : 0 ≤ U8CanonicalMother.M N :=
    (HighSixPhase6.original_scale_positive (hT.trans hN)).le
  exact (mul_le_mul_of_nonneg_right (sub_le_sub_right paid_lt_actual.le ε) hM).trans
    (hc N hN he)

theorem ordinary_P2 :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 100 ∧
      ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
        paidCoefficient * U8CanonicalMother.M N <
          ((Finset.filter (fun p => Nat.Prime p ∧ 0 < N - p ∧
            ArithmeticFunction.cardFactors (N - p) ≤ 2) (Finset.range (N + 1))).card : ℝ) := by
  let ε := (W01.ordinaryCoefficient W17Accepted.enhanced - paidCoefficient) / 2
  have hε : 0 < ε := half_pos (sub_pos.mpr paid_lt_actual)
  obtain ⟨δ, hd, _, hs, _, _, T, hT, hc⟩ :=
    W17Accepted.enhanced_ordinary_P2 hε (by norm_num : (0 : ℝ) < 1)
  refine ⟨δ, hd, hs, T, hT, ?_⟩
  intro N hN he
  have hM := HighSixPhase6.original_scale_positive (hT.trans hN)
  have hcoef : paidCoefficient < W01.ordinaryCoefficient W17Accepted.enhanced - ε := by
    dsimp [ε]
    linarith only [paid_lt_actual]
  exact (mul_lt_mul_of_pos_right hcoef hM).trans_le (hc N hN he)

end WuTarget.E09JointMainMajor
