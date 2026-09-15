import WE09JointMainPayment
import W17AcceptedBudget

noncomputable section
namespace WuTarget.E09JointMain
open Wu2008DoubleSieve Wu08TerminalAlignment Wu08OriginalFourWeights

theorem shifted_w11_le_actual_core :
    W11CreditAccepted.paidCoefficient + netGain ≤
      W14Accepted.paidCoefficient W04Accepted.enhanced := by
  have hp := payment_le_actual
  have hd := W12.weightedDebit_le_analyticUpper
  have hg := W02Accepted.nodeGain_le_full
  rw [W11CreditAccepted.paid_exact]
  unfold payment at hp
  unfold W12.weightedDebit at hd
  unfold W14Accepted.paidCoefficient W14Accepted.remainingCoefficient W14Accepted.signedCore
    W12Accepted.debitSlack W12.debitCeiling netGain
  linarith only [hp, hd, hg]

theorem shifted_w13_lt_actual :
    W13TightAccepted.paidCoefficient + netGain <
      W01.ordinaryCoefficient W04Accepted.enhanced := by
  have h := W14Accepted.paid_lt_actual W04Accepted.enhanced
  linarith only [W13TightAccepted.paid_le_previous, shifted_w11_le_actual_core, h]

def paidCoefficient : ℝ := W17Accepted.paidCoefficient + netGain

def remainingCoefficient : ℝ := W17Accepted.remainingCoefficient + netGain

theorem paid_net :
    paidCoefficient - W17Accepted.paidCoefficient = 5000 / 15848361 := by
  unfold paidCoefficient
  linarith only [netGain_exact]

theorem remaining_net :
    remainingCoefficient - W17Accepted.remainingCoefficient = 5000 / 15848361 := by
  unfold remainingCoefficient
  linarith only [netGain_exact]

theorem paid_strict : W17Accepted.paidCoefficient < paidCoefficient := by
  unfold paidCoefficient
  linarith only [netGain_pos]

theorem paid_lt_actual :
    paidCoefficient < W01.ordinaryCoefficient W17Accepted.enhanced := by
  have h := shifted_w13_lt_actual
  unfold paidCoefficient W17Accepted.paidCoefficient W17Accepted.jointCredit
  linarith only [h]

theorem paid_exact :
    paidCoefficient =
      (payment + sixthMain - W13Tight.pairUpper + W02Accepted.nodeGain) / 4 +
        W14Accepted.retainedSlack + W12Accepted.debitSlack +
        535927 / 200000 + 2493 / 4000000 - 2956239 / 1000000 +
        W17Accepted.jointCredit := by
  unfold paidCoefficient W17Accepted.paidCoefficient
  rw [W13TightAccepted.paid_exact, W11CreditAccepted.paid_exact]
  unfold payment netGain
  ring

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

theorem paid_threshold_iff : (4491 / 5000 : ℝ) ≤ paidCoefficient ↔
    (840977 / 800000 : ℝ) ≤ remainingCoefficient := by
  unfold paidCoefficient remainingCoefficient W17Accepted.paidCoefficient
    W17Accepted.remainingCoefficient W13TightAccepted.paidCoefficient
  constructor <;> intro h <;> linarith only [h]

theorem old_remaining_threshold_iff : (4491 / 5000 : ℝ) ≤ paidCoefficient ↔
    (13324107088697 / 12678688800000 : ℝ) ≤ W17Accepted.remainingCoefficient := by
  rw [paid_threshold_iff]
  unfold remainingCoefficient
  rw [netGain_exact]
  constructor <;> intro h <;> linarith only [h]

theorem refined_target
    (h : (13324107088697 / 12678688800000 : ℝ) ≤ W17Accepted.remainingCoefficient) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      RefinedExit.margin / 2 * U8CanonicalMother.M N ≤
        ((Wu2004MeanValue.refinedGood N (9469 / 5000)).card : ℝ) ∧
      ∃ p r q : ℕ, p.Prime ∧ (r = 1 ∨ r.Prime) ∧ q.Prime ∧
        N = p + r * q ∧ (r : ℝ) ≤ (q : ℝ) ^ (4469 / 5000 : ℝ) := by
  apply RefinedExit.from_actual_count (old_remaining_threshold_iff.mpr h)
  intro ε hε
  obtain ⟨_, _, _, _, T, hT, hc⟩ := ordinary_P2_paid hε (by norm_num : (0 : ℝ) < 1)
  exact ⟨T, hT, hc⟩

end WuTarget.E09JointMain
