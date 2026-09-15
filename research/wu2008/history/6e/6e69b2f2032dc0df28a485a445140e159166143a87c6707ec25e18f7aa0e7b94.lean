import WE01BaselineScalars

noncomputable section
namespace WuTarget.E01Baseline
open Wu2008DoubleSieve

theorem sixth_lower : sixthLower ≤ Wu08TerminalAlignment.sixthMain := by
  rw [← sixth_exact]
  exact Phase25.actual_sixth_ge_new

theorem node_lower : gammaLower ≤ W02Accepted.nodeGain := by
  rw [← gamma_exact]
  have hw (j : Fin 21) : 0 ≤ (W02.lowerVector j : ℝ) := by
    exact_mod_cast (W02.lowerVector_pos j).le
  exact (W03.paid_weights_consumer hw).trans W02Accepted.tableGain_le_nodeGain

theorem debit_strict : debitLower < W12Accepted.debitSlack := by
  have h := W12.analyticUpper_le_rationalUpper.trans_lt W12.rationalUpper_lt_paymentEndpoint
  rw [← debit_exact]
  unfold W12Accepted.debitSlack
  linarith only [h]

theorem remaining_strict : exactRemaining < W17Accepted.remainingCoefficient := by
  have hs := sixth_lower
  have hn := node_lower
  have hd := debit_strict
  have hr := W14Accepted.retainedSlack_nonneg
  have hj := W17Accepted.jointCredit_nonneg
  rw [← total_exact]
  unfold W17Accepted.remainingCoefficient W13TightAccepted.remainingCoefficient
  rw [payment_exact, four_exact]
  linarith only [hs, hn, hd, hr, hj]

theorem paid_net_identity :
    W17Accepted.paidCoefficient = W17Accepted.remainingCoefficient-122417/800000 := by
  unfold W17Accepted.paidCoefficient W17Accepted.remainingCoefficient
    W13TightAccepted.paidCoefficient
  ring

theorem paid_strict : exactPaid < W17Accepted.paidCoefficient := by
  rw [paid_net_identity]
  exact sub_lt_sub_right remaining_strict _

theorem actual_strict : exactPaid < W01.ordinaryCoefficient W17Accepted.enhanced :=
  paid_strict.trans W17Accepted.paid_lt_actual

theorem literal_baseline :
    (14826/15625 : ℝ) < W17Accepted.remainingCoefficient ∧
      (3183371/4000000 : ℝ) < W17Accepted.paidCoefficient ∧
      (3183371/4000000 : ℝ) < W01.ordinaryCoefficient W17Accepted.enhanced :=
  ⟨remaining_rational_bounds.1.trans remaining_strict,
    paid_rational_bounds.1.trans paid_strict,
    paid_rational_bounds.1.trans actual_strict⟩

theorem remaining_surplus_identity :
    W17Accepted.remainingCoefficient-exactRemaining =
      (Wu08TerminalAlignment.sixthMain-sixthLower)/4 +
      (W02Accepted.nodeGain-gammaLower)/4 +
      W14Accepted.retainedSlack +
      (W12.paymentEndpoint-W12.analyticUpper)/4 + W17Accepted.jointCredit := by
  rw [← total_exact]
  unfold W17Accepted.remainingCoefficient W13TightAccepted.remainingCoefficient
  rw [payment_exact, four_exact, ← debit_exact]
  unfold W12Accepted.debitSlack
  ring

theorem surplus_strict :
    0 < W17Accepted.remainingCoefficient-exactRemaining ∧
      W17Accepted.paidCoefficient-exactPaid =
        W17Accepted.remainingCoefficient-exactRemaining := by
  refine ⟨sub_pos.mpr remaining_strict, ?_⟩
  rw [paid_net_identity]
  unfold exactPaid
  ring

theorem actual_gap_identity :
    (840977/800000 : ℝ)-W17Accepted.remainingCoefficient =
      ((840977/800000 : ℝ)-exactRemaining) -
        (W17Accepted.remainingCoefficient-exactRemaining) ∧
      (4491/5000 : ℝ)-W17Accepted.paidCoefficient =
        (840977/800000 : ℝ)-W17Accepted.remainingCoefficient := by
  rw [paid_net_identity]
  constructor <;> ring

theorem certificate_gap_is_not_actual_gap :
    (840977/800000 : ℝ)-W17Accepted.remainingCoefficient <
      (840977/800000 : ℝ)-exactRemaining ∧
      (4491/5000 : ℝ)-W17Accepted.paidCoefficient <
        (4491/5000 : ℝ)-exactPaid :=
  ⟨sub_lt_sub_left remaining_strict _, sub_lt_sub_left paid_strict _⟩

theorem ordinary_P2_exact :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      exactPaid*U8CanonicalMother.M N ≤
        ((Finset.filter (fun p => Nat.Prime p ∧ 0 < N-p ∧
          ArithmeticFunction.cardFactors (N-p) ≤ 2) (Finset.range (N+1))).card : ℝ) := by
  obtain ⟨_, _, _, _, T, hT, hc⟩ :=
    W17Accepted.ordinary_P2_paid (sub_pos.mpr paid_strict)
      (by norm_num : (0 : ℝ) < 1)
  refine ⟨T, hT, ?_⟩
  intro N hN he
  have hpay : W17Accepted.paidCoefficient -
      (W17Accepted.paidCoefficient-exactPaid) = exactPaid := by ring
  simpa only [hpay] using hc N hN he

theorem ordinary_P2_baseline :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (3183371/4000000 : ℝ)*U8CanonicalMother.M N ≤
        ((Finset.filter (fun p => Nat.Prime p ∧ 0 < N-p ∧
          ArithmeticFunction.cardFactors (N-p) ≤ 2) (Finset.range (N+1))).card : ℝ) := by
  obtain ⟨T, hT, hc⟩ := ordinary_P2_exact
  refine ⟨T, hT, ?_⟩
  intro N hN he
  have hM : 0 ≤ U8CanonicalMother.M N :=
    (HighSixPhase6.original_scale_positive (hT.trans hN)).le
  exact (mul_le_mul_of_nonneg_right paid_rational_bounds.1.le hM).trans (hc N hN he)

end WuTarget.E01Baseline
