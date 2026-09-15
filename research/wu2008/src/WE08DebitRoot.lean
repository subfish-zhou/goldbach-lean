import WE08DebitBudget

noncomputable section
open Real Wu2008DoubleSieve
open scoped Interval

namespace WuTarget.E08Debit

theorem original_domains_cap :
    16 * (∫ t in SeventhEighth.sigma..(1/3),
        log ((1-2*t)/t)/(t*(1-t))) +
      8 * (∫ t in SeventhEighth.alpha..(1/3),
        log (2-3*t)/(t*(1-t))) +
      8 * (∫ t in SharpJBalance.b..SharpJBalance.s,
        log ((1-SharpJBalance.s-t)/SharpJBalance.s)/(t*(1-t))) -
      8 * ((∫ t in (100/1327 : ℝ)..(1/10), log (2-3*t)/(t*(1-t))) -
        (9/10 : ℝ) * ∫ t in (100/1327 : ℝ)..(1/10),
          log (2-3*t)/(t*(1-t)^2)) ≤ tightenedCap := by
  rw [← W12.weightedDebit_original_domains]
  exact weightedDebit_le_tightenedCap

theorem debitSlack_full_identity :
    W12Accepted.debitSlack =
      oldSlack+jointNet+smallNet+
        (jointCap-jointPacket log log)/4+
        (2*(U8CanonicalMother.L-U8CanonicalMother.I)-smallGain) := by
  rw [debitSlack_identity, netGain_identity]
  unfold tightenedCap W12.analyticUpper
  rw [joint_collection]
  ring

theorem unpaid_residuals_nonnegative :
    0 ≤ (jointCap-jointPacket log log)/4 ∧
      0 ≤ 2*(U8CanonicalMother.L-U8CanonicalMother.I)-smallGain := by
  have hj := joint_payment
  have hs := small_gain_lower
  change 0 ≤ (jointCap-jointPacket log log)/4 ∧ _
  change jointPacket log log ≤ jointCap at hj
  constructor <;> linarith only [hj, hs]

theorem ledger_improvement (rest : ℝ) :
    rest+oldSlack+(217/500000 : ℝ) < rest+W12Accepted.debitSlack := by
  linarith only [debitSlack_net_improvement]

def certifiedCoefficient (x : Fin 9 → ℝ) : ℝ :=
  W12Accepted.paidCoefficient x-W12Accepted.debitSlack+certifiedSlack

theorem coefficient_net_identity (x : Fin 9 → ℝ) :
    certifiedCoefficient x =
      (W12Accepted.paidCoefficient x-W12Accepted.debitSlack+oldSlack)+netGain := by
  unfold certifiedCoefficient
  rw [certifiedSlack_identity]
  ring

theorem coefficient_le_paid (x : Fin 9 → ℝ) :
    certifiedCoefficient x ≤ W12Accepted.paidCoefficient x := by
  unfold certifiedCoefficient
  linarith only [certifiedSlack_le_debitSlack]

theorem certified_ordinary_P2 {ε dmax : ℝ} (hε : 0 < ε) (hdmax : 0 < dmax) :
    ∃ δ : ℝ, 0 < δ ∧ δ < dmax ∧ δ ≤ 1/100 ∧
      ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
        (certifiedCoefficient W04Accepted.enhanced-ε)*U8CanonicalMother.M N ≤
          ((Finset.filter (fun p => Nat.Prime p ∧ 0 < N-p ∧
            ArithmeticFunction.cardFactors (N-p) ≤ 2) (Finset.range (N+1))).card : ℝ) := by
  obtain ⟨δ,hδ,hd,hδhi,T,hT,h⟩ := W12Accepted.enhanced_P2_paid hε hdmax
  refine ⟨δ,hδ,hd,hδhi,T,hT,?_⟩
  intro N hN he
  have hs : 0 ≤ U8CanonicalMother.M N :=
    (HighSixPhase6.original_scale_positive (hT.trans hN)).le
  exact (mul_le_mul_of_nonneg_right
    (sub_le_sub_right (coefficient_le_paid W04Accepted.enhanced) ε) hs).trans (h N hN he)

#check @joint_collection
#check @mixture_le_jointCap
#check @small_gain_lower
#check @smallGain_exact
#check @jointCap_exact
#check @tightenedCap_exact
#check @analyticUpper_le_tightenedCap
#check @analyticUpper_lt
#check @weightedDebit_le_tightenedCap
#check @weightedDebit_lt
#check @original_domains_cap
#check @tightenedCap_improves_rationalUpper
#check @jointNet_gt
#check @smallNet_gt
#check @netGain_gt
#check @cap_accounting
#check @certifiedSlack_identity
#check @debitSlack_identity
#check @debitSlack_full_identity
#check @unpaid_residuals_nonnegative
#check @debitSlack_gt
#check @debitSlack_net_improvement
#check @ledger_improvement
#check @coefficient_net_identity
#check @certified_ordinary_P2
#print tightenedCap
#print oldSlack
#print netGain
#print jointNet
#print smallNet
#print certifiedSlack
#print certifiedCoefficient
#print axioms joint_collection
#print axioms mixture_le_jointCap
#print axioms small_gain_lower
#print axioms smallGain_exact
#print axioms jointCap_exact
#print axioms tightenedCap_exact
#print axioms analyticUpper_le_tightenedCap
#print axioms analyticUpper_lt
#print axioms weightedDebit_le_tightenedCap
#print axioms weightedDebit_lt
#print axioms original_domains_cap
#print axioms tightenedCap_improves_rationalUpper
#print axioms jointNet_gt
#print axioms smallNet_gt
#print axioms netGain_gt
#print axioms cap_accounting
#print axioms certifiedSlack_identity
#print axioms debitSlack_identity
#print axioms debitSlack_full_identity
#print axioms unpaid_residuals_nonnegative
#print axioms debitSlack_gt
#print axioms debitSlack_net_improvement
#print axioms ledger_improvement
#print axioms coefficient_net_identity
#print axioms certified_ordinary_P2

end WuTarget.E08Debit
