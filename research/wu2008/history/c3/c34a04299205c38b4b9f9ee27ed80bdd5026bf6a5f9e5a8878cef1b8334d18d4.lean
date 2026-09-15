import W12WeightedDebit

noncomputable section
open Wu2008DoubleSieve

namespace WuTarget.W12

def paymentEndpoint : ℝ :=
  UnroundedPayments.weightedJUpper -
    SignedTotalCorrelation.jTwo * (SharpLogRecurrence.upperLog 2 -
      (JointLogTotalComparison.V (4/3) + JointLogTotalComparison.V (3/2))) -
    JointJLossStrength.fixedRecovery -
    4 * (2639/1000000) - 4 * U8ActualThreshold.gainLower

theorem rationalUpper_lt_paymentEndpoint : rationalUpper < paymentEndpoint := by
  have hg := JJointPayment.gain_bounds.1
  unfold rationalUpper rationalJUpper paymentEndpoint
  linarith only [hg]

theorem paymentEndpoint_exact : paymentEndpoint =
    (86206188551737982192947084628927108867054131274783231387631573486194410386523346017995658020008875411242056978453 /
      7290191673927056469150900117984060996314540999119243133694141128123071337756211785149931744997097068391183875000 : ℝ) := by
  unfold paymentEndpoint
  rw [U8ActualThreshold.gainLower_exact]
  norm_num [UnroundedPayments.weightedJUpper, UnroundedPayments.j7Upper,
    UnroundedPayments.j8Upper, UnroundedPayments.j9Upper,
    SignedTotalCorrelation.jTwo, JointJLossStrength.fixedRecovery,
    JointJLossStrength.massPayment, SharpJBalance.ninthA, SharpJBalance.s,
    SharpJBalance.b, SeventhEighth.sigma, SeventhEighth.alpha, ninthProfileK2,
    SharpLogRecurrence.upperLog, SharpLogRecurrence.lowerLog,
    JointLogTotalComparison.V]

def debitCeiling : ℝ := 11824956/1000000

theorem paymentEndpoint_lt_debitCeiling : paymentEndpoint < debitCeiling := by
  rw [paymentEndpoint_exact]
  norm_num [debitCeiling]

theorem rationalUpper_lt_debitCeiling : rationalUpper < debitCeiling :=
  rationalUpper_lt_paymentEndpoint.trans paymentEndpoint_lt_debitCeiling

theorem weightedDebit_lt_debitCeiling :
    2 * Wu08TerminalAlignment.seventhMain +
      Wu08TerminalAlignment.eighthMain + Wu08TerminalAlignment.ninthMain <
        11824956/1000000 :=
  weightedDebit_le_rationalUpper.trans_lt rationalUpper_lt_debitCeiling

theorem quarterDebit_lt :
    (2 * Wu08TerminalAlignment.seventhMain +
      Wu08TerminalAlignment.eighthMain + Wu08TerminalAlignment.ninthMain)/4 <
        2956239/1000000 := by
  linarith only [weightedDebit_lt_debitCeiling]

end WuTarget.W12
