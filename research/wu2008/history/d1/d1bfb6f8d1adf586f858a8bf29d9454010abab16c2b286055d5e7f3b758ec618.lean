import E08DebitJoint
import E08DebitSmall

noncomputable section
open Real Wu2008DoubleSieve
open SharpLogRecurrence JointLogTotalComparison

namespace WuTarget.E08Debit

def tightenedCap : ℝ := jointCap - 4 * smallGain

def oldSlack : ℝ := (W12.debitCeiling-W12.paymentEndpoint)/4

def netGain : ℝ := (W12.paymentEndpoint-tightenedCap)/4

def jointNet : ℝ :=
  (W12.paymentEndpoint + 4*U8ActualThreshold.gainLower-jointCap)/4

def smallNet : ℝ := smallGain-U8ActualThreshold.gainLower

def certifiedSlack : ℝ := (W12.debitCeiling-tightenedCap)/4

theorem analyticUpper_le_tightenedCap : W12.analyticUpper ≤ tightenedCap := by
  have hj := mixture_le_jointCap
  have hs := small_gain_lower
  unfold W12.analyticUpper tightenedCap
  linarith only [hj, hs]

theorem weightedDebit_le_tightenedCap :
    2 * Wu08TerminalAlignment.seventhMain +
      Wu08TerminalAlignment.eighthMain + Wu08TerminalAlignment.ninthMain ≤
        tightenedCap :=
  W12.weightedDebit_le_analyticUpper.trans analyticUpper_le_tightenedCap

theorem jointCap_exact : jointCap =
    (70541343621271076069121390945619987989042992845114226868299270918270612811647178113643290506051345656602365832173679695883466647781601154310457643306713171531030379526895425036071627018376627809026736251297926088225654002939893589333433624507353882308362164293449881489781282392955417207 /
      5956655340137885180969797046441844804527096110968141485983688943834388968979878936051328946251932240495782217126852030263617033606201611928650283875727212264685651380508218799617680264892161027101803410971559931534927217924265850387947914034191278940525507404781961958979355154450900000 : ℝ) := by
  unfold jointCap jointPacket
  rw [jointConstant_exact]
  norm_num [commonCoefficient, SignedTotalCorrelation.jTwo, SharpJBalance.ninthA,
    SharpJBalance.s, SeventhEighth.sigma, SeventhEighth.alpha,
    splitLower, splitUpper, V, upperLog, lowerLog]

theorem tightenedCap_exact : tightenedCap =
    (225561428121477004013451731600625610378082304494437777504599272140500289938446579466507964337198259137252610522064200365243359525844092194659838437794250150948845992692260681551889655786920015850891406410667395346253420401991040145806262985729391336539438999542458727224058584999494948776420180962927701 /
      19077835586759369396290568571994637949357133323917909555620061953079974090642092942958832276760438729903823120553738472484897874982936046481868144757037379842277052453744776344410590341002253620820257772314461722642910848096149191808283585104139297976518219034147059709870650470016066098038516848700000 : ℝ) := by
  unfold tightenedCap
  rw [jointCap_exact, smallGain_exact]
  norm_num

theorem tightenedCap_lt : tightenedCap < (1182322/100000 : ℝ) := by
  rw [tightenedCap_exact]
  norm_num

theorem netGain_gt : (217/500000 : ℝ) < netGain := by
  unfold netGain
  rw [W12.paymentEndpoint_exact, tightenedCap_exact]
  norm_num

theorem jointNet_gt : (1/5000 : ℝ) < jointNet := by
  unfold jointNet
  rw [W12.paymentEndpoint_exact, U8ActualThreshold.gainLower_exact, jointCap_exact]
  norm_num

theorem smallNet_gt : (1/5000 : ℝ) < smallNet := by
  unfold smallNet
  linarith only [smallGain_improves]

theorem netGain_identity : netGain = jointNet+smallNet := by
  unfold netGain jointNet smallNet tightenedCap
  ring

theorem cap_accounting :
    W12.paymentEndpoint-tightenedCap = 4*jointNet+4*smallNet := by
  unfold jointNet smallNet tightenedCap
  ring

theorem certifiedSlack_identity : certifiedSlack = oldSlack+netGain := by
  unfold certifiedSlack oldSlack netGain
  ring

theorem debitSlack_identity :
    W12Accepted.debitSlack =
      oldSlack+netGain+(tightenedCap-W12.analyticUpper)/4 := by
  unfold W12Accepted.debitSlack oldSlack netGain
  ring

theorem certifiedSlack_le_debitSlack : certifiedSlack ≤ W12Accepted.debitSlack := by
  unfold certifiedSlack W12Accepted.debitSlack
  linarith only [analyticUpper_le_tightenedCap]

theorem debitSlack_gt : (217/500000 : ℝ) < W12Accepted.debitSlack := by
  have h := analyticUpper_le_tightenedCap.trans_lt tightenedCap_lt
  unfold W12Accepted.debitSlack W12.debitCeiling
  linarith only [h]

theorem debitSlack_net_improvement :
    oldSlack+(217/500000 : ℝ) < W12Accepted.debitSlack := by
  rw [debitSlack_identity]
  have h := analyticUpper_le_tightenedCap
  linarith only [h, netGain_gt]

theorem tightenedCap_improves_rationalUpper :
    tightenedCap + 4*(433/1000000 : ℝ) < W12.rationalUpper := by
  have hn := netGain_gt
  have hg := JJointPayment.gain_bounds.2
  unfold netGain W12.paymentEndpoint at hn
  unfold W12.rationalUpper W12.rationalJUpper
  linarith only [hn, hg]

theorem analyticUpper_lt :
    W12.analyticUpper < (1182322/100000 : ℝ) :=
  analyticUpper_le_tightenedCap.trans_lt tightenedCap_lt

theorem weightedDebit_lt :
    2 * Wu08TerminalAlignment.seventhMain +
      Wu08TerminalAlignment.eighthMain + Wu08TerminalAlignment.ninthMain <
        (1182322/100000 : ℝ) :=
  weightedDebit_le_tightenedCap.trans_lt tightenedCap_lt

end WuTarget.E08Debit
