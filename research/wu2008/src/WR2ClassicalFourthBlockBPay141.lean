import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay141
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_141 (j : Fin 64) (hj : 64*141+j.val < 10540) :
    BPay (64*141+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_9024
  · exact WuPaper.ClassicalFourthNat.BPay_9025
  · exact WuPaper.ClassicalFourthNat.BPay_9026
  · exact WuPaper.ClassicalFourthNat.BPay_9027
  · exact WuPaper.ClassicalFourthNat.BPay_9028
  · exact WuPaper.ClassicalFourthNat.BPay_9029
  · exact WuPaper.ClassicalFourthNat.BPay_9030
  · exact WuPaper.ClassicalFourthNat.BPay_9031
  · exact WuPaper.ClassicalFourthNat.BPay_9032
  · exact WuPaper.ClassicalFourthNat.BPay_9033
  · exact WuPaper.ClassicalFourthNat.BPay_9034
  · exact WuPaper.ClassicalFourthNat.BPay_9035
  · exact WuPaper.ClassicalFourthNat.BPay_9036
  · exact WuPaper.ClassicalFourthNat.BPay_9037
  · exact WuPaper.ClassicalFourthNat.BPay_9038
  · exact WuPaper.ClassicalFourthNat.BPay_9039
  · exact WuPaper.ClassicalFourthNat.BPay_9040
  · exact WuPaper.ClassicalFourthNat.BPay_9041
  · exact WuPaper.ClassicalFourthNat.BPay_9042
  · exact WuPaper.ClassicalFourthNat.BPay_9043
  · exact WuPaper.ClassicalFourthNat.BPay_9044
  · exact WuPaper.ClassicalFourthNat.BPay_9045
  · exact WuPaper.ClassicalFourthNat.BPay_9046
  · exact WuPaper.ClassicalFourthNat.BPay_9047
  · exact WuPaper.ClassicalFourthNat.BPay_9048
  · exact WuPaper.ClassicalFourthNat.BPay_9049
  · exact WuPaper.ClassicalFourthNat.BPay_9050
  · exact WuPaper.ClassicalFourthNat.BPay_9051
  · exact WuPaper.ClassicalFourthNat.BPay_9052
  · exact WuPaper.ClassicalFourthNat.BPay_9053
  · exact WuPaper.ClassicalFourthNat.BPay_9054
  · exact WuPaper.ClassicalFourthNat.BPay_9055
  · exact WuPaper.ClassicalFourthNat.BPay_9056
  · exact WuPaper.ClassicalFourthNat.BPay_9057
  · exact WuPaper.ClassicalFourthNat.BPay_9058
  · exact WuPaper.ClassicalFourthNat.BPay_9059
  · exact WuPaper.ClassicalFourthNat.BPay_9060
  · exact WuPaper.ClassicalFourthNat.BPay_9061
  · exact WuPaper.ClassicalFourthNat.BPay_9062
  · exact WuPaper.ClassicalFourthNat.BPay_9063
  · exact WuPaper.ClassicalFourthNat.BPay_9064
  · exact WuPaper.ClassicalFourthNat.BPay_9065
  · exact WuPaper.ClassicalFourthNat.BPay_9066
  · exact WuPaper.ClassicalFourthNat.BPay_9067
  · exact WuPaper.ClassicalFourthNat.BPay_9068
  · exact WuPaper.ClassicalFourthNat.BPay_9069
  · exact WuPaper.ClassicalFourthNat.BPay_9070
  · exact WuPaper.ClassicalFourthNat.BPay_9071
  · exact WuPaper.ClassicalFourthNat.BPay_9072
  · exact WuPaper.ClassicalFourthNat.BPay_9073
  · exact WuPaper.ClassicalFourthNat.BPay_9074
  · exact WuPaper.ClassicalFourthNat.BPay_9075
  · exact WuPaper.ClassicalFourthNat.BPay_9076
  · exact WuPaper.ClassicalFourthNat.BPay_9077
  · exact WuPaper.ClassicalFourthNat.BPay_9078
  · exact WuPaper.ClassicalFourthNat.BPay_9079
  · exact WuPaper.ClassicalFourthNat.BPay_9080
  · exact WuPaper.ClassicalFourthNat.BPay_9081
  · exact WuPaper.ClassicalFourthNat.BPay_9082
  · exact WuPaper.ClassicalFourthNat.BPay_9083
  · exact WuPaper.ClassicalFourthNat.BPay_9084
  · exact WuPaper.ClassicalFourthNat.BPay_9085
  · exact WuPaper.ClassicalFourthNat.BPay_9086
  · exact WuPaper.ClassicalFourthNat.BPay_9087
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_141
