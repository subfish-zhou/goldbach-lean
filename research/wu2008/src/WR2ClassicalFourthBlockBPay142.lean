import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay142
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_142 (j : Fin 64) (hj : 64*142+j.val < 10540) :
    BPay (64*142+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_9088
  · exact WuPaper.ClassicalFourthNat.BPay_9089
  · exact WuPaper.ClassicalFourthNat.BPay_9090
  · exact WuPaper.ClassicalFourthNat.BPay_9091
  · exact WuPaper.ClassicalFourthNat.BPay_9092
  · exact WuPaper.ClassicalFourthNat.BPay_9093
  · exact WuPaper.ClassicalFourthNat.BPay_9094
  · exact WuPaper.ClassicalFourthNat.BPay_9095
  · exact WuPaper.ClassicalFourthNat.BPay_9096
  · exact WuPaper.ClassicalFourthNat.BPay_9097
  · exact WuPaper.ClassicalFourthNat.BPay_9098
  · exact WuPaper.ClassicalFourthNat.BPay_9099
  · exact WuPaper.ClassicalFourthNat.BPay_9100
  · exact WuPaper.ClassicalFourthNat.BPay_9101
  · exact WuPaper.ClassicalFourthNat.BPay_9102
  · exact WuPaper.ClassicalFourthNat.BPay_9103
  · exact WuPaper.ClassicalFourthNat.BPay_9104
  · exact WuPaper.ClassicalFourthNat.BPay_9105
  · exact WuPaper.ClassicalFourthNat.BPay_9106
  · exact WuPaper.ClassicalFourthNat.BPay_9107
  · exact WuPaper.ClassicalFourthNat.BPay_9108
  · exact WuPaper.ClassicalFourthNat.BPay_9109
  · exact WuPaper.ClassicalFourthNat.BPay_9110
  · exact WuPaper.ClassicalFourthNat.BPay_9111
  · exact WuPaper.ClassicalFourthNat.BPay_9112
  · exact WuPaper.ClassicalFourthNat.BPay_9113
  · exact WuPaper.ClassicalFourthNat.BPay_9114
  · exact WuPaper.ClassicalFourthNat.BPay_9115
  · exact WuPaper.ClassicalFourthNat.BPay_9116
  · exact WuPaper.ClassicalFourthNat.BPay_9117
  · exact WuPaper.ClassicalFourthNat.BPay_9118
  · exact WuPaper.ClassicalFourthNat.BPay_9119
  · exact WuPaper.ClassicalFourthNat.BPay_9120
  · exact WuPaper.ClassicalFourthNat.BPay_9121
  · exact WuPaper.ClassicalFourthNat.BPay_9122
  · exact WuPaper.ClassicalFourthNat.BPay_9123
  · exact WuPaper.ClassicalFourthNat.BPay_9124
  · exact WuPaper.ClassicalFourthNat.BPay_9125
  · exact WuPaper.ClassicalFourthNat.BPay_9126
  · exact WuPaper.ClassicalFourthNat.BPay_9127
  · exact WuPaper.ClassicalFourthNat.BPay_9128
  · exact WuPaper.ClassicalFourthNat.BPay_9129
  · exact WuPaper.ClassicalFourthNat.BPay_9130
  · exact WuPaper.ClassicalFourthNat.BPay_9131
  · exact WuPaper.ClassicalFourthNat.BPay_9132
  · exact WuPaper.ClassicalFourthNat.BPay_9133
  · exact WuPaper.ClassicalFourthNat.BPay_9134
  · exact WuPaper.ClassicalFourthNat.BPay_9135
  · exact WuPaper.ClassicalFourthNat.BPay_9136
  · exact WuPaper.ClassicalFourthNat.BPay_9137
  · exact WuPaper.ClassicalFourthNat.BPay_9138
  · exact WuPaper.ClassicalFourthNat.BPay_9139
  · exact WuPaper.ClassicalFourthNat.BPay_9140
  · exact WuPaper.ClassicalFourthNat.BPay_9141
  · exact WuPaper.ClassicalFourthNat.BPay_9142
  · exact WuPaper.ClassicalFourthNat.BPay_9143
  · exact WuPaper.ClassicalFourthNat.BPay_9144
  · exact WuPaper.ClassicalFourthNat.BPay_9145
  · exact WuPaper.ClassicalFourthNat.BPay_9146
  · exact WuPaper.ClassicalFourthNat.BPay_9147
  · exact WuPaper.ClassicalFourthNat.BPay_9148
  · exact WuPaper.ClassicalFourthNat.BPay_9149
  · exact WuPaper.ClassicalFourthNat.BPay_9150
  · exact WuPaper.ClassicalFourthNat.BPay_9151
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_142
