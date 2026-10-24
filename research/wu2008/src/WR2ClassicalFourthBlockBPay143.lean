import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay143
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_143 (j : Fin 64) (hj : 64*143+j.val < 10540) :
    BPay (64*143+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_9152
  · exact WuPaper.ClassicalFourthNat.BPay_9153
  · exact WuPaper.ClassicalFourthNat.BPay_9154
  · exact WuPaper.ClassicalFourthNat.BPay_9155
  · exact WuPaper.ClassicalFourthNat.BPay_9156
  · exact WuPaper.ClassicalFourthNat.BPay_9157
  · exact WuPaper.ClassicalFourthNat.BPay_9158
  · exact WuPaper.ClassicalFourthNat.BPay_9159
  · exact WuPaper.ClassicalFourthNat.BPay_9160
  · exact WuPaper.ClassicalFourthNat.BPay_9161
  · exact WuPaper.ClassicalFourthNat.BPay_9162
  · exact WuPaper.ClassicalFourthNat.BPay_9163
  · exact WuPaper.ClassicalFourthNat.BPay_9164
  · exact WuPaper.ClassicalFourthNat.BPay_9165
  · exact WuPaper.ClassicalFourthNat.BPay_9166
  · exact WuPaper.ClassicalFourthNat.BPay_9167
  · exact WuPaper.ClassicalFourthNat.BPay_9168
  · exact WuPaper.ClassicalFourthNat.BPay_9169
  · exact WuPaper.ClassicalFourthNat.BPay_9170
  · exact WuPaper.ClassicalFourthNat.BPay_9171
  · exact WuPaper.ClassicalFourthNat.BPay_9172
  · exact WuPaper.ClassicalFourthNat.BPay_9173
  · exact WuPaper.ClassicalFourthNat.BPay_9174
  · exact WuPaper.ClassicalFourthNat.BPay_9175
  · exact WuPaper.ClassicalFourthNat.BPay_9176
  · exact WuPaper.ClassicalFourthNat.BPay_9177
  · exact WuPaper.ClassicalFourthNat.BPay_9178
  · exact WuPaper.ClassicalFourthNat.BPay_9179
  · exact WuPaper.ClassicalFourthNat.BPay_9180
  · exact WuPaper.ClassicalFourthNat.BPay_9181
  · exact WuPaper.ClassicalFourthNat.BPay_9182
  · exact WuPaper.ClassicalFourthNat.BPay_9183
  · exact WuPaper.ClassicalFourthNat.BPay_9184
  · exact WuPaper.ClassicalFourthNat.BPay_9185
  · exact WuPaper.ClassicalFourthNat.BPay_9186
  · exact WuPaper.ClassicalFourthNat.BPay_9187
  · exact WuPaper.ClassicalFourthNat.BPay_9188
  · exact WuPaper.ClassicalFourthNat.BPay_9189
  · exact WuPaper.ClassicalFourthNat.BPay_9190
  · exact WuPaper.ClassicalFourthNat.BPay_9191
  · exact WuPaper.ClassicalFourthNat.BPay_9192
  · exact WuPaper.ClassicalFourthNat.BPay_9193
  · exact WuPaper.ClassicalFourthNat.BPay_9194
  · exact WuPaper.ClassicalFourthNat.BPay_9195
  · exact WuPaper.ClassicalFourthNat.BPay_9196
  · exact WuPaper.ClassicalFourthNat.BPay_9197
  · exact WuPaper.ClassicalFourthNat.BPay_9198
  · exact WuPaper.ClassicalFourthNat.BPay_9199
  · exact WuPaper.ClassicalFourthNat.BPay_9200
  · exact WuPaper.ClassicalFourthNat.BPay_9201
  · exact WuPaper.ClassicalFourthNat.BPay_9202
  · exact WuPaper.ClassicalFourthNat.BPay_9203
  · exact WuPaper.ClassicalFourthNat.BPay_9204
  · exact WuPaper.ClassicalFourthNat.BPay_9205
  · exact WuPaper.ClassicalFourthNat.BPay_9206
  · exact WuPaper.ClassicalFourthNat.BPay_9207
  · exact WuPaper.ClassicalFourthNat.BPay_9208
  · exact WuPaper.ClassicalFourthNat.BPay_9209
  · exact WuPaper.ClassicalFourthNat.BPay_9210
  · exact WuPaper.ClassicalFourthNat.BPay_9211
  · exact WuPaper.ClassicalFourthNat.BPay_9212
  · exact WuPaper.ClassicalFourthNat.BPay_9213
  · exact WuPaper.ClassicalFourthNat.BPay_9214
  · exact WuPaper.ClassicalFourthNat.BPay_9215
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_143
