import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay159
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_159 (j : Fin 64) (hj : 64*159+j.val < 10540) :
    BPay (64*159+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_10176
  · exact WuPaper.ClassicalFourthNat.BPay_10177
  · exact WuPaper.ClassicalFourthNat.BPay_10178
  · exact WuPaper.ClassicalFourthNat.BPay_10179
  · exact WuPaper.ClassicalFourthNat.BPay_10180
  · exact WuPaper.ClassicalFourthNat.BPay_10181
  · exact WuPaper.ClassicalFourthNat.BPay_10182
  · exact WuPaper.ClassicalFourthNat.BPay_10183
  · exact WuPaper.ClassicalFourthNat.BPay_10184
  · exact WuPaper.ClassicalFourthNat.BPay_10185
  · exact WuPaper.ClassicalFourthNat.BPay_10186
  · exact WuPaper.ClassicalFourthNat.BPay_10187
  · exact WuPaper.ClassicalFourthNat.BPay_10188
  · exact WuPaper.ClassicalFourthNat.BPay_10189
  · exact WuPaper.ClassicalFourthNat.BPay_10190
  · exact WuPaper.ClassicalFourthNat.BPay_10191
  · exact WuPaper.ClassicalFourthNat.BPay_10192
  · exact WuPaper.ClassicalFourthNat.BPay_10193
  · exact WuPaper.ClassicalFourthNat.BPay_10194
  · exact WuPaper.ClassicalFourthNat.BPay_10195
  · exact WuPaper.ClassicalFourthNat.BPay_10196
  · exact WuPaper.ClassicalFourthNat.BPay_10197
  · exact WuPaper.ClassicalFourthNat.BPay_10198
  · exact WuPaper.ClassicalFourthNat.BPay_10199
  · exact WuPaper.ClassicalFourthNat.BPay_10200
  · exact WuPaper.ClassicalFourthNat.BPay_10201
  · exact WuPaper.ClassicalFourthNat.BPay_10202
  · exact WuPaper.ClassicalFourthNat.BPay_10203
  · exact WuPaper.ClassicalFourthNat.BPay_10204
  · exact WuPaper.ClassicalFourthNat.BPay_10205
  · exact WuPaper.ClassicalFourthNat.BPay_10206
  · exact WuPaper.ClassicalFourthNat.BPay_10207
  · exact WuPaper.ClassicalFourthNat.BPay_10208
  · exact WuPaper.ClassicalFourthNat.BPay_10209
  · exact WuPaper.ClassicalFourthNat.BPay_10210
  · exact WuPaper.ClassicalFourthNat.BPay_10211
  · exact WuPaper.ClassicalFourthNat.BPay_10212
  · exact WuPaper.ClassicalFourthNat.BPay_10213
  · exact WuPaper.ClassicalFourthNat.BPay_10214
  · exact WuPaper.ClassicalFourthNat.BPay_10215
  · exact WuPaper.ClassicalFourthNat.BPay_10216
  · exact WuPaper.ClassicalFourthNat.BPay_10217
  · exact WuPaper.ClassicalFourthNat.BPay_10218
  · exact WuPaper.ClassicalFourthNat.BPay_10219
  · exact WuPaper.ClassicalFourthNat.BPay_10220
  · exact WuPaper.ClassicalFourthNat.BPay_10221
  · exact WuPaper.ClassicalFourthNat.BPay_10222
  · exact WuPaper.ClassicalFourthNat.BPay_10223
  · exact WuPaper.ClassicalFourthNat.BPay_10224
  · exact WuPaper.ClassicalFourthNat.BPay_10225
  · exact WuPaper.ClassicalFourthNat.BPay_10226
  · exact WuPaper.ClassicalFourthNat.BPay_10227
  · exact WuPaper.ClassicalFourthNat.BPay_10228
  · exact WuPaper.ClassicalFourthNat.BPay_10229
  · exact WuPaper.ClassicalFourthNat.BPay_10230
  · exact WuPaper.ClassicalFourthNat.BPay_10231
  · exact WuPaper.ClassicalFourthNat.BPay_10232
  · exact WuPaper.ClassicalFourthNat.BPay_10233
  · exact WuPaper.ClassicalFourthNat.BPay_10234
  · exact WuPaper.ClassicalFourthNat.BPay_10235
  · exact WuPaper.ClassicalFourthNat.BPay_10236
  · exact WuPaper.ClassicalFourthNat.BPay_10237
  · exact WuPaper.ClassicalFourthNat.BPay_10238
  · exact WuPaper.ClassicalFourthNat.BPay_10239
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_159
