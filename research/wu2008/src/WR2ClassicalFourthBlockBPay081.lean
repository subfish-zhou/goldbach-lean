import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay081
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_081 (j : Fin 64) (hj : 64*81+j.val < 10540) :
    BPay (64*81+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_5184
  · exact WuPaper.ClassicalFourthNat.BPay_5185
  · exact WuPaper.ClassicalFourthNat.BPay_5186
  · exact WuPaper.ClassicalFourthNat.BPay_5187
  · exact WuPaper.ClassicalFourthNat.BPay_5188
  · exact WuPaper.ClassicalFourthNat.BPay_5189
  · exact WuPaper.ClassicalFourthNat.BPay_5190
  · exact WuPaper.ClassicalFourthNat.BPay_5191
  · exact WuPaper.ClassicalFourthNat.BPay_5192
  · exact WuPaper.ClassicalFourthNat.BPay_5193
  · exact WuPaper.ClassicalFourthNat.BPay_5194
  · exact WuPaper.ClassicalFourthNat.BPay_5195
  · exact WuPaper.ClassicalFourthNat.BPay_5196
  · exact WuPaper.ClassicalFourthNat.BPay_5197
  · exact WuPaper.ClassicalFourthNat.BPay_5198
  · exact WuPaper.ClassicalFourthNat.BPay_5199
  · exact WuPaper.ClassicalFourthNat.BPay_5200
  · exact WuPaper.ClassicalFourthNat.BPay_5201
  · exact WuPaper.ClassicalFourthNat.BPay_5202
  · exact WuPaper.ClassicalFourthNat.BPay_5203
  · exact WuPaper.ClassicalFourthNat.BPay_5204
  · exact WuPaper.ClassicalFourthNat.BPay_5205
  · exact WuPaper.ClassicalFourthNat.BPay_5206
  · exact WuPaper.ClassicalFourthNat.BPay_5207
  · exact WuPaper.ClassicalFourthNat.BPay_5208
  · exact WuPaper.ClassicalFourthNat.BPay_5209
  · exact WuPaper.ClassicalFourthNat.BPay_5210
  · exact WuPaper.ClassicalFourthNat.BPay_5211
  · exact WuPaper.ClassicalFourthNat.BPay_5212
  · exact WuPaper.ClassicalFourthNat.BPay_5213
  · exact WuPaper.ClassicalFourthNat.BPay_5214
  · exact WuPaper.ClassicalFourthNat.BPay_5215
  · exact WuPaper.ClassicalFourthNat.BPay_5216
  · exact WuPaper.ClassicalFourthNat.BPay_5217
  · exact WuPaper.ClassicalFourthNat.BPay_5218
  · exact WuPaper.ClassicalFourthNat.BPay_5219
  · exact WuPaper.ClassicalFourthNat.BPay_5220
  · exact WuPaper.ClassicalFourthNat.BPay_5221
  · exact WuPaper.ClassicalFourthNat.BPay_5222
  · exact WuPaper.ClassicalFourthNat.BPay_5223
  · exact WuPaper.ClassicalFourthNat.BPay_5224
  · exact WuPaper.ClassicalFourthNat.BPay_5225
  · exact WuPaper.ClassicalFourthNat.BPay_5226
  · exact WuPaper.ClassicalFourthNat.BPay_5227
  · exact WuPaper.ClassicalFourthNat.BPay_5228
  · exact WuPaper.ClassicalFourthNat.BPay_5229
  · exact WuPaper.ClassicalFourthNat.BPay_5230
  · exact WuPaper.ClassicalFourthNat.BPay_5231
  · exact WuPaper.ClassicalFourthNat.BPay_5232
  · exact WuPaper.ClassicalFourthNat.BPay_5233
  · exact WuPaper.ClassicalFourthNat.BPay_5234
  · exact WuPaper.ClassicalFourthNat.BPay_5235
  · exact WuPaper.ClassicalFourthNat.BPay_5236
  · exact WuPaper.ClassicalFourthNat.BPay_5237
  · exact WuPaper.ClassicalFourthNat.BPay_5238
  · exact WuPaper.ClassicalFourthNat.BPay_5239
  · exact WuPaper.ClassicalFourthNat.BPay_5240
  · exact WuPaper.ClassicalFourthNat.BPay_5241
  · exact WuPaper.ClassicalFourthNat.BPay_5242
  · exact WuPaper.ClassicalFourthNat.BPay_5243
  · exact WuPaper.ClassicalFourthNat.BPay_5244
  · exact WuPaper.ClassicalFourthNat.BPay_5245
  · exact WuPaper.ClassicalFourthNat.BPay_5246
  · exact WuPaper.ClassicalFourthNat.BPay_5247
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_081
