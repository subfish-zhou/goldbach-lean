import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay144
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_144 (j : Fin 64) (hj : 64*144+j.val < 10540) :
    BPay (64*144+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_9216
  · exact WuPaper.ClassicalFourthNat.BPay_9217
  · exact WuPaper.ClassicalFourthNat.BPay_9218
  · exact WuPaper.ClassicalFourthNat.BPay_9219
  · exact WuPaper.ClassicalFourthNat.BPay_9220
  · exact WuPaper.ClassicalFourthNat.BPay_9221
  · exact WuPaper.ClassicalFourthNat.BPay_9222
  · exact WuPaper.ClassicalFourthNat.BPay_9223
  · exact WuPaper.ClassicalFourthNat.BPay_9224
  · exact WuPaper.ClassicalFourthNat.BPay_9225
  · exact WuPaper.ClassicalFourthNat.BPay_9226
  · exact WuPaper.ClassicalFourthNat.BPay_9227
  · exact WuPaper.ClassicalFourthNat.BPay_9228
  · exact WuPaper.ClassicalFourthNat.BPay_9229
  · exact WuPaper.ClassicalFourthNat.BPay_9230
  · exact WuPaper.ClassicalFourthNat.BPay_9231
  · exact WuPaper.ClassicalFourthNat.BPay_9232
  · exact WuPaper.ClassicalFourthNat.BPay_9233
  · exact WuPaper.ClassicalFourthNat.BPay_9234
  · exact WuPaper.ClassicalFourthNat.BPay_9235
  · exact WuPaper.ClassicalFourthNat.BPay_9236
  · exact WuPaper.ClassicalFourthNat.BPay_9237
  · exact WuPaper.ClassicalFourthNat.BPay_9238
  · exact WuPaper.ClassicalFourthNat.BPay_9239
  · exact WuPaper.ClassicalFourthNat.BPay_9240
  · exact WuPaper.ClassicalFourthNat.BPay_9241
  · exact WuPaper.ClassicalFourthNat.BPay_9242
  · exact WuPaper.ClassicalFourthNat.BPay_9243
  · exact WuPaper.ClassicalFourthNat.BPay_9244
  · exact WuPaper.ClassicalFourthNat.BPay_9245
  · exact WuPaper.ClassicalFourthNat.BPay_9246
  · exact WuPaper.ClassicalFourthNat.BPay_9247
  · exact WuPaper.ClassicalFourthNat.BPay_9248
  · exact WuPaper.ClassicalFourthNat.BPay_9249
  · exact WuPaper.ClassicalFourthNat.BPay_9250
  · exact WuPaper.ClassicalFourthNat.BPay_9251
  · exact WuPaper.ClassicalFourthNat.BPay_9252
  · exact WuPaper.ClassicalFourthNat.BPay_9253
  · exact WuPaper.ClassicalFourthNat.BPay_9254
  · exact WuPaper.ClassicalFourthNat.BPay_9255
  · exact WuPaper.ClassicalFourthNat.BPay_9256
  · exact WuPaper.ClassicalFourthNat.BPay_9257
  · exact WuPaper.ClassicalFourthNat.BPay_9258
  · exact WuPaper.ClassicalFourthNat.BPay_9259
  · exact WuPaper.ClassicalFourthNat.BPay_9260
  · exact WuPaper.ClassicalFourthNat.BPay_9261
  · exact WuPaper.ClassicalFourthNat.BPay_9262
  · exact WuPaper.ClassicalFourthNat.BPay_9263
  · exact WuPaper.ClassicalFourthNat.BPay_9264
  · exact WuPaper.ClassicalFourthNat.BPay_9265
  · exact WuPaper.ClassicalFourthNat.BPay_9266
  · exact WuPaper.ClassicalFourthNat.BPay_9267
  · exact WuPaper.ClassicalFourthNat.BPay_9268
  · exact WuPaper.ClassicalFourthNat.BPay_9269
  · exact WuPaper.ClassicalFourthNat.BPay_9270
  · exact WuPaper.ClassicalFourthNat.BPay_9271
  · exact WuPaper.ClassicalFourthNat.BPay_9272
  · exact WuPaper.ClassicalFourthNat.BPay_9273
  · exact WuPaper.ClassicalFourthNat.BPay_9274
  · exact WuPaper.ClassicalFourthNat.BPay_9275
  · exact WuPaper.ClassicalFourthNat.BPay_9276
  · exact WuPaper.ClassicalFourthNat.BPay_9277
  · exact WuPaper.ClassicalFourthNat.BPay_9278
  · exact WuPaper.ClassicalFourthNat.BPay_9279
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_144
