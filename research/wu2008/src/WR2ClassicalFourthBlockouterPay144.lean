import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatouterPay144
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem outerPay_block_144 (j : Fin 64) (hj : 64*144+j.val < 10540) :
    OuterPay (64*144+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.outerPay_9216
  · exact WuPaper.ClassicalFourthNat.outerPay_9217
  · exact WuPaper.ClassicalFourthNat.outerPay_9218
  · exact WuPaper.ClassicalFourthNat.outerPay_9219
  · exact WuPaper.ClassicalFourthNat.outerPay_9220
  · exact WuPaper.ClassicalFourthNat.outerPay_9221
  · exact WuPaper.ClassicalFourthNat.outerPay_9222
  · exact WuPaper.ClassicalFourthNat.outerPay_9223
  · exact WuPaper.ClassicalFourthNat.outerPay_9224
  · exact WuPaper.ClassicalFourthNat.outerPay_9225
  · exact WuPaper.ClassicalFourthNat.outerPay_9226
  · exact WuPaper.ClassicalFourthNat.outerPay_9227
  · exact WuPaper.ClassicalFourthNat.outerPay_9228
  · exact WuPaper.ClassicalFourthNat.outerPay_9229
  · exact WuPaper.ClassicalFourthNat.outerPay_9230
  · exact WuPaper.ClassicalFourthNat.outerPay_9231
  · exact WuPaper.ClassicalFourthNat.outerPay_9232
  · exact WuPaper.ClassicalFourthNat.outerPay_9233
  · exact WuPaper.ClassicalFourthNat.outerPay_9234
  · exact WuPaper.ClassicalFourthNat.outerPay_9235
  · exact WuPaper.ClassicalFourthNat.outerPay_9236
  · exact WuPaper.ClassicalFourthNat.outerPay_9237
  · exact WuPaper.ClassicalFourthNat.outerPay_9238
  · exact WuPaper.ClassicalFourthNat.outerPay_9239
  · exact WuPaper.ClassicalFourthNat.outerPay_9240
  · exact WuPaper.ClassicalFourthNat.outerPay_9241
  · exact WuPaper.ClassicalFourthNat.outerPay_9242
  · exact WuPaper.ClassicalFourthNat.outerPay_9243
  · exact WuPaper.ClassicalFourthNat.outerPay_9244
  · exact WuPaper.ClassicalFourthNat.outerPay_9245
  · exact WuPaper.ClassicalFourthNat.outerPay_9246
  · exact WuPaper.ClassicalFourthNat.outerPay_9247
  · exact WuPaper.ClassicalFourthNat.outerPay_9248
  · exact WuPaper.ClassicalFourthNat.outerPay_9249
  · exact WuPaper.ClassicalFourthNat.outerPay_9250
  · exact WuPaper.ClassicalFourthNat.outerPay_9251
  · exact WuPaper.ClassicalFourthNat.outerPay_9252
  · exact WuPaper.ClassicalFourthNat.outerPay_9253
  · exact WuPaper.ClassicalFourthNat.outerPay_9254
  · exact WuPaper.ClassicalFourthNat.outerPay_9255
  · exact WuPaper.ClassicalFourthNat.outerPay_9256
  · exact WuPaper.ClassicalFourthNat.outerPay_9257
  · exact WuPaper.ClassicalFourthNat.outerPay_9258
  · exact WuPaper.ClassicalFourthNat.outerPay_9259
  · exact WuPaper.ClassicalFourthNat.outerPay_9260
  · exact WuPaper.ClassicalFourthNat.outerPay_9261
  · exact WuPaper.ClassicalFourthNat.outerPay_9262
  · exact WuPaper.ClassicalFourthNat.outerPay_9263
  · exact WuPaper.ClassicalFourthNat.outerPay_9264
  · exact WuPaper.ClassicalFourthNat.outerPay_9265
  · exact WuPaper.ClassicalFourthNat.outerPay_9266
  · exact WuPaper.ClassicalFourthNat.outerPay_9267
  · exact WuPaper.ClassicalFourthNat.outerPay_9268
  · exact WuPaper.ClassicalFourthNat.outerPay_9269
  · exact WuPaper.ClassicalFourthNat.outerPay_9270
  · exact WuPaper.ClassicalFourthNat.outerPay_9271
  · exact WuPaper.ClassicalFourthNat.outerPay_9272
  · exact WuPaper.ClassicalFourthNat.outerPay_9273
  · exact WuPaper.ClassicalFourthNat.outerPay_9274
  · exact WuPaper.ClassicalFourthNat.outerPay_9275
  · exact WuPaper.ClassicalFourthNat.outerPay_9276
  · exact WuPaper.ClassicalFourthNat.outerPay_9277
  · exact WuPaper.ClassicalFourthNat.outerPay_9278
  · exact WuPaper.ClassicalFourthNat.outerPay_9279
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.outerPay_block_144
