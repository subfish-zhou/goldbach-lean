import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatouterPay129
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem outerPay_block_129 (j : Fin 64) (hj : 64*129+j.val < 10540) :
    OuterPay (64*129+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.outerPay_8256
  · exact WuPaper.ClassicalFourthNat.outerPay_8257
  · exact WuPaper.ClassicalFourthNat.outerPay_8258
  · exact WuPaper.ClassicalFourthNat.outerPay_8259
  · exact WuPaper.ClassicalFourthNat.outerPay_8260
  · exact WuPaper.ClassicalFourthNat.outerPay_8261
  · exact WuPaper.ClassicalFourthNat.outerPay_8262
  · exact WuPaper.ClassicalFourthNat.outerPay_8263
  · exact WuPaper.ClassicalFourthNat.outerPay_8264
  · exact WuPaper.ClassicalFourthNat.outerPay_8265
  · exact WuPaper.ClassicalFourthNat.outerPay_8266
  · exact WuPaper.ClassicalFourthNat.outerPay_8267
  · exact WuPaper.ClassicalFourthNat.outerPay_8268
  · exact WuPaper.ClassicalFourthNat.outerPay_8269
  · exact WuPaper.ClassicalFourthNat.outerPay_8270
  · exact WuPaper.ClassicalFourthNat.outerPay_8271
  · exact WuPaper.ClassicalFourthNat.outerPay_8272
  · exact WuPaper.ClassicalFourthNat.outerPay_8273
  · exact WuPaper.ClassicalFourthNat.outerPay_8274
  · exact WuPaper.ClassicalFourthNat.outerPay_8275
  · exact WuPaper.ClassicalFourthNat.outerPay_8276
  · exact WuPaper.ClassicalFourthNat.outerPay_8277
  · exact WuPaper.ClassicalFourthNat.outerPay_8278
  · exact WuPaper.ClassicalFourthNat.outerPay_8279
  · exact WuPaper.ClassicalFourthNat.outerPay_8280
  · exact WuPaper.ClassicalFourthNat.outerPay_8281
  · exact WuPaper.ClassicalFourthNat.outerPay_8282
  · exact WuPaper.ClassicalFourthNat.outerPay_8283
  · exact WuPaper.ClassicalFourthNat.outerPay_8284
  · exact WuPaper.ClassicalFourthNat.outerPay_8285
  · exact WuPaper.ClassicalFourthNat.outerPay_8286
  · exact WuPaper.ClassicalFourthNat.outerPay_8287
  · exact WuPaper.ClassicalFourthNat.outerPay_8288
  · exact WuPaper.ClassicalFourthNat.outerPay_8289
  · exact WuPaper.ClassicalFourthNat.outerPay_8290
  · exact WuPaper.ClassicalFourthNat.outerPay_8291
  · exact WuPaper.ClassicalFourthNat.outerPay_8292
  · exact WuPaper.ClassicalFourthNat.outerPay_8293
  · exact WuPaper.ClassicalFourthNat.outerPay_8294
  · exact WuPaper.ClassicalFourthNat.outerPay_8295
  · exact WuPaper.ClassicalFourthNat.outerPay_8296
  · exact WuPaper.ClassicalFourthNat.outerPay_8297
  · exact WuPaper.ClassicalFourthNat.outerPay_8298
  · exact WuPaper.ClassicalFourthNat.outerPay_8299
  · exact WuPaper.ClassicalFourthNat.outerPay_8300
  · exact WuPaper.ClassicalFourthNat.outerPay_8301
  · exact WuPaper.ClassicalFourthNat.outerPay_8302
  · exact WuPaper.ClassicalFourthNat.outerPay_8303
  · exact WuPaper.ClassicalFourthNat.outerPay_8304
  · exact WuPaper.ClassicalFourthNat.outerPay_8305
  · exact WuPaper.ClassicalFourthNat.outerPay_8306
  · exact WuPaper.ClassicalFourthNat.outerPay_8307
  · exact WuPaper.ClassicalFourthNat.outerPay_8308
  · exact WuPaper.ClassicalFourthNat.outerPay_8309
  · exact WuPaper.ClassicalFourthNat.outerPay_8310
  · exact WuPaper.ClassicalFourthNat.outerPay_8311
  · exact WuPaper.ClassicalFourthNat.outerPay_8312
  · exact WuPaper.ClassicalFourthNat.outerPay_8313
  · exact WuPaper.ClassicalFourthNat.outerPay_8314
  · exact WuPaper.ClassicalFourthNat.outerPay_8315
  · exact WuPaper.ClassicalFourthNat.outerPay_8316
  · exact WuPaper.ClassicalFourthNat.outerPay_8317
  · exact WuPaper.ClassicalFourthNat.outerPay_8318
  · exact WuPaper.ClassicalFourthNat.outerPay_8319
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.outerPay_block_129
