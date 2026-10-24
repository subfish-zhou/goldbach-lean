import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay129
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_129 (j : Fin 64) (hj : 64*129+j.val < 10540) :
    BPay (64*129+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_8256
  · exact WuPaper.ClassicalFourthNat.BPay_8257
  · exact WuPaper.ClassicalFourthNat.BPay_8258
  · exact WuPaper.ClassicalFourthNat.BPay_8259
  · exact WuPaper.ClassicalFourthNat.BPay_8260
  · exact WuPaper.ClassicalFourthNat.BPay_8261
  · exact WuPaper.ClassicalFourthNat.BPay_8262
  · exact WuPaper.ClassicalFourthNat.BPay_8263
  · exact WuPaper.ClassicalFourthNat.BPay_8264
  · exact WuPaper.ClassicalFourthNat.BPay_8265
  · exact WuPaper.ClassicalFourthNat.BPay_8266
  · exact WuPaper.ClassicalFourthNat.BPay_8267
  · exact WuPaper.ClassicalFourthNat.BPay_8268
  · exact WuPaper.ClassicalFourthNat.BPay_8269
  · exact WuPaper.ClassicalFourthNat.BPay_8270
  · exact WuPaper.ClassicalFourthNat.BPay_8271
  · exact WuPaper.ClassicalFourthNat.BPay_8272
  · exact WuPaper.ClassicalFourthNat.BPay_8273
  · exact WuPaper.ClassicalFourthNat.BPay_8274
  · exact WuPaper.ClassicalFourthNat.BPay_8275
  · exact WuPaper.ClassicalFourthNat.BPay_8276
  · exact WuPaper.ClassicalFourthNat.BPay_8277
  · exact WuPaper.ClassicalFourthNat.BPay_8278
  · exact WuPaper.ClassicalFourthNat.BPay_8279
  · exact WuPaper.ClassicalFourthNat.BPay_8280
  · exact WuPaper.ClassicalFourthNat.BPay_8281
  · exact WuPaper.ClassicalFourthNat.BPay_8282
  · exact WuPaper.ClassicalFourthNat.BPay_8283
  · exact WuPaper.ClassicalFourthNat.BPay_8284
  · exact WuPaper.ClassicalFourthNat.BPay_8285
  · exact WuPaper.ClassicalFourthNat.BPay_8286
  · exact WuPaper.ClassicalFourthNat.BPay_8287
  · exact WuPaper.ClassicalFourthNat.BPay_8288
  · exact WuPaper.ClassicalFourthNat.BPay_8289
  · exact WuPaper.ClassicalFourthNat.BPay_8290
  · exact WuPaper.ClassicalFourthNat.BPay_8291
  · exact WuPaper.ClassicalFourthNat.BPay_8292
  · exact WuPaper.ClassicalFourthNat.BPay_8293
  · exact WuPaper.ClassicalFourthNat.BPay_8294
  · exact WuPaper.ClassicalFourthNat.BPay_8295
  · exact WuPaper.ClassicalFourthNat.BPay_8296
  · exact WuPaper.ClassicalFourthNat.BPay_8297
  · exact WuPaper.ClassicalFourthNat.BPay_8298
  · exact WuPaper.ClassicalFourthNat.BPay_8299
  · exact WuPaper.ClassicalFourthNat.BPay_8300
  · exact WuPaper.ClassicalFourthNat.BPay_8301
  · exact WuPaper.ClassicalFourthNat.BPay_8302
  · exact WuPaper.ClassicalFourthNat.BPay_8303
  · exact WuPaper.ClassicalFourthNat.BPay_8304
  · exact WuPaper.ClassicalFourthNat.BPay_8305
  · exact WuPaper.ClassicalFourthNat.BPay_8306
  · exact WuPaper.ClassicalFourthNat.BPay_8307
  · exact WuPaper.ClassicalFourthNat.BPay_8308
  · exact WuPaper.ClassicalFourthNat.BPay_8309
  · exact WuPaper.ClassicalFourthNat.BPay_8310
  · exact WuPaper.ClassicalFourthNat.BPay_8311
  · exact WuPaper.ClassicalFourthNat.BPay_8312
  · exact WuPaper.ClassicalFourthNat.BPay_8313
  · exact WuPaper.ClassicalFourthNat.BPay_8314
  · exact WuPaper.ClassicalFourthNat.BPay_8315
  · exact WuPaper.ClassicalFourthNat.BPay_8316
  · exact WuPaper.ClassicalFourthNat.BPay_8317
  · exact WuPaper.ClassicalFourthNat.BPay_8318
  · exact WuPaper.ClassicalFourthNat.BPay_8319
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_129
