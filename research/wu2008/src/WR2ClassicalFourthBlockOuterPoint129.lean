import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatOuterPoint129
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem OuterPoint_block_129 (j : Fin 64) (hj : 64*129+j.val < 10541) :
    OuterPoint (64*129+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8256
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8257
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8258
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8259
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8260
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8261
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8262
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8263
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8264
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8265
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8266
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8267
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8268
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8269
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8270
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8271
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8272
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8273
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8274
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8275
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8276
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8277
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8278
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8279
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8280
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8281
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8282
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8283
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8284
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8285
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8286
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8287
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8288
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8289
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8290
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8291
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8292
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8293
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8294
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8295
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8296
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8297
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8298
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8299
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8300
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8301
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8302
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8303
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8304
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8305
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8306
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8307
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8308
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8309
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8310
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8311
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8312
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8313
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8314
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8315
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8316
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8317
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8318
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8319
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.OuterPoint_block_129
