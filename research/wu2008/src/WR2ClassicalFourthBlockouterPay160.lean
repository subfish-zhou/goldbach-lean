import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatouterPay160
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem outerPay_block_160 (j : Fin 64) (hj : 64*160+j.val < 10540) :
    OuterPay (64*160+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.outerPay_10240
  · exact WuPaper.ClassicalFourthNat.outerPay_10241
  · exact WuPaper.ClassicalFourthNat.outerPay_10242
  · exact WuPaper.ClassicalFourthNat.outerPay_10243
  · exact WuPaper.ClassicalFourthNat.outerPay_10244
  · exact WuPaper.ClassicalFourthNat.outerPay_10245
  · exact WuPaper.ClassicalFourthNat.outerPay_10246
  · exact WuPaper.ClassicalFourthNat.outerPay_10247
  · exact WuPaper.ClassicalFourthNat.outerPay_10248
  · exact WuPaper.ClassicalFourthNat.outerPay_10249
  · exact WuPaper.ClassicalFourthNat.outerPay_10250
  · exact WuPaper.ClassicalFourthNat.outerPay_10251
  · exact WuPaper.ClassicalFourthNat.outerPay_10252
  · exact WuPaper.ClassicalFourthNat.outerPay_10253
  · exact WuPaper.ClassicalFourthNat.outerPay_10254
  · exact WuPaper.ClassicalFourthNat.outerPay_10255
  · exact WuPaper.ClassicalFourthNat.outerPay_10256
  · exact WuPaper.ClassicalFourthNat.outerPay_10257
  · exact WuPaper.ClassicalFourthNat.outerPay_10258
  · exact WuPaper.ClassicalFourthNat.outerPay_10259
  · exact WuPaper.ClassicalFourthNat.outerPay_10260
  · exact WuPaper.ClassicalFourthNat.outerPay_10261
  · exact WuPaper.ClassicalFourthNat.outerPay_10262
  · exact WuPaper.ClassicalFourthNat.outerPay_10263
  · exact WuPaper.ClassicalFourthNat.outerPay_10264
  · exact WuPaper.ClassicalFourthNat.outerPay_10265
  · exact WuPaper.ClassicalFourthNat.outerPay_10266
  · exact WuPaper.ClassicalFourthNat.outerPay_10267
  · exact WuPaper.ClassicalFourthNat.outerPay_10268
  · exact WuPaper.ClassicalFourthNat.outerPay_10269
  · exact WuPaper.ClassicalFourthNat.outerPay_10270
  · exact WuPaper.ClassicalFourthNat.outerPay_10271
  · exact WuPaper.ClassicalFourthNat.outerPay_10272
  · exact WuPaper.ClassicalFourthNat.outerPay_10273
  · exact WuPaper.ClassicalFourthNat.outerPay_10274
  · exact WuPaper.ClassicalFourthNat.outerPay_10275
  · exact WuPaper.ClassicalFourthNat.outerPay_10276
  · exact WuPaper.ClassicalFourthNat.outerPay_10277
  · exact WuPaper.ClassicalFourthNat.outerPay_10278
  · exact WuPaper.ClassicalFourthNat.outerPay_10279
  · exact WuPaper.ClassicalFourthNat.outerPay_10280
  · exact WuPaper.ClassicalFourthNat.outerPay_10281
  · exact WuPaper.ClassicalFourthNat.outerPay_10282
  · exact WuPaper.ClassicalFourthNat.outerPay_10283
  · exact WuPaper.ClassicalFourthNat.outerPay_10284
  · exact WuPaper.ClassicalFourthNat.outerPay_10285
  · exact WuPaper.ClassicalFourthNat.outerPay_10286
  · exact WuPaper.ClassicalFourthNat.outerPay_10287
  · exact WuPaper.ClassicalFourthNat.outerPay_10288
  · exact WuPaper.ClassicalFourthNat.outerPay_10289
  · exact WuPaper.ClassicalFourthNat.outerPay_10290
  · exact WuPaper.ClassicalFourthNat.outerPay_10291
  · exact WuPaper.ClassicalFourthNat.outerPay_10292
  · exact WuPaper.ClassicalFourthNat.outerPay_10293
  · exact WuPaper.ClassicalFourthNat.outerPay_10294
  · exact WuPaper.ClassicalFourthNat.outerPay_10295
  · exact WuPaper.ClassicalFourthNat.outerPay_10296
  · exact WuPaper.ClassicalFourthNat.outerPay_10297
  · exact WuPaper.ClassicalFourthNat.outerPay_10298
  · exact WuPaper.ClassicalFourthNat.outerPay_10299
  · exact WuPaper.ClassicalFourthNat.outerPay_10300
  · exact WuPaper.ClassicalFourthNat.outerPay_10301
  · exact WuPaper.ClassicalFourthNat.outerPay_10302
  · exact WuPaper.ClassicalFourthNat.outerPay_10303
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.outerPay_block_160
