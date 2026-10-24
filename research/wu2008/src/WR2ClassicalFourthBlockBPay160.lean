import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay160
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_160 (j : Fin 64) (hj : 64*160+j.val < 10540) :
    BPay (64*160+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_10240
  · exact WuPaper.ClassicalFourthNat.BPay_10241
  · exact WuPaper.ClassicalFourthNat.BPay_10242
  · exact WuPaper.ClassicalFourthNat.BPay_10243
  · exact WuPaper.ClassicalFourthNat.BPay_10244
  · exact WuPaper.ClassicalFourthNat.BPay_10245
  · exact WuPaper.ClassicalFourthNat.BPay_10246
  · exact WuPaper.ClassicalFourthNat.BPay_10247
  · exact WuPaper.ClassicalFourthNat.BPay_10248
  · exact WuPaper.ClassicalFourthNat.BPay_10249
  · exact WuPaper.ClassicalFourthNat.BPay_10250
  · exact WuPaper.ClassicalFourthNat.BPay_10251
  · exact WuPaper.ClassicalFourthNat.BPay_10252
  · exact WuPaper.ClassicalFourthNat.BPay_10253
  · exact WuPaper.ClassicalFourthNat.BPay_10254
  · exact WuPaper.ClassicalFourthNat.BPay_10255
  · exact WuPaper.ClassicalFourthNat.BPay_10256
  · exact WuPaper.ClassicalFourthNat.BPay_10257
  · exact WuPaper.ClassicalFourthNat.BPay_10258
  · exact WuPaper.ClassicalFourthNat.BPay_10259
  · exact WuPaper.ClassicalFourthNat.BPay_10260
  · exact WuPaper.ClassicalFourthNat.BPay_10261
  · exact WuPaper.ClassicalFourthNat.BPay_10262
  · exact WuPaper.ClassicalFourthNat.BPay_10263
  · exact WuPaper.ClassicalFourthNat.BPay_10264
  · exact WuPaper.ClassicalFourthNat.BPay_10265
  · exact WuPaper.ClassicalFourthNat.BPay_10266
  · exact WuPaper.ClassicalFourthNat.BPay_10267
  · exact WuPaper.ClassicalFourthNat.BPay_10268
  · exact WuPaper.ClassicalFourthNat.BPay_10269
  · exact WuPaper.ClassicalFourthNat.BPay_10270
  · exact WuPaper.ClassicalFourthNat.BPay_10271
  · exact WuPaper.ClassicalFourthNat.BPay_10272
  · exact WuPaper.ClassicalFourthNat.BPay_10273
  · exact WuPaper.ClassicalFourthNat.BPay_10274
  · exact WuPaper.ClassicalFourthNat.BPay_10275
  · exact WuPaper.ClassicalFourthNat.BPay_10276
  · exact WuPaper.ClassicalFourthNat.BPay_10277
  · exact WuPaper.ClassicalFourthNat.BPay_10278
  · exact WuPaper.ClassicalFourthNat.BPay_10279
  · exact WuPaper.ClassicalFourthNat.BPay_10280
  · exact WuPaper.ClassicalFourthNat.BPay_10281
  · exact WuPaper.ClassicalFourthNat.BPay_10282
  · exact WuPaper.ClassicalFourthNat.BPay_10283
  · exact WuPaper.ClassicalFourthNat.BPay_10284
  · exact WuPaper.ClassicalFourthNat.BPay_10285
  · exact WuPaper.ClassicalFourthNat.BPay_10286
  · exact WuPaper.ClassicalFourthNat.BPay_10287
  · exact WuPaper.ClassicalFourthNat.BPay_10288
  · exact WuPaper.ClassicalFourthNat.BPay_10289
  · exact WuPaper.ClassicalFourthNat.BPay_10290
  · exact WuPaper.ClassicalFourthNat.BPay_10291
  · exact WuPaper.ClassicalFourthNat.BPay_10292
  · exact WuPaper.ClassicalFourthNat.BPay_10293
  · exact WuPaper.ClassicalFourthNat.BPay_10294
  · exact WuPaper.ClassicalFourthNat.BPay_10295
  · exact WuPaper.ClassicalFourthNat.BPay_10296
  · exact WuPaper.ClassicalFourthNat.BPay_10297
  · exact WuPaper.ClassicalFourthNat.BPay_10298
  · exact WuPaper.ClassicalFourthNat.BPay_10299
  · exact WuPaper.ClassicalFourthNat.BPay_10300
  · exact WuPaper.ClassicalFourthNat.BPay_10301
  · exact WuPaper.ClassicalFourthNat.BPay_10302
  · exact WuPaper.ClassicalFourthNat.BPay_10303
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_160
