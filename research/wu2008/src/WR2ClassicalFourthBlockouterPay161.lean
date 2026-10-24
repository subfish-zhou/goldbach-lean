import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatouterPay161
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem outerPay_block_161 (j : Fin 64) (hj : 64*161+j.val < 10540) :
    OuterPay (64*161+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.outerPay_10304
  · exact WuPaper.ClassicalFourthNat.outerPay_10305
  · exact WuPaper.ClassicalFourthNat.outerPay_10306
  · exact WuPaper.ClassicalFourthNat.outerPay_10307
  · exact WuPaper.ClassicalFourthNat.outerPay_10308
  · exact WuPaper.ClassicalFourthNat.outerPay_10309
  · exact WuPaper.ClassicalFourthNat.outerPay_10310
  · exact WuPaper.ClassicalFourthNat.outerPay_10311
  · exact WuPaper.ClassicalFourthNat.outerPay_10312
  · exact WuPaper.ClassicalFourthNat.outerPay_10313
  · exact WuPaper.ClassicalFourthNat.outerPay_10314
  · exact WuPaper.ClassicalFourthNat.outerPay_10315
  · exact WuPaper.ClassicalFourthNat.outerPay_10316
  · exact WuPaper.ClassicalFourthNat.outerPay_10317
  · exact WuPaper.ClassicalFourthNat.outerPay_10318
  · exact WuPaper.ClassicalFourthNat.outerPay_10319
  · exact WuPaper.ClassicalFourthNat.outerPay_10320
  · exact WuPaper.ClassicalFourthNat.outerPay_10321
  · exact WuPaper.ClassicalFourthNat.outerPay_10322
  · exact WuPaper.ClassicalFourthNat.outerPay_10323
  · exact WuPaper.ClassicalFourthNat.outerPay_10324
  · exact WuPaper.ClassicalFourthNat.outerPay_10325
  · exact WuPaper.ClassicalFourthNat.outerPay_10326
  · exact WuPaper.ClassicalFourthNat.outerPay_10327
  · exact WuPaper.ClassicalFourthNat.outerPay_10328
  · exact WuPaper.ClassicalFourthNat.outerPay_10329
  · exact WuPaper.ClassicalFourthNat.outerPay_10330
  · exact WuPaper.ClassicalFourthNat.outerPay_10331
  · exact WuPaper.ClassicalFourthNat.outerPay_10332
  · exact WuPaper.ClassicalFourthNat.outerPay_10333
  · exact WuPaper.ClassicalFourthNat.outerPay_10334
  · exact WuPaper.ClassicalFourthNat.outerPay_10335
  · exact WuPaper.ClassicalFourthNat.outerPay_10336
  · exact WuPaper.ClassicalFourthNat.outerPay_10337
  · exact WuPaper.ClassicalFourthNat.outerPay_10338
  · exact WuPaper.ClassicalFourthNat.outerPay_10339
  · exact WuPaper.ClassicalFourthNat.outerPay_10340
  · exact WuPaper.ClassicalFourthNat.outerPay_10341
  · exact WuPaper.ClassicalFourthNat.outerPay_10342
  · exact WuPaper.ClassicalFourthNat.outerPay_10343
  · exact WuPaper.ClassicalFourthNat.outerPay_10344
  · exact WuPaper.ClassicalFourthNat.outerPay_10345
  · exact WuPaper.ClassicalFourthNat.outerPay_10346
  · exact WuPaper.ClassicalFourthNat.outerPay_10347
  · exact WuPaper.ClassicalFourthNat.outerPay_10348
  · exact WuPaper.ClassicalFourthNat.outerPay_10349
  · exact WuPaper.ClassicalFourthNat.outerPay_10350
  · exact WuPaper.ClassicalFourthNat.outerPay_10351
  · exact WuPaper.ClassicalFourthNat.outerPay_10352
  · exact WuPaper.ClassicalFourthNat.outerPay_10353
  · exact WuPaper.ClassicalFourthNat.outerPay_10354
  · exact WuPaper.ClassicalFourthNat.outerPay_10355
  · exact WuPaper.ClassicalFourthNat.outerPay_10356
  · exact WuPaper.ClassicalFourthNat.outerPay_10357
  · exact WuPaper.ClassicalFourthNat.outerPay_10358
  · exact WuPaper.ClassicalFourthNat.outerPay_10359
  · exact WuPaper.ClassicalFourthNat.outerPay_10360
  · exact WuPaper.ClassicalFourthNat.outerPay_10361
  · exact WuPaper.ClassicalFourthNat.outerPay_10362
  · exact WuPaper.ClassicalFourthNat.outerPay_10363
  · exact WuPaper.ClassicalFourthNat.outerPay_10364
  · exact WuPaper.ClassicalFourthNat.outerPay_10365
  · exact WuPaper.ClassicalFourthNat.outerPay_10366
  · exact WuPaper.ClassicalFourthNat.outerPay_10367
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.outerPay_block_161
