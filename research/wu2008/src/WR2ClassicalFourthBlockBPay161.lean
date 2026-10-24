import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay161
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_161 (j : Fin 64) (hj : 64*161+j.val < 10540) :
    BPay (64*161+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_10304
  · exact WuPaper.ClassicalFourthNat.BPay_10305
  · exact WuPaper.ClassicalFourthNat.BPay_10306
  · exact WuPaper.ClassicalFourthNat.BPay_10307
  · exact WuPaper.ClassicalFourthNat.BPay_10308
  · exact WuPaper.ClassicalFourthNat.BPay_10309
  · exact WuPaper.ClassicalFourthNat.BPay_10310
  · exact WuPaper.ClassicalFourthNat.BPay_10311
  · exact WuPaper.ClassicalFourthNat.BPay_10312
  · exact WuPaper.ClassicalFourthNat.BPay_10313
  · exact WuPaper.ClassicalFourthNat.BPay_10314
  · exact WuPaper.ClassicalFourthNat.BPay_10315
  · exact WuPaper.ClassicalFourthNat.BPay_10316
  · exact WuPaper.ClassicalFourthNat.BPay_10317
  · exact WuPaper.ClassicalFourthNat.BPay_10318
  · exact WuPaper.ClassicalFourthNat.BPay_10319
  · exact WuPaper.ClassicalFourthNat.BPay_10320
  · exact WuPaper.ClassicalFourthNat.BPay_10321
  · exact WuPaper.ClassicalFourthNat.BPay_10322
  · exact WuPaper.ClassicalFourthNat.BPay_10323
  · exact WuPaper.ClassicalFourthNat.BPay_10324
  · exact WuPaper.ClassicalFourthNat.BPay_10325
  · exact WuPaper.ClassicalFourthNat.BPay_10326
  · exact WuPaper.ClassicalFourthNat.BPay_10327
  · exact WuPaper.ClassicalFourthNat.BPay_10328
  · exact WuPaper.ClassicalFourthNat.BPay_10329
  · exact WuPaper.ClassicalFourthNat.BPay_10330
  · exact WuPaper.ClassicalFourthNat.BPay_10331
  · exact WuPaper.ClassicalFourthNat.BPay_10332
  · exact WuPaper.ClassicalFourthNat.BPay_10333
  · exact WuPaper.ClassicalFourthNat.BPay_10334
  · exact WuPaper.ClassicalFourthNat.BPay_10335
  · exact WuPaper.ClassicalFourthNat.BPay_10336
  · exact WuPaper.ClassicalFourthNat.BPay_10337
  · exact WuPaper.ClassicalFourthNat.BPay_10338
  · exact WuPaper.ClassicalFourthNat.BPay_10339
  · exact WuPaper.ClassicalFourthNat.BPay_10340
  · exact WuPaper.ClassicalFourthNat.BPay_10341
  · exact WuPaper.ClassicalFourthNat.BPay_10342
  · exact WuPaper.ClassicalFourthNat.BPay_10343
  · exact WuPaper.ClassicalFourthNat.BPay_10344
  · exact WuPaper.ClassicalFourthNat.BPay_10345
  · exact WuPaper.ClassicalFourthNat.BPay_10346
  · exact WuPaper.ClassicalFourthNat.BPay_10347
  · exact WuPaper.ClassicalFourthNat.BPay_10348
  · exact WuPaper.ClassicalFourthNat.BPay_10349
  · exact WuPaper.ClassicalFourthNat.BPay_10350
  · exact WuPaper.ClassicalFourthNat.BPay_10351
  · exact WuPaper.ClassicalFourthNat.BPay_10352
  · exact WuPaper.ClassicalFourthNat.BPay_10353
  · exact WuPaper.ClassicalFourthNat.BPay_10354
  · exact WuPaper.ClassicalFourthNat.BPay_10355
  · exact WuPaper.ClassicalFourthNat.BPay_10356
  · exact WuPaper.ClassicalFourthNat.BPay_10357
  · exact WuPaper.ClassicalFourthNat.BPay_10358
  · exact WuPaper.ClassicalFourthNat.BPay_10359
  · exact WuPaper.ClassicalFourthNat.BPay_10360
  · exact WuPaper.ClassicalFourthNat.BPay_10361
  · exact WuPaper.ClassicalFourthNat.BPay_10362
  · exact WuPaper.ClassicalFourthNat.BPay_10363
  · exact WuPaper.ClassicalFourthNat.BPay_10364
  · exact WuPaper.ClassicalFourthNat.BPay_10365
  · exact WuPaper.ClassicalFourthNat.BPay_10366
  · exact WuPaper.ClassicalFourthNat.BPay_10367
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_161
