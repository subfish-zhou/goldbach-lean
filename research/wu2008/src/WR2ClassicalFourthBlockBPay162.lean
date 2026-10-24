import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay162
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_162 (j : Fin 64) (hj : 64*162+j.val < 10540) :
    BPay (64*162+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_10368
  · exact WuPaper.ClassicalFourthNat.BPay_10369
  · exact WuPaper.ClassicalFourthNat.BPay_10370
  · exact WuPaper.ClassicalFourthNat.BPay_10371
  · exact WuPaper.ClassicalFourthNat.BPay_10372
  · exact WuPaper.ClassicalFourthNat.BPay_10373
  · exact WuPaper.ClassicalFourthNat.BPay_10374
  · exact WuPaper.ClassicalFourthNat.BPay_10375
  · exact WuPaper.ClassicalFourthNat.BPay_10376
  · exact WuPaper.ClassicalFourthNat.BPay_10377
  · exact WuPaper.ClassicalFourthNat.BPay_10378
  · exact WuPaper.ClassicalFourthNat.BPay_10379
  · exact WuPaper.ClassicalFourthNat.BPay_10380
  · exact WuPaper.ClassicalFourthNat.BPay_10381
  · exact WuPaper.ClassicalFourthNat.BPay_10382
  · exact WuPaper.ClassicalFourthNat.BPay_10383
  · exact WuPaper.ClassicalFourthNat.BPay_10384
  · exact WuPaper.ClassicalFourthNat.BPay_10385
  · exact WuPaper.ClassicalFourthNat.BPay_10386
  · exact WuPaper.ClassicalFourthNat.BPay_10387
  · exact WuPaper.ClassicalFourthNat.BPay_10388
  · exact WuPaper.ClassicalFourthNat.BPay_10389
  · exact WuPaper.ClassicalFourthNat.BPay_10390
  · exact WuPaper.ClassicalFourthNat.BPay_10391
  · exact WuPaper.ClassicalFourthNat.BPay_10392
  · exact WuPaper.ClassicalFourthNat.BPay_10393
  · exact WuPaper.ClassicalFourthNat.BPay_10394
  · exact WuPaper.ClassicalFourthNat.BPay_10395
  · exact WuPaper.ClassicalFourthNat.BPay_10396
  · exact WuPaper.ClassicalFourthNat.BPay_10397
  · exact WuPaper.ClassicalFourthNat.BPay_10398
  · exact WuPaper.ClassicalFourthNat.BPay_10399
  · exact WuPaper.ClassicalFourthNat.BPay_10400
  · exact WuPaper.ClassicalFourthNat.BPay_10401
  · exact WuPaper.ClassicalFourthNat.BPay_10402
  · exact WuPaper.ClassicalFourthNat.BPay_10403
  · exact WuPaper.ClassicalFourthNat.BPay_10404
  · exact WuPaper.ClassicalFourthNat.BPay_10405
  · exact WuPaper.ClassicalFourthNat.BPay_10406
  · exact WuPaper.ClassicalFourthNat.BPay_10407
  · exact WuPaper.ClassicalFourthNat.BPay_10408
  · exact WuPaper.ClassicalFourthNat.BPay_10409
  · exact WuPaper.ClassicalFourthNat.BPay_10410
  · exact WuPaper.ClassicalFourthNat.BPay_10411
  · exact WuPaper.ClassicalFourthNat.BPay_10412
  · exact WuPaper.ClassicalFourthNat.BPay_10413
  · exact WuPaper.ClassicalFourthNat.BPay_10414
  · exact WuPaper.ClassicalFourthNat.BPay_10415
  · exact WuPaper.ClassicalFourthNat.BPay_10416
  · exact WuPaper.ClassicalFourthNat.BPay_10417
  · exact WuPaper.ClassicalFourthNat.BPay_10418
  · exact WuPaper.ClassicalFourthNat.BPay_10419
  · exact WuPaper.ClassicalFourthNat.BPay_10420
  · exact WuPaper.ClassicalFourthNat.BPay_10421
  · exact WuPaper.ClassicalFourthNat.BPay_10422
  · exact WuPaper.ClassicalFourthNat.BPay_10423
  · exact WuPaper.ClassicalFourthNat.BPay_10424
  · exact WuPaper.ClassicalFourthNat.BPay_10425
  · exact WuPaper.ClassicalFourthNat.BPay_10426
  · exact WuPaper.ClassicalFourthNat.BPay_10427
  · exact WuPaper.ClassicalFourthNat.BPay_10428
  · exact WuPaper.ClassicalFourthNat.BPay_10429
  · exact WuPaper.ClassicalFourthNat.BPay_10430
  · exact WuPaper.ClassicalFourthNat.BPay_10431
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_162
