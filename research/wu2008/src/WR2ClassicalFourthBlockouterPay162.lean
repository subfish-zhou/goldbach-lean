import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatouterPay162
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem outerPay_block_162 (j : Fin 64) (hj : 64*162+j.val < 10540) :
    OuterPay (64*162+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.outerPay_10368
  · exact WuPaper.ClassicalFourthNat.outerPay_10369
  · exact WuPaper.ClassicalFourthNat.outerPay_10370
  · exact WuPaper.ClassicalFourthNat.outerPay_10371
  · exact WuPaper.ClassicalFourthNat.outerPay_10372
  · exact WuPaper.ClassicalFourthNat.outerPay_10373
  · exact WuPaper.ClassicalFourthNat.outerPay_10374
  · exact WuPaper.ClassicalFourthNat.outerPay_10375
  · exact WuPaper.ClassicalFourthNat.outerPay_10376
  · exact WuPaper.ClassicalFourthNat.outerPay_10377
  · exact WuPaper.ClassicalFourthNat.outerPay_10378
  · exact WuPaper.ClassicalFourthNat.outerPay_10379
  · exact WuPaper.ClassicalFourthNat.outerPay_10380
  · exact WuPaper.ClassicalFourthNat.outerPay_10381
  · exact WuPaper.ClassicalFourthNat.outerPay_10382
  · exact WuPaper.ClassicalFourthNat.outerPay_10383
  · exact WuPaper.ClassicalFourthNat.outerPay_10384
  · exact WuPaper.ClassicalFourthNat.outerPay_10385
  · exact WuPaper.ClassicalFourthNat.outerPay_10386
  · exact WuPaper.ClassicalFourthNat.outerPay_10387
  · exact WuPaper.ClassicalFourthNat.outerPay_10388
  · exact WuPaper.ClassicalFourthNat.outerPay_10389
  · exact WuPaper.ClassicalFourthNat.outerPay_10390
  · exact WuPaper.ClassicalFourthNat.outerPay_10391
  · exact WuPaper.ClassicalFourthNat.outerPay_10392
  · exact WuPaper.ClassicalFourthNat.outerPay_10393
  · exact WuPaper.ClassicalFourthNat.outerPay_10394
  · exact WuPaper.ClassicalFourthNat.outerPay_10395
  · exact WuPaper.ClassicalFourthNat.outerPay_10396
  · exact WuPaper.ClassicalFourthNat.outerPay_10397
  · exact WuPaper.ClassicalFourthNat.outerPay_10398
  · exact WuPaper.ClassicalFourthNat.outerPay_10399
  · exact WuPaper.ClassicalFourthNat.outerPay_10400
  · exact WuPaper.ClassicalFourthNat.outerPay_10401
  · exact WuPaper.ClassicalFourthNat.outerPay_10402
  · exact WuPaper.ClassicalFourthNat.outerPay_10403
  · exact WuPaper.ClassicalFourthNat.outerPay_10404
  · exact WuPaper.ClassicalFourthNat.outerPay_10405
  · exact WuPaper.ClassicalFourthNat.outerPay_10406
  · exact WuPaper.ClassicalFourthNat.outerPay_10407
  · exact WuPaper.ClassicalFourthNat.outerPay_10408
  · exact WuPaper.ClassicalFourthNat.outerPay_10409
  · exact WuPaper.ClassicalFourthNat.outerPay_10410
  · exact WuPaper.ClassicalFourthNat.outerPay_10411
  · exact WuPaper.ClassicalFourthNat.outerPay_10412
  · exact WuPaper.ClassicalFourthNat.outerPay_10413
  · exact WuPaper.ClassicalFourthNat.outerPay_10414
  · exact WuPaper.ClassicalFourthNat.outerPay_10415
  · exact WuPaper.ClassicalFourthNat.outerPay_10416
  · exact WuPaper.ClassicalFourthNat.outerPay_10417
  · exact WuPaper.ClassicalFourthNat.outerPay_10418
  · exact WuPaper.ClassicalFourthNat.outerPay_10419
  · exact WuPaper.ClassicalFourthNat.outerPay_10420
  · exact WuPaper.ClassicalFourthNat.outerPay_10421
  · exact WuPaper.ClassicalFourthNat.outerPay_10422
  · exact WuPaper.ClassicalFourthNat.outerPay_10423
  · exact WuPaper.ClassicalFourthNat.outerPay_10424
  · exact WuPaper.ClassicalFourthNat.outerPay_10425
  · exact WuPaper.ClassicalFourthNat.outerPay_10426
  · exact WuPaper.ClassicalFourthNat.outerPay_10427
  · exact WuPaper.ClassicalFourthNat.outerPay_10428
  · exact WuPaper.ClassicalFourthNat.outerPay_10429
  · exact WuPaper.ClassicalFourthNat.outerPay_10430
  · exact WuPaper.ClassicalFourthNat.outerPay_10431
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.outerPay_block_162
