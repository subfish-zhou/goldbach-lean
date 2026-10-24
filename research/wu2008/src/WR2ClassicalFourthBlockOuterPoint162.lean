import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatOuterPoint162
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem OuterPoint_block_162 (j : Fin 64) (hj : 64*162+j.val < 10541) :
    OuterPoint (64*162+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10368
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10369
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10370
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10371
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10372
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10373
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10374
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10375
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10376
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10377
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10378
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10379
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10380
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10381
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10382
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10383
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10384
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10385
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10386
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10387
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10388
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10389
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10390
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10391
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10392
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10393
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10394
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10395
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10396
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10397
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10398
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10399
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10400
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10401
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10402
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10403
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10404
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10405
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10406
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10407
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10408
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10409
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10410
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10411
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10412
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10413
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10414
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10415
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10416
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10417
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10418
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10419
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10420
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10421
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10422
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10423
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10424
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10425
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10426
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10427
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10428
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10429
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10430
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10431
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.OuterPoint_block_162
