import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatOuterPoint100
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem OuterPoint_block_100 (j : Fin 64) (hj : 64*100+j.val < 10541) :
    OuterPoint (64*100+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6400
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6401
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6402
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6403
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6404
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6405
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6406
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6407
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6408
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6409
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6410
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6411
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6412
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6413
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6414
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6415
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6416
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6417
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6418
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6419
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6420
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6421
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6422
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6423
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6424
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6425
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6426
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6427
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6428
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6429
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6430
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6431
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6432
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6433
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6434
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6435
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6436
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6437
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6438
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6439
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6440
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6441
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6442
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6443
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6444
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6445
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6446
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6447
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6448
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6449
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6450
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6451
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6452
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6453
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6454
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6455
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6456
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6457
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6458
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6459
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6460
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6461
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6462
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6463
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.OuterPoint_block_100
