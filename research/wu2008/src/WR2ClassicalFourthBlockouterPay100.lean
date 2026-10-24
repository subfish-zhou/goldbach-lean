import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatouterPay100
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem outerPay_block_100 (j : Fin 64) (hj : 64*100+j.val < 10540) :
    OuterPay (64*100+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.outerPay_6400
  · exact WuPaper.ClassicalFourthNat.outerPay_6401
  · exact WuPaper.ClassicalFourthNat.outerPay_6402
  · exact WuPaper.ClassicalFourthNat.outerPay_6403
  · exact WuPaper.ClassicalFourthNat.outerPay_6404
  · exact WuPaper.ClassicalFourthNat.outerPay_6405
  · exact WuPaper.ClassicalFourthNat.outerPay_6406
  · exact WuPaper.ClassicalFourthNat.outerPay_6407
  · exact WuPaper.ClassicalFourthNat.outerPay_6408
  · exact WuPaper.ClassicalFourthNat.outerPay_6409
  · exact WuPaper.ClassicalFourthNat.outerPay_6410
  · exact WuPaper.ClassicalFourthNat.outerPay_6411
  · exact WuPaper.ClassicalFourthNat.outerPay_6412
  · exact WuPaper.ClassicalFourthNat.outerPay_6413
  · exact WuPaper.ClassicalFourthNat.outerPay_6414
  · exact WuPaper.ClassicalFourthNat.outerPay_6415
  · exact WuPaper.ClassicalFourthNat.outerPay_6416
  · exact WuPaper.ClassicalFourthNat.outerPay_6417
  · exact WuPaper.ClassicalFourthNat.outerPay_6418
  · exact WuPaper.ClassicalFourthNat.outerPay_6419
  · exact WuPaper.ClassicalFourthNat.outerPay_6420
  · exact WuPaper.ClassicalFourthNat.outerPay_6421
  · exact WuPaper.ClassicalFourthNat.outerPay_6422
  · exact WuPaper.ClassicalFourthNat.outerPay_6423
  · exact WuPaper.ClassicalFourthNat.outerPay_6424
  · exact WuPaper.ClassicalFourthNat.outerPay_6425
  · exact WuPaper.ClassicalFourthNat.outerPay_6426
  · exact WuPaper.ClassicalFourthNat.outerPay_6427
  · exact WuPaper.ClassicalFourthNat.outerPay_6428
  · exact WuPaper.ClassicalFourthNat.outerPay_6429
  · exact WuPaper.ClassicalFourthNat.outerPay_6430
  · exact WuPaper.ClassicalFourthNat.outerPay_6431
  · exact WuPaper.ClassicalFourthNat.outerPay_6432
  · exact WuPaper.ClassicalFourthNat.outerPay_6433
  · exact WuPaper.ClassicalFourthNat.outerPay_6434
  · exact WuPaper.ClassicalFourthNat.outerPay_6435
  · exact WuPaper.ClassicalFourthNat.outerPay_6436
  · exact WuPaper.ClassicalFourthNat.outerPay_6437
  · exact WuPaper.ClassicalFourthNat.outerPay_6438
  · exact WuPaper.ClassicalFourthNat.outerPay_6439
  · exact WuPaper.ClassicalFourthNat.outerPay_6440
  · exact WuPaper.ClassicalFourthNat.outerPay_6441
  · exact WuPaper.ClassicalFourthNat.outerPay_6442
  · exact WuPaper.ClassicalFourthNat.outerPay_6443
  · exact WuPaper.ClassicalFourthNat.outerPay_6444
  · exact WuPaper.ClassicalFourthNat.outerPay_6445
  · exact WuPaper.ClassicalFourthNat.outerPay_6446
  · exact WuPaper.ClassicalFourthNat.outerPay_6447
  · exact WuPaper.ClassicalFourthNat.outerPay_6448
  · exact WuPaper.ClassicalFourthNat.outerPay_6449
  · exact WuPaper.ClassicalFourthNat.outerPay_6450
  · exact WuPaper.ClassicalFourthNat.outerPay_6451
  · exact WuPaper.ClassicalFourthNat.outerPay_6452
  · exact WuPaper.ClassicalFourthNat.outerPay_6453
  · exact WuPaper.ClassicalFourthNat.outerPay_6454
  · exact WuPaper.ClassicalFourthNat.outerPay_6455
  · exact WuPaper.ClassicalFourthNat.outerPay_6456
  · exact WuPaper.ClassicalFourthNat.outerPay_6457
  · exact WuPaper.ClassicalFourthNat.outerPay_6458
  · exact WuPaper.ClassicalFourthNat.outerPay_6459
  · exact WuPaper.ClassicalFourthNat.outerPay_6460
  · exact WuPaper.ClassicalFourthNat.outerPay_6461
  · exact WuPaper.ClassicalFourthNat.outerPay_6462
  · exact WuPaper.ClassicalFourthNat.outerPay_6463
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.outerPay_block_100
