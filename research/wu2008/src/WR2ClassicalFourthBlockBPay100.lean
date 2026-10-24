import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay100
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_100 (j : Fin 64) (hj : 64*100+j.val < 10540) :
    BPay (64*100+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_6400
  · exact WuPaper.ClassicalFourthNat.BPay_6401
  · exact WuPaper.ClassicalFourthNat.BPay_6402
  · exact WuPaper.ClassicalFourthNat.BPay_6403
  · exact WuPaper.ClassicalFourthNat.BPay_6404
  · exact WuPaper.ClassicalFourthNat.BPay_6405
  · exact WuPaper.ClassicalFourthNat.BPay_6406
  · exact WuPaper.ClassicalFourthNat.BPay_6407
  · exact WuPaper.ClassicalFourthNat.BPay_6408
  · exact WuPaper.ClassicalFourthNat.BPay_6409
  · exact WuPaper.ClassicalFourthNat.BPay_6410
  · exact WuPaper.ClassicalFourthNat.BPay_6411
  · exact WuPaper.ClassicalFourthNat.BPay_6412
  · exact WuPaper.ClassicalFourthNat.BPay_6413
  · exact WuPaper.ClassicalFourthNat.BPay_6414
  · exact WuPaper.ClassicalFourthNat.BPay_6415
  · exact WuPaper.ClassicalFourthNat.BPay_6416
  · exact WuPaper.ClassicalFourthNat.BPay_6417
  · exact WuPaper.ClassicalFourthNat.BPay_6418
  · exact WuPaper.ClassicalFourthNat.BPay_6419
  · exact WuPaper.ClassicalFourthNat.BPay_6420
  · exact WuPaper.ClassicalFourthNat.BPay_6421
  · exact WuPaper.ClassicalFourthNat.BPay_6422
  · exact WuPaper.ClassicalFourthNat.BPay_6423
  · exact WuPaper.ClassicalFourthNat.BPay_6424
  · exact WuPaper.ClassicalFourthNat.BPay_6425
  · exact WuPaper.ClassicalFourthNat.BPay_6426
  · exact WuPaper.ClassicalFourthNat.BPay_6427
  · exact WuPaper.ClassicalFourthNat.BPay_6428
  · exact WuPaper.ClassicalFourthNat.BPay_6429
  · exact WuPaper.ClassicalFourthNat.BPay_6430
  · exact WuPaper.ClassicalFourthNat.BPay_6431
  · exact WuPaper.ClassicalFourthNat.BPay_6432
  · exact WuPaper.ClassicalFourthNat.BPay_6433
  · exact WuPaper.ClassicalFourthNat.BPay_6434
  · exact WuPaper.ClassicalFourthNat.BPay_6435
  · exact WuPaper.ClassicalFourthNat.BPay_6436
  · exact WuPaper.ClassicalFourthNat.BPay_6437
  · exact WuPaper.ClassicalFourthNat.BPay_6438
  · exact WuPaper.ClassicalFourthNat.BPay_6439
  · exact WuPaper.ClassicalFourthNat.BPay_6440
  · exact WuPaper.ClassicalFourthNat.BPay_6441
  · exact WuPaper.ClassicalFourthNat.BPay_6442
  · exact WuPaper.ClassicalFourthNat.BPay_6443
  · exact WuPaper.ClassicalFourthNat.BPay_6444
  · exact WuPaper.ClassicalFourthNat.BPay_6445
  · exact WuPaper.ClassicalFourthNat.BPay_6446
  · exact WuPaper.ClassicalFourthNat.BPay_6447
  · exact WuPaper.ClassicalFourthNat.BPay_6448
  · exact WuPaper.ClassicalFourthNat.BPay_6449
  · exact WuPaper.ClassicalFourthNat.BPay_6450
  · exact WuPaper.ClassicalFourthNat.BPay_6451
  · exact WuPaper.ClassicalFourthNat.BPay_6452
  · exact WuPaper.ClassicalFourthNat.BPay_6453
  · exact WuPaper.ClassicalFourthNat.BPay_6454
  · exact WuPaper.ClassicalFourthNat.BPay_6455
  · exact WuPaper.ClassicalFourthNat.BPay_6456
  · exact WuPaper.ClassicalFourthNat.BPay_6457
  · exact WuPaper.ClassicalFourthNat.BPay_6458
  · exact WuPaper.ClassicalFourthNat.BPay_6459
  · exact WuPaper.ClassicalFourthNat.BPay_6460
  · exact WuPaper.ClassicalFourthNat.BPay_6461
  · exact WuPaper.ClassicalFourthNat.BPay_6462
  · exact WuPaper.ClassicalFourthNat.BPay_6463
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_100
