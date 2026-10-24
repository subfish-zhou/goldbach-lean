import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay148
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_148 (j : Fin 64) (hj : 64*148+j.val < 10540) :
    BPay (64*148+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_9472
  · exact WuPaper.ClassicalFourthNat.BPay_9473
  · exact WuPaper.ClassicalFourthNat.BPay_9474
  · exact WuPaper.ClassicalFourthNat.BPay_9475
  · exact WuPaper.ClassicalFourthNat.BPay_9476
  · exact WuPaper.ClassicalFourthNat.BPay_9477
  · exact WuPaper.ClassicalFourthNat.BPay_9478
  · exact WuPaper.ClassicalFourthNat.BPay_9479
  · exact WuPaper.ClassicalFourthNat.BPay_9480
  · exact WuPaper.ClassicalFourthNat.BPay_9481
  · exact WuPaper.ClassicalFourthNat.BPay_9482
  · exact WuPaper.ClassicalFourthNat.BPay_9483
  · exact WuPaper.ClassicalFourthNat.BPay_9484
  · exact WuPaper.ClassicalFourthNat.BPay_9485
  · exact WuPaper.ClassicalFourthNat.BPay_9486
  · exact WuPaper.ClassicalFourthNat.BPay_9487
  · exact WuPaper.ClassicalFourthNat.BPay_9488
  · exact WuPaper.ClassicalFourthNat.BPay_9489
  · exact WuPaper.ClassicalFourthNat.BPay_9490
  · exact WuPaper.ClassicalFourthNat.BPay_9491
  · exact WuPaper.ClassicalFourthNat.BPay_9492
  · exact WuPaper.ClassicalFourthNat.BPay_9493
  · exact WuPaper.ClassicalFourthNat.BPay_9494
  · exact WuPaper.ClassicalFourthNat.BPay_9495
  · exact WuPaper.ClassicalFourthNat.BPay_9496
  · exact WuPaper.ClassicalFourthNat.BPay_9497
  · exact WuPaper.ClassicalFourthNat.BPay_9498
  · exact WuPaper.ClassicalFourthNat.BPay_9499
  · exact WuPaper.ClassicalFourthNat.BPay_9500
  · exact WuPaper.ClassicalFourthNat.BPay_9501
  · exact WuPaper.ClassicalFourthNat.BPay_9502
  · exact WuPaper.ClassicalFourthNat.BPay_9503
  · exact WuPaper.ClassicalFourthNat.BPay_9504
  · exact WuPaper.ClassicalFourthNat.BPay_9505
  · exact WuPaper.ClassicalFourthNat.BPay_9506
  · exact WuPaper.ClassicalFourthNat.BPay_9507
  · exact WuPaper.ClassicalFourthNat.BPay_9508
  · exact WuPaper.ClassicalFourthNat.BPay_9509
  · exact WuPaper.ClassicalFourthNat.BPay_9510
  · exact WuPaper.ClassicalFourthNat.BPay_9511
  · exact WuPaper.ClassicalFourthNat.BPay_9512
  · exact WuPaper.ClassicalFourthNat.BPay_9513
  · exact WuPaper.ClassicalFourthNat.BPay_9514
  · exact WuPaper.ClassicalFourthNat.BPay_9515
  · exact WuPaper.ClassicalFourthNat.BPay_9516
  · exact WuPaper.ClassicalFourthNat.BPay_9517
  · exact WuPaper.ClassicalFourthNat.BPay_9518
  · exact WuPaper.ClassicalFourthNat.BPay_9519
  · exact WuPaper.ClassicalFourthNat.BPay_9520
  · exact WuPaper.ClassicalFourthNat.BPay_9521
  · exact WuPaper.ClassicalFourthNat.BPay_9522
  · exact WuPaper.ClassicalFourthNat.BPay_9523
  · exact WuPaper.ClassicalFourthNat.BPay_9524
  · exact WuPaper.ClassicalFourthNat.BPay_9525
  · exact WuPaper.ClassicalFourthNat.BPay_9526
  · exact WuPaper.ClassicalFourthNat.BPay_9527
  · exact WuPaper.ClassicalFourthNat.BPay_9528
  · exact WuPaper.ClassicalFourthNat.BPay_9529
  · exact WuPaper.ClassicalFourthNat.BPay_9530
  · exact WuPaper.ClassicalFourthNat.BPay_9531
  · exact WuPaper.ClassicalFourthNat.BPay_9532
  · exact WuPaper.ClassicalFourthNat.BPay_9533
  · exact WuPaper.ClassicalFourthNat.BPay_9534
  · exact WuPaper.ClassicalFourthNat.BPay_9535
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_148
