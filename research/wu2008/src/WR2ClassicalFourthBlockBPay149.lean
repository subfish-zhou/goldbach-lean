import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay149
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_149 (j : Fin 64) (hj : 64*149+j.val < 10540) :
    BPay (64*149+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_9536
  · exact WuPaper.ClassicalFourthNat.BPay_9537
  · exact WuPaper.ClassicalFourthNat.BPay_9538
  · exact WuPaper.ClassicalFourthNat.BPay_9539
  · exact WuPaper.ClassicalFourthNat.BPay_9540
  · exact WuPaper.ClassicalFourthNat.BPay_9541
  · exact WuPaper.ClassicalFourthNat.BPay_9542
  · exact WuPaper.ClassicalFourthNat.BPay_9543
  · exact WuPaper.ClassicalFourthNat.BPay_9544
  · exact WuPaper.ClassicalFourthNat.BPay_9545
  · exact WuPaper.ClassicalFourthNat.BPay_9546
  · exact WuPaper.ClassicalFourthNat.BPay_9547
  · exact WuPaper.ClassicalFourthNat.BPay_9548
  · exact WuPaper.ClassicalFourthNat.BPay_9549
  · exact WuPaper.ClassicalFourthNat.BPay_9550
  · exact WuPaper.ClassicalFourthNat.BPay_9551
  · exact WuPaper.ClassicalFourthNat.BPay_9552
  · exact WuPaper.ClassicalFourthNat.BPay_9553
  · exact WuPaper.ClassicalFourthNat.BPay_9554
  · exact WuPaper.ClassicalFourthNat.BPay_9555
  · exact WuPaper.ClassicalFourthNat.BPay_9556
  · exact WuPaper.ClassicalFourthNat.BPay_9557
  · exact WuPaper.ClassicalFourthNat.BPay_9558
  · exact WuPaper.ClassicalFourthNat.BPay_9559
  · exact WuPaper.ClassicalFourthNat.BPay_9560
  · exact WuPaper.ClassicalFourthNat.BPay_9561
  · exact WuPaper.ClassicalFourthNat.BPay_9562
  · exact WuPaper.ClassicalFourthNat.BPay_9563
  · exact WuPaper.ClassicalFourthNat.BPay_9564
  · exact WuPaper.ClassicalFourthNat.BPay_9565
  · exact WuPaper.ClassicalFourthNat.BPay_9566
  · exact WuPaper.ClassicalFourthNat.BPay_9567
  · exact WuPaper.ClassicalFourthNat.BPay_9568
  · exact WuPaper.ClassicalFourthNat.BPay_9569
  · exact WuPaper.ClassicalFourthNat.BPay_9570
  · exact WuPaper.ClassicalFourthNat.BPay_9571
  · exact WuPaper.ClassicalFourthNat.BPay_9572
  · exact WuPaper.ClassicalFourthNat.BPay_9573
  · exact WuPaper.ClassicalFourthNat.BPay_9574
  · exact WuPaper.ClassicalFourthNat.BPay_9575
  · exact WuPaper.ClassicalFourthNat.BPay_9576
  · exact WuPaper.ClassicalFourthNat.BPay_9577
  · exact WuPaper.ClassicalFourthNat.BPay_9578
  · exact WuPaper.ClassicalFourthNat.BPay_9579
  · exact WuPaper.ClassicalFourthNat.BPay_9580
  · exact WuPaper.ClassicalFourthNat.BPay_9581
  · exact WuPaper.ClassicalFourthNat.BPay_9582
  · exact WuPaper.ClassicalFourthNat.BPay_9583
  · exact WuPaper.ClassicalFourthNat.BPay_9584
  · exact WuPaper.ClassicalFourthNat.BPay_9585
  · exact WuPaper.ClassicalFourthNat.BPay_9586
  · exact WuPaper.ClassicalFourthNat.BPay_9587
  · exact WuPaper.ClassicalFourthNat.BPay_9588
  · exact WuPaper.ClassicalFourthNat.BPay_9589
  · exact WuPaper.ClassicalFourthNat.BPay_9590
  · exact WuPaper.ClassicalFourthNat.BPay_9591
  · exact WuPaper.ClassicalFourthNat.BPay_9592
  · exact WuPaper.ClassicalFourthNat.BPay_9593
  · exact WuPaper.ClassicalFourthNat.BPay_9594
  · exact WuPaper.ClassicalFourthNat.BPay_9595
  · exact WuPaper.ClassicalFourthNat.BPay_9596
  · exact WuPaper.ClassicalFourthNat.BPay_9597
  · exact WuPaper.ClassicalFourthNat.BPay_9598
  · exact WuPaper.ClassicalFourthNat.BPay_9599
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_149
