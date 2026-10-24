import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay102
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_102 (j : Fin 64) (hj : 64*102+j.val < 10540) :
    BPay (64*102+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_6528
  · exact WuPaper.ClassicalFourthNat.BPay_6529
  · exact WuPaper.ClassicalFourthNat.BPay_6530
  · exact WuPaper.ClassicalFourthNat.BPay_6531
  · exact WuPaper.ClassicalFourthNat.BPay_6532
  · exact WuPaper.ClassicalFourthNat.BPay_6533
  · exact WuPaper.ClassicalFourthNat.BPay_6534
  · exact WuPaper.ClassicalFourthNat.BPay_6535
  · exact WuPaper.ClassicalFourthNat.BPay_6536
  · exact WuPaper.ClassicalFourthNat.BPay_6537
  · exact WuPaper.ClassicalFourthNat.BPay_6538
  · exact WuPaper.ClassicalFourthNat.BPay_6539
  · exact WuPaper.ClassicalFourthNat.BPay_6540
  · exact WuPaper.ClassicalFourthNat.BPay_6541
  · exact WuPaper.ClassicalFourthNat.BPay_6542
  · exact WuPaper.ClassicalFourthNat.BPay_6543
  · exact WuPaper.ClassicalFourthNat.BPay_6544
  · exact WuPaper.ClassicalFourthNat.BPay_6545
  · exact WuPaper.ClassicalFourthNat.BPay_6546
  · exact WuPaper.ClassicalFourthNat.BPay_6547
  · exact WuPaper.ClassicalFourthNat.BPay_6548
  · exact WuPaper.ClassicalFourthNat.BPay_6549
  · exact WuPaper.ClassicalFourthNat.BPay_6550
  · exact WuPaper.ClassicalFourthNat.BPay_6551
  · exact WuPaper.ClassicalFourthNat.BPay_6552
  · exact WuPaper.ClassicalFourthNat.BPay_6553
  · exact WuPaper.ClassicalFourthNat.BPay_6554
  · exact WuPaper.ClassicalFourthNat.BPay_6555
  · exact WuPaper.ClassicalFourthNat.BPay_6556
  · exact WuPaper.ClassicalFourthNat.BPay_6557
  · exact WuPaper.ClassicalFourthNat.BPay_6558
  · exact WuPaper.ClassicalFourthNat.BPay_6559
  · exact WuPaper.ClassicalFourthNat.BPay_6560
  · exact WuPaper.ClassicalFourthNat.BPay_6561
  · exact WuPaper.ClassicalFourthNat.BPay_6562
  · exact WuPaper.ClassicalFourthNat.BPay_6563
  · exact WuPaper.ClassicalFourthNat.BPay_6564
  · exact WuPaper.ClassicalFourthNat.BPay_6565
  · exact WuPaper.ClassicalFourthNat.BPay_6566
  · exact WuPaper.ClassicalFourthNat.BPay_6567
  · exact WuPaper.ClassicalFourthNat.BPay_6568
  · exact WuPaper.ClassicalFourthNat.BPay_6569
  · exact WuPaper.ClassicalFourthNat.BPay_6570
  · exact WuPaper.ClassicalFourthNat.BPay_6571
  · exact WuPaper.ClassicalFourthNat.BPay_6572
  · exact WuPaper.ClassicalFourthNat.BPay_6573
  · exact WuPaper.ClassicalFourthNat.BPay_6574
  · exact WuPaper.ClassicalFourthNat.BPay_6575
  · exact WuPaper.ClassicalFourthNat.BPay_6576
  · exact WuPaper.ClassicalFourthNat.BPay_6577
  · exact WuPaper.ClassicalFourthNat.BPay_6578
  · exact WuPaper.ClassicalFourthNat.BPay_6579
  · exact WuPaper.ClassicalFourthNat.BPay_6580
  · exact WuPaper.ClassicalFourthNat.BPay_6581
  · exact WuPaper.ClassicalFourthNat.BPay_6582
  · exact WuPaper.ClassicalFourthNat.BPay_6583
  · exact WuPaper.ClassicalFourthNat.BPay_6584
  · exact WuPaper.ClassicalFourthNat.BPay_6585
  · exact WuPaper.ClassicalFourthNat.BPay_6586
  · exact WuPaper.ClassicalFourthNat.BPay_6587
  · exact WuPaper.ClassicalFourthNat.BPay_6588
  · exact WuPaper.ClassicalFourthNat.BPay_6589
  · exact WuPaper.ClassicalFourthNat.BPay_6590
  · exact WuPaper.ClassicalFourthNat.BPay_6591
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_102
