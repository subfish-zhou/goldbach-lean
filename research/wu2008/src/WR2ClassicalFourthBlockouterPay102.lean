import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatouterPay102
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem outerPay_block_102 (j : Fin 64) (hj : 64*102+j.val < 10540) :
    OuterPay (64*102+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.outerPay_6528
  · exact WuPaper.ClassicalFourthNat.outerPay_6529
  · exact WuPaper.ClassicalFourthNat.outerPay_6530
  · exact WuPaper.ClassicalFourthNat.outerPay_6531
  · exact WuPaper.ClassicalFourthNat.outerPay_6532
  · exact WuPaper.ClassicalFourthNat.outerPay_6533
  · exact WuPaper.ClassicalFourthNat.outerPay_6534
  · exact WuPaper.ClassicalFourthNat.outerPay_6535
  · exact WuPaper.ClassicalFourthNat.outerPay_6536
  · exact WuPaper.ClassicalFourthNat.outerPay_6537
  · exact WuPaper.ClassicalFourthNat.outerPay_6538
  · exact WuPaper.ClassicalFourthNat.outerPay_6539
  · exact WuPaper.ClassicalFourthNat.outerPay_6540
  · exact WuPaper.ClassicalFourthNat.outerPay_6541
  · exact WuPaper.ClassicalFourthNat.outerPay_6542
  · exact WuPaper.ClassicalFourthNat.outerPay_6543
  · exact WuPaper.ClassicalFourthNat.outerPay_6544
  · exact WuPaper.ClassicalFourthNat.outerPay_6545
  · exact WuPaper.ClassicalFourthNat.outerPay_6546
  · exact WuPaper.ClassicalFourthNat.outerPay_6547
  · exact WuPaper.ClassicalFourthNat.outerPay_6548
  · exact WuPaper.ClassicalFourthNat.outerPay_6549
  · exact WuPaper.ClassicalFourthNat.outerPay_6550
  · exact WuPaper.ClassicalFourthNat.outerPay_6551
  · exact WuPaper.ClassicalFourthNat.outerPay_6552
  · exact WuPaper.ClassicalFourthNat.outerPay_6553
  · exact WuPaper.ClassicalFourthNat.outerPay_6554
  · exact WuPaper.ClassicalFourthNat.outerPay_6555
  · exact WuPaper.ClassicalFourthNat.outerPay_6556
  · exact WuPaper.ClassicalFourthNat.outerPay_6557
  · exact WuPaper.ClassicalFourthNat.outerPay_6558
  · exact WuPaper.ClassicalFourthNat.outerPay_6559
  · exact WuPaper.ClassicalFourthNat.outerPay_6560
  · exact WuPaper.ClassicalFourthNat.outerPay_6561
  · exact WuPaper.ClassicalFourthNat.outerPay_6562
  · exact WuPaper.ClassicalFourthNat.outerPay_6563
  · exact WuPaper.ClassicalFourthNat.outerPay_6564
  · exact WuPaper.ClassicalFourthNat.outerPay_6565
  · exact WuPaper.ClassicalFourthNat.outerPay_6566
  · exact WuPaper.ClassicalFourthNat.outerPay_6567
  · exact WuPaper.ClassicalFourthNat.outerPay_6568
  · exact WuPaper.ClassicalFourthNat.outerPay_6569
  · exact WuPaper.ClassicalFourthNat.outerPay_6570
  · exact WuPaper.ClassicalFourthNat.outerPay_6571
  · exact WuPaper.ClassicalFourthNat.outerPay_6572
  · exact WuPaper.ClassicalFourthNat.outerPay_6573
  · exact WuPaper.ClassicalFourthNat.outerPay_6574
  · exact WuPaper.ClassicalFourthNat.outerPay_6575
  · exact WuPaper.ClassicalFourthNat.outerPay_6576
  · exact WuPaper.ClassicalFourthNat.outerPay_6577
  · exact WuPaper.ClassicalFourthNat.outerPay_6578
  · exact WuPaper.ClassicalFourthNat.outerPay_6579
  · exact WuPaper.ClassicalFourthNat.outerPay_6580
  · exact WuPaper.ClassicalFourthNat.outerPay_6581
  · exact WuPaper.ClassicalFourthNat.outerPay_6582
  · exact WuPaper.ClassicalFourthNat.outerPay_6583
  · exact WuPaper.ClassicalFourthNat.outerPay_6584
  · exact WuPaper.ClassicalFourthNat.outerPay_6585
  · exact WuPaper.ClassicalFourthNat.outerPay_6586
  · exact WuPaper.ClassicalFourthNat.outerPay_6587
  · exact WuPaper.ClassicalFourthNat.outerPay_6588
  · exact WuPaper.ClassicalFourthNat.outerPay_6589
  · exact WuPaper.ClassicalFourthNat.outerPay_6590
  · exact WuPaper.ClassicalFourthNat.outerPay_6591
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.outerPay_block_102
