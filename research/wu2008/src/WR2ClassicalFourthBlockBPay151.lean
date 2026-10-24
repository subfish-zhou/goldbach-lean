import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay151
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_151 (j : Fin 64) (hj : 64*151+j.val < 10540) :
    BPay (64*151+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_9664
  · exact WuPaper.ClassicalFourthNat.BPay_9665
  · exact WuPaper.ClassicalFourthNat.BPay_9666
  · exact WuPaper.ClassicalFourthNat.BPay_9667
  · exact WuPaper.ClassicalFourthNat.BPay_9668
  · exact WuPaper.ClassicalFourthNat.BPay_9669
  · exact WuPaper.ClassicalFourthNat.BPay_9670
  · exact WuPaper.ClassicalFourthNat.BPay_9671
  · exact WuPaper.ClassicalFourthNat.BPay_9672
  · exact WuPaper.ClassicalFourthNat.BPay_9673
  · exact WuPaper.ClassicalFourthNat.BPay_9674
  · exact WuPaper.ClassicalFourthNat.BPay_9675
  · exact WuPaper.ClassicalFourthNat.BPay_9676
  · exact WuPaper.ClassicalFourthNat.BPay_9677
  · exact WuPaper.ClassicalFourthNat.BPay_9678
  · exact WuPaper.ClassicalFourthNat.BPay_9679
  · exact WuPaper.ClassicalFourthNat.BPay_9680
  · exact WuPaper.ClassicalFourthNat.BPay_9681
  · exact WuPaper.ClassicalFourthNat.BPay_9682
  · exact WuPaper.ClassicalFourthNat.BPay_9683
  · exact WuPaper.ClassicalFourthNat.BPay_9684
  · exact WuPaper.ClassicalFourthNat.BPay_9685
  · exact WuPaper.ClassicalFourthNat.BPay_9686
  · exact WuPaper.ClassicalFourthNat.BPay_9687
  · exact WuPaper.ClassicalFourthNat.BPay_9688
  · exact WuPaper.ClassicalFourthNat.BPay_9689
  · exact WuPaper.ClassicalFourthNat.BPay_9690
  · exact WuPaper.ClassicalFourthNat.BPay_9691
  · exact WuPaper.ClassicalFourthNat.BPay_9692
  · exact WuPaper.ClassicalFourthNat.BPay_9693
  · exact WuPaper.ClassicalFourthNat.BPay_9694
  · exact WuPaper.ClassicalFourthNat.BPay_9695
  · exact WuPaper.ClassicalFourthNat.BPay_9696
  · exact WuPaper.ClassicalFourthNat.BPay_9697
  · exact WuPaper.ClassicalFourthNat.BPay_9698
  · exact WuPaper.ClassicalFourthNat.BPay_9699
  · exact WuPaper.ClassicalFourthNat.BPay_9700
  · exact WuPaper.ClassicalFourthNat.BPay_9701
  · exact WuPaper.ClassicalFourthNat.BPay_9702
  · exact WuPaper.ClassicalFourthNat.BPay_9703
  · exact WuPaper.ClassicalFourthNat.BPay_9704
  · exact WuPaper.ClassicalFourthNat.BPay_9705
  · exact WuPaper.ClassicalFourthNat.BPay_9706
  · exact WuPaper.ClassicalFourthNat.BPay_9707
  · exact WuPaper.ClassicalFourthNat.BPay_9708
  · exact WuPaper.ClassicalFourthNat.BPay_9709
  · exact WuPaper.ClassicalFourthNat.BPay_9710
  · exact WuPaper.ClassicalFourthNat.BPay_9711
  · exact WuPaper.ClassicalFourthNat.BPay_9712
  · exact WuPaper.ClassicalFourthNat.BPay_9713
  · exact WuPaper.ClassicalFourthNat.BPay_9714
  · exact WuPaper.ClassicalFourthNat.BPay_9715
  · exact WuPaper.ClassicalFourthNat.BPay_9716
  · exact WuPaper.ClassicalFourthNat.BPay_9717
  · exact WuPaper.ClassicalFourthNat.BPay_9718
  · exact WuPaper.ClassicalFourthNat.BPay_9719
  · exact WuPaper.ClassicalFourthNat.BPay_9720
  · exact WuPaper.ClassicalFourthNat.BPay_9721
  · exact WuPaper.ClassicalFourthNat.BPay_9722
  · exact WuPaper.ClassicalFourthNat.BPay_9723
  · exact WuPaper.ClassicalFourthNat.BPay_9724
  · exact WuPaper.ClassicalFourthNat.BPay_9725
  · exact WuPaper.ClassicalFourthNat.BPay_9726
  · exact WuPaper.ClassicalFourthNat.BPay_9727
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_151
