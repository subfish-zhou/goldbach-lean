import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay011
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_011 (j : Fin 64) (hj : 64*11+j.val < 10540) :
    BPay (64*11+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_704
  · exact WuPaper.ClassicalFourthNat.BPay_705
  · exact WuPaper.ClassicalFourthNat.BPay_706
  · exact WuPaper.ClassicalFourthNat.BPay_707
  · exact WuPaper.ClassicalFourthNat.BPay_708
  · exact WuPaper.ClassicalFourthNat.BPay_709
  · exact WuPaper.ClassicalFourthNat.BPay_710
  · exact WuPaper.ClassicalFourthNat.BPay_711
  · exact WuPaper.ClassicalFourthNat.BPay_712
  · exact WuPaper.ClassicalFourthNat.BPay_713
  · exact WuPaper.ClassicalFourthNat.BPay_714
  · exact WuPaper.ClassicalFourthNat.BPay_715
  · exact WuPaper.ClassicalFourthNat.BPay_716
  · exact WuPaper.ClassicalFourthNat.BPay_717
  · exact WuPaper.ClassicalFourthNat.BPay_718
  · exact WuPaper.ClassicalFourthNat.BPay_719
  · exact WuPaper.ClassicalFourthNat.BPay_720
  · exact WuPaper.ClassicalFourthNat.BPay_721
  · exact WuPaper.ClassicalFourthNat.BPay_722
  · exact WuPaper.ClassicalFourthNat.BPay_723
  · exact WuPaper.ClassicalFourthNat.BPay_724
  · exact WuPaper.ClassicalFourthNat.BPay_725
  · exact WuPaper.ClassicalFourthNat.BPay_726
  · exact WuPaper.ClassicalFourthNat.BPay_727
  · exact WuPaper.ClassicalFourthNat.BPay_728
  · exact WuPaper.ClassicalFourthNat.BPay_729
  · exact WuPaper.ClassicalFourthNat.BPay_730
  · exact WuPaper.ClassicalFourthNat.BPay_731
  · exact WuPaper.ClassicalFourthNat.BPay_732
  · exact WuPaper.ClassicalFourthNat.BPay_733
  · exact WuPaper.ClassicalFourthNat.BPay_734
  · exact WuPaper.ClassicalFourthNat.BPay_735
  · exact WuPaper.ClassicalFourthNat.BPay_736
  · exact WuPaper.ClassicalFourthNat.BPay_737
  · exact WuPaper.ClassicalFourthNat.BPay_738
  · exact WuPaper.ClassicalFourthNat.BPay_739
  · exact WuPaper.ClassicalFourthNat.BPay_740
  · exact WuPaper.ClassicalFourthNat.BPay_741
  · exact WuPaper.ClassicalFourthNat.BPay_742
  · exact WuPaper.ClassicalFourthNat.BPay_743
  · exact WuPaper.ClassicalFourthNat.BPay_744
  · exact WuPaper.ClassicalFourthNat.BPay_745
  · exact WuPaper.ClassicalFourthNat.BPay_746
  · exact WuPaper.ClassicalFourthNat.BPay_747
  · exact WuPaper.ClassicalFourthNat.BPay_748
  · exact WuPaper.ClassicalFourthNat.BPay_749
  · exact WuPaper.ClassicalFourthNat.BPay_750
  · exact WuPaper.ClassicalFourthNat.BPay_751
  · exact WuPaper.ClassicalFourthNat.BPay_752
  · exact WuPaper.ClassicalFourthNat.BPay_753
  · exact WuPaper.ClassicalFourthNat.BPay_754
  · exact WuPaper.ClassicalFourthNat.BPay_755
  · exact WuPaper.ClassicalFourthNat.BPay_756
  · exact WuPaper.ClassicalFourthNat.BPay_757
  · exact WuPaper.ClassicalFourthNat.BPay_758
  · exact WuPaper.ClassicalFourthNat.BPay_759
  · exact WuPaper.ClassicalFourthNat.BPay_760
  · exact WuPaper.ClassicalFourthNat.BPay_761
  · exact WuPaper.ClassicalFourthNat.BPay_762
  · exact WuPaper.ClassicalFourthNat.BPay_763
  · exact WuPaper.ClassicalFourthNat.BPay_764
  · exact WuPaper.ClassicalFourthNat.BPay_765
  · exact WuPaper.ClassicalFourthNat.BPay_766
  · exact WuPaper.ClassicalFourthNat.BPay_767
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_011
