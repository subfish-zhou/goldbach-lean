import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatouterPay011
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem outerPay_block_011 (j : Fin 64) (hj : 64*11+j.val < 10540) :
    OuterPay (64*11+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.outerPay_704
  · exact WuPaper.ClassicalFourthNat.outerPay_705
  · exact WuPaper.ClassicalFourthNat.outerPay_706
  · exact WuPaper.ClassicalFourthNat.outerPay_707
  · exact WuPaper.ClassicalFourthNat.outerPay_708
  · exact WuPaper.ClassicalFourthNat.outerPay_709
  · exact WuPaper.ClassicalFourthNat.outerPay_710
  · exact WuPaper.ClassicalFourthNat.outerPay_711
  · exact WuPaper.ClassicalFourthNat.outerPay_712
  · exact WuPaper.ClassicalFourthNat.outerPay_713
  · exact WuPaper.ClassicalFourthNat.outerPay_714
  · exact WuPaper.ClassicalFourthNat.outerPay_715
  · exact WuPaper.ClassicalFourthNat.outerPay_716
  · exact WuPaper.ClassicalFourthNat.outerPay_717
  · exact WuPaper.ClassicalFourthNat.outerPay_718
  · exact WuPaper.ClassicalFourthNat.outerPay_719
  · exact WuPaper.ClassicalFourthNat.outerPay_720
  · exact WuPaper.ClassicalFourthNat.outerPay_721
  · exact WuPaper.ClassicalFourthNat.outerPay_722
  · exact WuPaper.ClassicalFourthNat.outerPay_723
  · exact WuPaper.ClassicalFourthNat.outerPay_724
  · exact WuPaper.ClassicalFourthNat.outerPay_725
  · exact WuPaper.ClassicalFourthNat.outerPay_726
  · exact WuPaper.ClassicalFourthNat.outerPay_727
  · exact WuPaper.ClassicalFourthNat.outerPay_728
  · exact WuPaper.ClassicalFourthNat.outerPay_729
  · exact WuPaper.ClassicalFourthNat.outerPay_730
  · exact WuPaper.ClassicalFourthNat.outerPay_731
  · exact WuPaper.ClassicalFourthNat.outerPay_732
  · exact WuPaper.ClassicalFourthNat.outerPay_733
  · exact WuPaper.ClassicalFourthNat.outerPay_734
  · exact WuPaper.ClassicalFourthNat.outerPay_735
  · exact WuPaper.ClassicalFourthNat.outerPay_736
  · exact WuPaper.ClassicalFourthNat.outerPay_737
  · exact WuPaper.ClassicalFourthNat.outerPay_738
  · exact WuPaper.ClassicalFourthNat.outerPay_739
  · exact WuPaper.ClassicalFourthNat.outerPay_740
  · exact WuPaper.ClassicalFourthNat.outerPay_741
  · exact WuPaper.ClassicalFourthNat.outerPay_742
  · exact WuPaper.ClassicalFourthNat.outerPay_743
  · exact WuPaper.ClassicalFourthNat.outerPay_744
  · exact WuPaper.ClassicalFourthNat.outerPay_745
  · exact WuPaper.ClassicalFourthNat.outerPay_746
  · exact WuPaper.ClassicalFourthNat.outerPay_747
  · exact WuPaper.ClassicalFourthNat.outerPay_748
  · exact WuPaper.ClassicalFourthNat.outerPay_749
  · exact WuPaper.ClassicalFourthNat.outerPay_750
  · exact WuPaper.ClassicalFourthNat.outerPay_751
  · exact WuPaper.ClassicalFourthNat.outerPay_752
  · exact WuPaper.ClassicalFourthNat.outerPay_753
  · exact WuPaper.ClassicalFourthNat.outerPay_754
  · exact WuPaper.ClassicalFourthNat.outerPay_755
  · exact WuPaper.ClassicalFourthNat.outerPay_756
  · exact WuPaper.ClassicalFourthNat.outerPay_757
  · exact WuPaper.ClassicalFourthNat.outerPay_758
  · exact WuPaper.ClassicalFourthNat.outerPay_759
  · exact WuPaper.ClassicalFourthNat.outerPay_760
  · exact WuPaper.ClassicalFourthNat.outerPay_761
  · exact WuPaper.ClassicalFourthNat.outerPay_762
  · exact WuPaper.ClassicalFourthNat.outerPay_763
  · exact WuPaper.ClassicalFourthNat.outerPay_764
  · exact WuPaper.ClassicalFourthNat.outerPay_765
  · exact WuPaper.ClassicalFourthNat.outerPay_766
  · exact WuPaper.ClassicalFourthNat.outerPay_767
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.outerPay_block_011
