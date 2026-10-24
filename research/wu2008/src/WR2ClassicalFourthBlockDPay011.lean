import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatDPay011
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem DPay_block_011 (j : Fin 64) (hj : 64*11+j.val < 2540) :
    DPay (64*11+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.DPay_704
  · exact WuPaper.ClassicalFourthNat.DPay_705
  · exact WuPaper.ClassicalFourthNat.DPay_706
  · exact WuPaper.ClassicalFourthNat.DPay_707
  · exact WuPaper.ClassicalFourthNat.DPay_708
  · exact WuPaper.ClassicalFourthNat.DPay_709
  · exact WuPaper.ClassicalFourthNat.DPay_710
  · exact WuPaper.ClassicalFourthNat.DPay_711
  · exact WuPaper.ClassicalFourthNat.DPay_712
  · exact WuPaper.ClassicalFourthNat.DPay_713
  · exact WuPaper.ClassicalFourthNat.DPay_714
  · exact WuPaper.ClassicalFourthNat.DPay_715
  · exact WuPaper.ClassicalFourthNat.DPay_716
  · exact WuPaper.ClassicalFourthNat.DPay_717
  · exact WuPaper.ClassicalFourthNat.DPay_718
  · exact WuPaper.ClassicalFourthNat.DPay_719
  · exact WuPaper.ClassicalFourthNat.DPay_720
  · exact WuPaper.ClassicalFourthNat.DPay_721
  · exact WuPaper.ClassicalFourthNat.DPay_722
  · exact WuPaper.ClassicalFourthNat.DPay_723
  · exact WuPaper.ClassicalFourthNat.DPay_724
  · exact WuPaper.ClassicalFourthNat.DPay_725
  · exact WuPaper.ClassicalFourthNat.DPay_726
  · exact WuPaper.ClassicalFourthNat.DPay_727
  · exact WuPaper.ClassicalFourthNat.DPay_728
  · exact WuPaper.ClassicalFourthNat.DPay_729
  · exact WuPaper.ClassicalFourthNat.DPay_730
  · exact WuPaper.ClassicalFourthNat.DPay_731
  · exact WuPaper.ClassicalFourthNat.DPay_732
  · exact WuPaper.ClassicalFourthNat.DPay_733
  · exact WuPaper.ClassicalFourthNat.DPay_734
  · exact WuPaper.ClassicalFourthNat.DPay_735
  · exact WuPaper.ClassicalFourthNat.DPay_736
  · exact WuPaper.ClassicalFourthNat.DPay_737
  · exact WuPaper.ClassicalFourthNat.DPay_738
  · exact WuPaper.ClassicalFourthNat.DPay_739
  · exact WuPaper.ClassicalFourthNat.DPay_740
  · exact WuPaper.ClassicalFourthNat.DPay_741
  · exact WuPaper.ClassicalFourthNat.DPay_742
  · exact WuPaper.ClassicalFourthNat.DPay_743
  · exact WuPaper.ClassicalFourthNat.DPay_744
  · exact WuPaper.ClassicalFourthNat.DPay_745
  · exact WuPaper.ClassicalFourthNat.DPay_746
  · exact WuPaper.ClassicalFourthNat.DPay_747
  · exact WuPaper.ClassicalFourthNat.DPay_748
  · exact WuPaper.ClassicalFourthNat.DPay_749
  · exact WuPaper.ClassicalFourthNat.DPay_750
  · exact WuPaper.ClassicalFourthNat.DPay_751
  · exact WuPaper.ClassicalFourthNat.DPay_752
  · exact WuPaper.ClassicalFourthNat.DPay_753
  · exact WuPaper.ClassicalFourthNat.DPay_754
  · exact WuPaper.ClassicalFourthNat.DPay_755
  · exact WuPaper.ClassicalFourthNat.DPay_756
  · exact WuPaper.ClassicalFourthNat.DPay_757
  · exact WuPaper.ClassicalFourthNat.DPay_758
  · exact WuPaper.ClassicalFourthNat.DPay_759
  · exact WuPaper.ClassicalFourthNat.DPay_760
  · exact WuPaper.ClassicalFourthNat.DPay_761
  · exact WuPaper.ClassicalFourthNat.DPay_762
  · exact WuPaper.ClassicalFourthNat.DPay_763
  · exact WuPaper.ClassicalFourthNat.DPay_764
  · exact WuPaper.ClassicalFourthNat.DPay_765
  · exact WuPaper.ClassicalFourthNat.DPay_766
  · exact WuPaper.ClassicalFourthNat.DPay_767
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.DPay_block_011
