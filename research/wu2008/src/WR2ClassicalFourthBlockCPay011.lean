import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatCPay011
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem CPay_block_011 (j : Fin 64) (hj : 64*11+j.val < 2540) :
    CPay (64*11+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.CPay_704
  · exact WuPaper.ClassicalFourthNat.CPay_705
  · exact WuPaper.ClassicalFourthNat.CPay_706
  · exact WuPaper.ClassicalFourthNat.CPay_707
  · exact WuPaper.ClassicalFourthNat.CPay_708
  · exact WuPaper.ClassicalFourthNat.CPay_709
  · exact WuPaper.ClassicalFourthNat.CPay_710
  · exact WuPaper.ClassicalFourthNat.CPay_711
  · exact WuPaper.ClassicalFourthNat.CPay_712
  · exact WuPaper.ClassicalFourthNat.CPay_713
  · exact WuPaper.ClassicalFourthNat.CPay_714
  · exact WuPaper.ClassicalFourthNat.CPay_715
  · exact WuPaper.ClassicalFourthNat.CPay_716
  · exact WuPaper.ClassicalFourthNat.CPay_717
  · exact WuPaper.ClassicalFourthNat.CPay_718
  · exact WuPaper.ClassicalFourthNat.CPay_719
  · exact WuPaper.ClassicalFourthNat.CPay_720
  · exact WuPaper.ClassicalFourthNat.CPay_721
  · exact WuPaper.ClassicalFourthNat.CPay_722
  · exact WuPaper.ClassicalFourthNat.CPay_723
  · exact WuPaper.ClassicalFourthNat.CPay_724
  · exact WuPaper.ClassicalFourthNat.CPay_725
  · exact WuPaper.ClassicalFourthNat.CPay_726
  · exact WuPaper.ClassicalFourthNat.CPay_727
  · exact WuPaper.ClassicalFourthNat.CPay_728
  · exact WuPaper.ClassicalFourthNat.CPay_729
  · exact WuPaper.ClassicalFourthNat.CPay_730
  · exact WuPaper.ClassicalFourthNat.CPay_731
  · exact WuPaper.ClassicalFourthNat.CPay_732
  · exact WuPaper.ClassicalFourthNat.CPay_733
  · exact WuPaper.ClassicalFourthNat.CPay_734
  · exact WuPaper.ClassicalFourthNat.CPay_735
  · exact WuPaper.ClassicalFourthNat.CPay_736
  · exact WuPaper.ClassicalFourthNat.CPay_737
  · exact WuPaper.ClassicalFourthNat.CPay_738
  · exact WuPaper.ClassicalFourthNat.CPay_739
  · exact WuPaper.ClassicalFourthNat.CPay_740
  · exact WuPaper.ClassicalFourthNat.CPay_741
  · exact WuPaper.ClassicalFourthNat.CPay_742
  · exact WuPaper.ClassicalFourthNat.CPay_743
  · exact WuPaper.ClassicalFourthNat.CPay_744
  · exact WuPaper.ClassicalFourthNat.CPay_745
  · exact WuPaper.ClassicalFourthNat.CPay_746
  · exact WuPaper.ClassicalFourthNat.CPay_747
  · exact WuPaper.ClassicalFourthNat.CPay_748
  · exact WuPaper.ClassicalFourthNat.CPay_749
  · exact WuPaper.ClassicalFourthNat.CPay_750
  · exact WuPaper.ClassicalFourthNat.CPay_751
  · exact WuPaper.ClassicalFourthNat.CPay_752
  · exact WuPaper.ClassicalFourthNat.CPay_753
  · exact WuPaper.ClassicalFourthNat.CPay_754
  · exact WuPaper.ClassicalFourthNat.CPay_755
  · exact WuPaper.ClassicalFourthNat.CPay_756
  · exact WuPaper.ClassicalFourthNat.CPay_757
  · exact WuPaper.ClassicalFourthNat.CPay_758
  · exact WuPaper.ClassicalFourthNat.CPay_759
  · exact WuPaper.ClassicalFourthNat.CPay_760
  · exact WuPaper.ClassicalFourthNat.CPay_761
  · exact WuPaper.ClassicalFourthNat.CPay_762
  · exact WuPaper.ClassicalFourthNat.CPay_763
  · exact WuPaper.ClassicalFourthNat.CPay_764
  · exact WuPaper.ClassicalFourthNat.CPay_765
  · exact WuPaper.ClassicalFourthNat.CPay_766
  · exact WuPaper.ClassicalFourthNat.CPay_767
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.CPay_block_011
