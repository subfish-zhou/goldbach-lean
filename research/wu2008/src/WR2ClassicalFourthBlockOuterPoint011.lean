import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatOuterPoint011
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem OuterPoint_block_011 (j : Fin 64) (hj : 64*11+j.val < 10541) :
    OuterPoint (64*11+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.OuterPoint_704
  · exact WuPaper.ClassicalFourthNat.OuterPoint_705
  · exact WuPaper.ClassicalFourthNat.OuterPoint_706
  · exact WuPaper.ClassicalFourthNat.OuterPoint_707
  · exact WuPaper.ClassicalFourthNat.OuterPoint_708
  · exact WuPaper.ClassicalFourthNat.OuterPoint_709
  · exact WuPaper.ClassicalFourthNat.OuterPoint_710
  · exact WuPaper.ClassicalFourthNat.OuterPoint_711
  · exact WuPaper.ClassicalFourthNat.OuterPoint_712
  · exact WuPaper.ClassicalFourthNat.OuterPoint_713
  · exact WuPaper.ClassicalFourthNat.OuterPoint_714
  · exact WuPaper.ClassicalFourthNat.OuterPoint_715
  · exact WuPaper.ClassicalFourthNat.OuterPoint_716
  · exact WuPaper.ClassicalFourthNat.OuterPoint_717
  · exact WuPaper.ClassicalFourthNat.OuterPoint_718
  · exact WuPaper.ClassicalFourthNat.OuterPoint_719
  · exact WuPaper.ClassicalFourthNat.OuterPoint_720
  · exact WuPaper.ClassicalFourthNat.OuterPoint_721
  · exact WuPaper.ClassicalFourthNat.OuterPoint_722
  · exact WuPaper.ClassicalFourthNat.OuterPoint_723
  · exact WuPaper.ClassicalFourthNat.OuterPoint_724
  · exact WuPaper.ClassicalFourthNat.OuterPoint_725
  · exact WuPaper.ClassicalFourthNat.OuterPoint_726
  · exact WuPaper.ClassicalFourthNat.OuterPoint_727
  · exact WuPaper.ClassicalFourthNat.OuterPoint_728
  · exact WuPaper.ClassicalFourthNat.OuterPoint_729
  · exact WuPaper.ClassicalFourthNat.OuterPoint_730
  · exact WuPaper.ClassicalFourthNat.OuterPoint_731
  · exact WuPaper.ClassicalFourthNat.OuterPoint_732
  · exact WuPaper.ClassicalFourthNat.OuterPoint_733
  · exact WuPaper.ClassicalFourthNat.OuterPoint_734
  · exact WuPaper.ClassicalFourthNat.OuterPoint_735
  · exact WuPaper.ClassicalFourthNat.OuterPoint_736
  · exact WuPaper.ClassicalFourthNat.OuterPoint_737
  · exact WuPaper.ClassicalFourthNat.OuterPoint_738
  · exact WuPaper.ClassicalFourthNat.OuterPoint_739
  · exact WuPaper.ClassicalFourthNat.OuterPoint_740
  · exact WuPaper.ClassicalFourthNat.OuterPoint_741
  · exact WuPaper.ClassicalFourthNat.OuterPoint_742
  · exact WuPaper.ClassicalFourthNat.OuterPoint_743
  · exact WuPaper.ClassicalFourthNat.OuterPoint_744
  · exact WuPaper.ClassicalFourthNat.OuterPoint_745
  · exact WuPaper.ClassicalFourthNat.OuterPoint_746
  · exact WuPaper.ClassicalFourthNat.OuterPoint_747
  · exact WuPaper.ClassicalFourthNat.OuterPoint_748
  · exact WuPaper.ClassicalFourthNat.OuterPoint_749
  · exact WuPaper.ClassicalFourthNat.OuterPoint_750
  · exact WuPaper.ClassicalFourthNat.OuterPoint_751
  · exact WuPaper.ClassicalFourthNat.OuterPoint_752
  · exact WuPaper.ClassicalFourthNat.OuterPoint_753
  · exact WuPaper.ClassicalFourthNat.OuterPoint_754
  · exact WuPaper.ClassicalFourthNat.OuterPoint_755
  · exact WuPaper.ClassicalFourthNat.OuterPoint_756
  · exact WuPaper.ClassicalFourthNat.OuterPoint_757
  · exact WuPaper.ClassicalFourthNat.OuterPoint_758
  · exact WuPaper.ClassicalFourthNat.OuterPoint_759
  · exact WuPaper.ClassicalFourthNat.OuterPoint_760
  · exact WuPaper.ClassicalFourthNat.OuterPoint_761
  · exact WuPaper.ClassicalFourthNat.OuterPoint_762
  · exact WuPaper.ClassicalFourthNat.OuterPoint_763
  · exact WuPaper.ClassicalFourthNat.OuterPoint_764
  · exact WuPaper.ClassicalFourthNat.OuterPoint_765
  · exact WuPaper.ClassicalFourthNat.OuterPoint_766
  · exact WuPaper.ClassicalFourthNat.OuterPoint_767
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.OuterPoint_block_011
