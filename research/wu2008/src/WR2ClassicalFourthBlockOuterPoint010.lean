import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatOuterPoint010
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem OuterPoint_block_010 (j : Fin 64) (hj : 64*10+j.val < 10541) :
    OuterPoint (64*10+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.OuterPoint_640
  · exact WuPaper.ClassicalFourthNat.OuterPoint_641
  · exact WuPaper.ClassicalFourthNat.OuterPoint_642
  · exact WuPaper.ClassicalFourthNat.OuterPoint_643
  · exact WuPaper.ClassicalFourthNat.OuterPoint_644
  · exact WuPaper.ClassicalFourthNat.OuterPoint_645
  · exact WuPaper.ClassicalFourthNat.OuterPoint_646
  · exact WuPaper.ClassicalFourthNat.OuterPoint_647
  · exact WuPaper.ClassicalFourthNat.OuterPoint_648
  · exact WuPaper.ClassicalFourthNat.OuterPoint_649
  · exact WuPaper.ClassicalFourthNat.OuterPoint_650
  · exact WuPaper.ClassicalFourthNat.OuterPoint_651
  · exact WuPaper.ClassicalFourthNat.OuterPoint_652
  · exact WuPaper.ClassicalFourthNat.OuterPoint_653
  · exact WuPaper.ClassicalFourthNat.OuterPoint_654
  · exact WuPaper.ClassicalFourthNat.OuterPoint_655
  · exact WuPaper.ClassicalFourthNat.OuterPoint_656
  · exact WuPaper.ClassicalFourthNat.OuterPoint_657
  · exact WuPaper.ClassicalFourthNat.OuterPoint_658
  · exact WuPaper.ClassicalFourthNat.OuterPoint_659
  · exact WuPaper.ClassicalFourthNat.OuterPoint_660
  · exact WuPaper.ClassicalFourthNat.OuterPoint_661
  · exact WuPaper.ClassicalFourthNat.OuterPoint_662
  · exact WuPaper.ClassicalFourthNat.OuterPoint_663
  · exact WuPaper.ClassicalFourthNat.OuterPoint_664
  · exact WuPaper.ClassicalFourthNat.OuterPoint_665
  · exact WuPaper.ClassicalFourthNat.OuterPoint_666
  · exact WuPaper.ClassicalFourthNat.OuterPoint_667
  · exact WuPaper.ClassicalFourthNat.OuterPoint_668
  · exact WuPaper.ClassicalFourthNat.OuterPoint_669
  · exact WuPaper.ClassicalFourthNat.OuterPoint_670
  · exact WuPaper.ClassicalFourthNat.OuterPoint_671
  · exact WuPaper.ClassicalFourthNat.OuterPoint_672
  · exact WuPaper.ClassicalFourthNat.OuterPoint_673
  · exact WuPaper.ClassicalFourthNat.OuterPoint_674
  · exact WuPaper.ClassicalFourthNat.OuterPoint_675
  · exact WuPaper.ClassicalFourthNat.OuterPoint_676
  · exact WuPaper.ClassicalFourthNat.OuterPoint_677
  · exact WuPaper.ClassicalFourthNat.OuterPoint_678
  · exact WuPaper.ClassicalFourthNat.OuterPoint_679
  · exact WuPaper.ClassicalFourthNat.OuterPoint_680
  · exact WuPaper.ClassicalFourthNat.OuterPoint_681
  · exact WuPaper.ClassicalFourthNat.OuterPoint_682
  · exact WuPaper.ClassicalFourthNat.OuterPoint_683
  · exact WuPaper.ClassicalFourthNat.OuterPoint_684
  · exact WuPaper.ClassicalFourthNat.OuterPoint_685
  · exact WuPaper.ClassicalFourthNat.OuterPoint_686
  · exact WuPaper.ClassicalFourthNat.OuterPoint_687
  · exact WuPaper.ClassicalFourthNat.OuterPoint_688
  · exact WuPaper.ClassicalFourthNat.OuterPoint_689
  · exact WuPaper.ClassicalFourthNat.OuterPoint_690
  · exact WuPaper.ClassicalFourthNat.OuterPoint_691
  · exact WuPaper.ClassicalFourthNat.OuterPoint_692
  · exact WuPaper.ClassicalFourthNat.OuterPoint_693
  · exact WuPaper.ClassicalFourthNat.OuterPoint_694
  · exact WuPaper.ClassicalFourthNat.OuterPoint_695
  · exact WuPaper.ClassicalFourthNat.OuterPoint_696
  · exact WuPaper.ClassicalFourthNat.OuterPoint_697
  · exact WuPaper.ClassicalFourthNat.OuterPoint_698
  · exact WuPaper.ClassicalFourthNat.OuterPoint_699
  · exact WuPaper.ClassicalFourthNat.OuterPoint_700
  · exact WuPaper.ClassicalFourthNat.OuterPoint_701
  · exact WuPaper.ClassicalFourthNat.OuterPoint_702
  · exact WuPaper.ClassicalFourthNat.OuterPoint_703
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.OuterPoint_block_010
