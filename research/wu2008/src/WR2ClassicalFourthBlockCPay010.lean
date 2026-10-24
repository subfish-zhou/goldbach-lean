import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatCPay010
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem CPay_block_010 (j : Fin 64) (hj : 64*10+j.val < 2540) :
    CPay (64*10+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.CPay_640
  · exact WuPaper.ClassicalFourthNat.CPay_641
  · exact WuPaper.ClassicalFourthNat.CPay_642
  · exact WuPaper.ClassicalFourthNat.CPay_643
  · exact WuPaper.ClassicalFourthNat.CPay_644
  · exact WuPaper.ClassicalFourthNat.CPay_645
  · exact WuPaper.ClassicalFourthNat.CPay_646
  · exact WuPaper.ClassicalFourthNat.CPay_647
  · exact WuPaper.ClassicalFourthNat.CPay_648
  · exact WuPaper.ClassicalFourthNat.CPay_649
  · exact WuPaper.ClassicalFourthNat.CPay_650
  · exact WuPaper.ClassicalFourthNat.CPay_651
  · exact WuPaper.ClassicalFourthNat.CPay_652
  · exact WuPaper.ClassicalFourthNat.CPay_653
  · exact WuPaper.ClassicalFourthNat.CPay_654
  · exact WuPaper.ClassicalFourthNat.CPay_655
  · exact WuPaper.ClassicalFourthNat.CPay_656
  · exact WuPaper.ClassicalFourthNat.CPay_657
  · exact WuPaper.ClassicalFourthNat.CPay_658
  · exact WuPaper.ClassicalFourthNat.CPay_659
  · exact WuPaper.ClassicalFourthNat.CPay_660
  · exact WuPaper.ClassicalFourthNat.CPay_661
  · exact WuPaper.ClassicalFourthNat.CPay_662
  · exact WuPaper.ClassicalFourthNat.CPay_663
  · exact WuPaper.ClassicalFourthNat.CPay_664
  · exact WuPaper.ClassicalFourthNat.CPay_665
  · exact WuPaper.ClassicalFourthNat.CPay_666
  · exact WuPaper.ClassicalFourthNat.CPay_667
  · exact WuPaper.ClassicalFourthNat.CPay_668
  · exact WuPaper.ClassicalFourthNat.CPay_669
  · exact WuPaper.ClassicalFourthNat.CPay_670
  · exact WuPaper.ClassicalFourthNat.CPay_671
  · exact WuPaper.ClassicalFourthNat.CPay_672
  · exact WuPaper.ClassicalFourthNat.CPay_673
  · exact WuPaper.ClassicalFourthNat.CPay_674
  · exact WuPaper.ClassicalFourthNat.CPay_675
  · exact WuPaper.ClassicalFourthNat.CPay_676
  · exact WuPaper.ClassicalFourthNat.CPay_677
  · exact WuPaper.ClassicalFourthNat.CPay_678
  · exact WuPaper.ClassicalFourthNat.CPay_679
  · exact WuPaper.ClassicalFourthNat.CPay_680
  · exact WuPaper.ClassicalFourthNat.CPay_681
  · exact WuPaper.ClassicalFourthNat.CPay_682
  · exact WuPaper.ClassicalFourthNat.CPay_683
  · exact WuPaper.ClassicalFourthNat.CPay_684
  · exact WuPaper.ClassicalFourthNat.CPay_685
  · exact WuPaper.ClassicalFourthNat.CPay_686
  · exact WuPaper.ClassicalFourthNat.CPay_687
  · exact WuPaper.ClassicalFourthNat.CPay_688
  · exact WuPaper.ClassicalFourthNat.CPay_689
  · exact WuPaper.ClassicalFourthNat.CPay_690
  · exact WuPaper.ClassicalFourthNat.CPay_691
  · exact WuPaper.ClassicalFourthNat.CPay_692
  · exact WuPaper.ClassicalFourthNat.CPay_693
  · exact WuPaper.ClassicalFourthNat.CPay_694
  · exact WuPaper.ClassicalFourthNat.CPay_695
  · exact WuPaper.ClassicalFourthNat.CPay_696
  · exact WuPaper.ClassicalFourthNat.CPay_697
  · exact WuPaper.ClassicalFourthNat.CPay_698
  · exact WuPaper.ClassicalFourthNat.CPay_699
  · exact WuPaper.ClassicalFourthNat.CPay_700
  · exact WuPaper.ClassicalFourthNat.CPay_701
  · exact WuPaper.ClassicalFourthNat.CPay_702
  · exact WuPaper.ClassicalFourthNat.CPay_703
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.CPay_block_010
