import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatouterPay010
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem outerPay_block_010 (j : Fin 64) (hj : 64*10+j.val < 10540) :
    OuterPay (64*10+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.outerPay_640
  · exact WuPaper.ClassicalFourthNat.outerPay_641
  · exact WuPaper.ClassicalFourthNat.outerPay_642
  · exact WuPaper.ClassicalFourthNat.outerPay_643
  · exact WuPaper.ClassicalFourthNat.outerPay_644
  · exact WuPaper.ClassicalFourthNat.outerPay_645
  · exact WuPaper.ClassicalFourthNat.outerPay_646
  · exact WuPaper.ClassicalFourthNat.outerPay_647
  · exact WuPaper.ClassicalFourthNat.outerPay_648
  · exact WuPaper.ClassicalFourthNat.outerPay_649
  · exact WuPaper.ClassicalFourthNat.outerPay_650
  · exact WuPaper.ClassicalFourthNat.outerPay_651
  · exact WuPaper.ClassicalFourthNat.outerPay_652
  · exact WuPaper.ClassicalFourthNat.outerPay_653
  · exact WuPaper.ClassicalFourthNat.outerPay_654
  · exact WuPaper.ClassicalFourthNat.outerPay_655
  · exact WuPaper.ClassicalFourthNat.outerPay_656
  · exact WuPaper.ClassicalFourthNat.outerPay_657
  · exact WuPaper.ClassicalFourthNat.outerPay_658
  · exact WuPaper.ClassicalFourthNat.outerPay_659
  · exact WuPaper.ClassicalFourthNat.outerPay_660
  · exact WuPaper.ClassicalFourthNat.outerPay_661
  · exact WuPaper.ClassicalFourthNat.outerPay_662
  · exact WuPaper.ClassicalFourthNat.outerPay_663
  · exact WuPaper.ClassicalFourthNat.outerPay_664
  · exact WuPaper.ClassicalFourthNat.outerPay_665
  · exact WuPaper.ClassicalFourthNat.outerPay_666
  · exact WuPaper.ClassicalFourthNat.outerPay_667
  · exact WuPaper.ClassicalFourthNat.outerPay_668
  · exact WuPaper.ClassicalFourthNat.outerPay_669
  · exact WuPaper.ClassicalFourthNat.outerPay_670
  · exact WuPaper.ClassicalFourthNat.outerPay_671
  · exact WuPaper.ClassicalFourthNat.outerPay_672
  · exact WuPaper.ClassicalFourthNat.outerPay_673
  · exact WuPaper.ClassicalFourthNat.outerPay_674
  · exact WuPaper.ClassicalFourthNat.outerPay_675
  · exact WuPaper.ClassicalFourthNat.outerPay_676
  · exact WuPaper.ClassicalFourthNat.outerPay_677
  · exact WuPaper.ClassicalFourthNat.outerPay_678
  · exact WuPaper.ClassicalFourthNat.outerPay_679
  · exact WuPaper.ClassicalFourthNat.outerPay_680
  · exact WuPaper.ClassicalFourthNat.outerPay_681
  · exact WuPaper.ClassicalFourthNat.outerPay_682
  · exact WuPaper.ClassicalFourthNat.outerPay_683
  · exact WuPaper.ClassicalFourthNat.outerPay_684
  · exact WuPaper.ClassicalFourthNat.outerPay_685
  · exact WuPaper.ClassicalFourthNat.outerPay_686
  · exact WuPaper.ClassicalFourthNat.outerPay_687
  · exact WuPaper.ClassicalFourthNat.outerPay_688
  · exact WuPaper.ClassicalFourthNat.outerPay_689
  · exact WuPaper.ClassicalFourthNat.outerPay_690
  · exact WuPaper.ClassicalFourthNat.outerPay_691
  · exact WuPaper.ClassicalFourthNat.outerPay_692
  · exact WuPaper.ClassicalFourthNat.outerPay_693
  · exact WuPaper.ClassicalFourthNat.outerPay_694
  · exact WuPaper.ClassicalFourthNat.outerPay_695
  · exact WuPaper.ClassicalFourthNat.outerPay_696
  · exact WuPaper.ClassicalFourthNat.outerPay_697
  · exact WuPaper.ClassicalFourthNat.outerPay_698
  · exact WuPaper.ClassicalFourthNat.outerPay_699
  · exact WuPaper.ClassicalFourthNat.outerPay_700
  · exact WuPaper.ClassicalFourthNat.outerPay_701
  · exact WuPaper.ClassicalFourthNat.outerPay_702
  · exact WuPaper.ClassicalFourthNat.outerPay_703
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.outerPay_block_010
