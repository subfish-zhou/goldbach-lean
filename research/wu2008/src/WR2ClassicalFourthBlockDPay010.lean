import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatDPay010
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem DPay_block_010 (j : Fin 64) (hj : 64*10+j.val < 2540) :
    DPay (64*10+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.DPay_640
  · exact WuPaper.ClassicalFourthNat.DPay_641
  · exact WuPaper.ClassicalFourthNat.DPay_642
  · exact WuPaper.ClassicalFourthNat.DPay_643
  · exact WuPaper.ClassicalFourthNat.DPay_644
  · exact WuPaper.ClassicalFourthNat.DPay_645
  · exact WuPaper.ClassicalFourthNat.DPay_646
  · exact WuPaper.ClassicalFourthNat.DPay_647
  · exact WuPaper.ClassicalFourthNat.DPay_648
  · exact WuPaper.ClassicalFourthNat.DPay_649
  · exact WuPaper.ClassicalFourthNat.DPay_650
  · exact WuPaper.ClassicalFourthNat.DPay_651
  · exact WuPaper.ClassicalFourthNat.DPay_652
  · exact WuPaper.ClassicalFourthNat.DPay_653
  · exact WuPaper.ClassicalFourthNat.DPay_654
  · exact WuPaper.ClassicalFourthNat.DPay_655
  · exact WuPaper.ClassicalFourthNat.DPay_656
  · exact WuPaper.ClassicalFourthNat.DPay_657
  · exact WuPaper.ClassicalFourthNat.DPay_658
  · exact WuPaper.ClassicalFourthNat.DPay_659
  · exact WuPaper.ClassicalFourthNat.DPay_660
  · exact WuPaper.ClassicalFourthNat.DPay_661
  · exact WuPaper.ClassicalFourthNat.DPay_662
  · exact WuPaper.ClassicalFourthNat.DPay_663
  · exact WuPaper.ClassicalFourthNat.DPay_664
  · exact WuPaper.ClassicalFourthNat.DPay_665
  · exact WuPaper.ClassicalFourthNat.DPay_666
  · exact WuPaper.ClassicalFourthNat.DPay_667
  · exact WuPaper.ClassicalFourthNat.DPay_668
  · exact WuPaper.ClassicalFourthNat.DPay_669
  · exact WuPaper.ClassicalFourthNat.DPay_670
  · exact WuPaper.ClassicalFourthNat.DPay_671
  · exact WuPaper.ClassicalFourthNat.DPay_672
  · exact WuPaper.ClassicalFourthNat.DPay_673
  · exact WuPaper.ClassicalFourthNat.DPay_674
  · exact WuPaper.ClassicalFourthNat.DPay_675
  · exact WuPaper.ClassicalFourthNat.DPay_676
  · exact WuPaper.ClassicalFourthNat.DPay_677
  · exact WuPaper.ClassicalFourthNat.DPay_678
  · exact WuPaper.ClassicalFourthNat.DPay_679
  · exact WuPaper.ClassicalFourthNat.DPay_680
  · exact WuPaper.ClassicalFourthNat.DPay_681
  · exact WuPaper.ClassicalFourthNat.DPay_682
  · exact WuPaper.ClassicalFourthNat.DPay_683
  · exact WuPaper.ClassicalFourthNat.DPay_684
  · exact WuPaper.ClassicalFourthNat.DPay_685
  · exact WuPaper.ClassicalFourthNat.DPay_686
  · exact WuPaper.ClassicalFourthNat.DPay_687
  · exact WuPaper.ClassicalFourthNat.DPay_688
  · exact WuPaper.ClassicalFourthNat.DPay_689
  · exact WuPaper.ClassicalFourthNat.DPay_690
  · exact WuPaper.ClassicalFourthNat.DPay_691
  · exact WuPaper.ClassicalFourthNat.DPay_692
  · exact WuPaper.ClassicalFourthNat.DPay_693
  · exact WuPaper.ClassicalFourthNat.DPay_694
  · exact WuPaper.ClassicalFourthNat.DPay_695
  · exact WuPaper.ClassicalFourthNat.DPay_696
  · exact WuPaper.ClassicalFourthNat.DPay_697
  · exact WuPaper.ClassicalFourthNat.DPay_698
  · exact WuPaper.ClassicalFourthNat.DPay_699
  · exact WuPaper.ClassicalFourthNat.DPay_700
  · exact WuPaper.ClassicalFourthNat.DPay_701
  · exact WuPaper.ClassicalFourthNat.DPay_702
  · exact WuPaper.ClassicalFourthNat.DPay_703
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.DPay_block_010
