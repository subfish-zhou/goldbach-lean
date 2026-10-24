import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay010
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_010 (j : Fin 64) (hj : 64*10+j.val < 10540) :
    BPay (64*10+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_640
  · exact WuPaper.ClassicalFourthNat.BPay_641
  · exact WuPaper.ClassicalFourthNat.BPay_642
  · exact WuPaper.ClassicalFourthNat.BPay_643
  · exact WuPaper.ClassicalFourthNat.BPay_644
  · exact WuPaper.ClassicalFourthNat.BPay_645
  · exact WuPaper.ClassicalFourthNat.BPay_646
  · exact WuPaper.ClassicalFourthNat.BPay_647
  · exact WuPaper.ClassicalFourthNat.BPay_648
  · exact WuPaper.ClassicalFourthNat.BPay_649
  · exact WuPaper.ClassicalFourthNat.BPay_650
  · exact WuPaper.ClassicalFourthNat.BPay_651
  · exact WuPaper.ClassicalFourthNat.BPay_652
  · exact WuPaper.ClassicalFourthNat.BPay_653
  · exact WuPaper.ClassicalFourthNat.BPay_654
  · exact WuPaper.ClassicalFourthNat.BPay_655
  · exact WuPaper.ClassicalFourthNat.BPay_656
  · exact WuPaper.ClassicalFourthNat.BPay_657
  · exact WuPaper.ClassicalFourthNat.BPay_658
  · exact WuPaper.ClassicalFourthNat.BPay_659
  · exact WuPaper.ClassicalFourthNat.BPay_660
  · exact WuPaper.ClassicalFourthNat.BPay_661
  · exact WuPaper.ClassicalFourthNat.BPay_662
  · exact WuPaper.ClassicalFourthNat.BPay_663
  · exact WuPaper.ClassicalFourthNat.BPay_664
  · exact WuPaper.ClassicalFourthNat.BPay_665
  · exact WuPaper.ClassicalFourthNat.BPay_666
  · exact WuPaper.ClassicalFourthNat.BPay_667
  · exact WuPaper.ClassicalFourthNat.BPay_668
  · exact WuPaper.ClassicalFourthNat.BPay_669
  · exact WuPaper.ClassicalFourthNat.BPay_670
  · exact WuPaper.ClassicalFourthNat.BPay_671
  · exact WuPaper.ClassicalFourthNat.BPay_672
  · exact WuPaper.ClassicalFourthNat.BPay_673
  · exact WuPaper.ClassicalFourthNat.BPay_674
  · exact WuPaper.ClassicalFourthNat.BPay_675
  · exact WuPaper.ClassicalFourthNat.BPay_676
  · exact WuPaper.ClassicalFourthNat.BPay_677
  · exact WuPaper.ClassicalFourthNat.BPay_678
  · exact WuPaper.ClassicalFourthNat.BPay_679
  · exact WuPaper.ClassicalFourthNat.BPay_680
  · exact WuPaper.ClassicalFourthNat.BPay_681
  · exact WuPaper.ClassicalFourthNat.BPay_682
  · exact WuPaper.ClassicalFourthNat.BPay_683
  · exact WuPaper.ClassicalFourthNat.BPay_684
  · exact WuPaper.ClassicalFourthNat.BPay_685
  · exact WuPaper.ClassicalFourthNat.BPay_686
  · exact WuPaper.ClassicalFourthNat.BPay_687
  · exact WuPaper.ClassicalFourthNat.BPay_688
  · exact WuPaper.ClassicalFourthNat.BPay_689
  · exact WuPaper.ClassicalFourthNat.BPay_690
  · exact WuPaper.ClassicalFourthNat.BPay_691
  · exact WuPaper.ClassicalFourthNat.BPay_692
  · exact WuPaper.ClassicalFourthNat.BPay_693
  · exact WuPaper.ClassicalFourthNat.BPay_694
  · exact WuPaper.ClassicalFourthNat.BPay_695
  · exact WuPaper.ClassicalFourthNat.BPay_696
  · exact WuPaper.ClassicalFourthNat.BPay_697
  · exact WuPaper.ClassicalFourthNat.BPay_698
  · exact WuPaper.ClassicalFourthNat.BPay_699
  · exact WuPaper.ClassicalFourthNat.BPay_700
  · exact WuPaper.ClassicalFourthNat.BPay_701
  · exact WuPaper.ClassicalFourthNat.BPay_702
  · exact WuPaper.ClassicalFourthNat.BPay_703
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_010
