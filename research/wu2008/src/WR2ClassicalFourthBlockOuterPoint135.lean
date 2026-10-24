import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatOuterPoint135
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem OuterPoint_block_135 (j : Fin 64) (hj : 64*135+j.val < 10541) :
    OuterPoint (64*135+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8640
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8641
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8642
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8643
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8644
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8645
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8646
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8647
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8648
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8649
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8650
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8651
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8652
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8653
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8654
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8655
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8656
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8657
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8658
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8659
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8660
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8661
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8662
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8663
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8664
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8665
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8666
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8667
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8668
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8669
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8670
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8671
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8672
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8673
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8674
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8675
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8676
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8677
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8678
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8679
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8680
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8681
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8682
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8683
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8684
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8685
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8686
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8687
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8688
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8689
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8690
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8691
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8692
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8693
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8694
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8695
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8696
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8697
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8698
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8699
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8700
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8701
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8702
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8703
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.OuterPoint_block_135
