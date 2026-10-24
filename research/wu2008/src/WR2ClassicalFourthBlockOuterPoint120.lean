import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatOuterPoint120
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem OuterPoint_block_120 (j : Fin 64) (hj : 64*120+j.val < 10541) :
    OuterPoint (64*120+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7680
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7681
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7682
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7683
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7684
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7685
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7686
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7687
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7688
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7689
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7690
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7691
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7692
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7693
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7694
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7695
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7696
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7697
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7698
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7699
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7700
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7701
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7702
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7703
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7704
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7705
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7706
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7707
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7708
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7709
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7710
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7711
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7712
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7713
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7714
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7715
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7716
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7717
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7718
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7719
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7720
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7721
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7722
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7723
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7724
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7725
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7726
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7727
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7728
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7729
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7730
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7731
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7732
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7733
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7734
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7735
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7736
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7737
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7738
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7739
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7740
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7741
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7742
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7743
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.OuterPoint_block_120
