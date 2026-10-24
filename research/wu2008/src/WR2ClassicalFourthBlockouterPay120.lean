import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatouterPay120
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem outerPay_block_120 (j : Fin 64) (hj : 64*120+j.val < 10540) :
    OuterPay (64*120+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.outerPay_7680
  · exact WuPaper.ClassicalFourthNat.outerPay_7681
  · exact WuPaper.ClassicalFourthNat.outerPay_7682
  · exact WuPaper.ClassicalFourthNat.outerPay_7683
  · exact WuPaper.ClassicalFourthNat.outerPay_7684
  · exact WuPaper.ClassicalFourthNat.outerPay_7685
  · exact WuPaper.ClassicalFourthNat.outerPay_7686
  · exact WuPaper.ClassicalFourthNat.outerPay_7687
  · exact WuPaper.ClassicalFourthNat.outerPay_7688
  · exact WuPaper.ClassicalFourthNat.outerPay_7689
  · exact WuPaper.ClassicalFourthNat.outerPay_7690
  · exact WuPaper.ClassicalFourthNat.outerPay_7691
  · exact WuPaper.ClassicalFourthNat.outerPay_7692
  · exact WuPaper.ClassicalFourthNat.outerPay_7693
  · exact WuPaper.ClassicalFourthNat.outerPay_7694
  · exact WuPaper.ClassicalFourthNat.outerPay_7695
  · exact WuPaper.ClassicalFourthNat.outerPay_7696
  · exact WuPaper.ClassicalFourthNat.outerPay_7697
  · exact WuPaper.ClassicalFourthNat.outerPay_7698
  · exact WuPaper.ClassicalFourthNat.outerPay_7699
  · exact WuPaper.ClassicalFourthNat.outerPay_7700
  · exact WuPaper.ClassicalFourthNat.outerPay_7701
  · exact WuPaper.ClassicalFourthNat.outerPay_7702
  · exact WuPaper.ClassicalFourthNat.outerPay_7703
  · exact WuPaper.ClassicalFourthNat.outerPay_7704
  · exact WuPaper.ClassicalFourthNat.outerPay_7705
  · exact WuPaper.ClassicalFourthNat.outerPay_7706
  · exact WuPaper.ClassicalFourthNat.outerPay_7707
  · exact WuPaper.ClassicalFourthNat.outerPay_7708
  · exact WuPaper.ClassicalFourthNat.outerPay_7709
  · exact WuPaper.ClassicalFourthNat.outerPay_7710
  · exact WuPaper.ClassicalFourthNat.outerPay_7711
  · exact WuPaper.ClassicalFourthNat.outerPay_7712
  · exact WuPaper.ClassicalFourthNat.outerPay_7713
  · exact WuPaper.ClassicalFourthNat.outerPay_7714
  · exact WuPaper.ClassicalFourthNat.outerPay_7715
  · exact WuPaper.ClassicalFourthNat.outerPay_7716
  · exact WuPaper.ClassicalFourthNat.outerPay_7717
  · exact WuPaper.ClassicalFourthNat.outerPay_7718
  · exact WuPaper.ClassicalFourthNat.outerPay_7719
  · exact WuPaper.ClassicalFourthNat.outerPay_7720
  · exact WuPaper.ClassicalFourthNat.outerPay_7721
  · exact WuPaper.ClassicalFourthNat.outerPay_7722
  · exact WuPaper.ClassicalFourthNat.outerPay_7723
  · exact WuPaper.ClassicalFourthNat.outerPay_7724
  · exact WuPaper.ClassicalFourthNat.outerPay_7725
  · exact WuPaper.ClassicalFourthNat.outerPay_7726
  · exact WuPaper.ClassicalFourthNat.outerPay_7727
  · exact WuPaper.ClassicalFourthNat.outerPay_7728
  · exact WuPaper.ClassicalFourthNat.outerPay_7729
  · exact WuPaper.ClassicalFourthNat.outerPay_7730
  · exact WuPaper.ClassicalFourthNat.outerPay_7731
  · exact WuPaper.ClassicalFourthNat.outerPay_7732
  · exact WuPaper.ClassicalFourthNat.outerPay_7733
  · exact WuPaper.ClassicalFourthNat.outerPay_7734
  · exact WuPaper.ClassicalFourthNat.outerPay_7735
  · exact WuPaper.ClassicalFourthNat.outerPay_7736
  · exact WuPaper.ClassicalFourthNat.outerPay_7737
  · exact WuPaper.ClassicalFourthNat.outerPay_7738
  · exact WuPaper.ClassicalFourthNat.outerPay_7739
  · exact WuPaper.ClassicalFourthNat.outerPay_7740
  · exact WuPaper.ClassicalFourthNat.outerPay_7741
  · exact WuPaper.ClassicalFourthNat.outerPay_7742
  · exact WuPaper.ClassicalFourthNat.outerPay_7743
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.outerPay_block_120
