import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay120
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_120 (j : Fin 64) (hj : 64*120+j.val < 10540) :
    BPay (64*120+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_7680
  · exact WuPaper.ClassicalFourthNat.BPay_7681
  · exact WuPaper.ClassicalFourthNat.BPay_7682
  · exact WuPaper.ClassicalFourthNat.BPay_7683
  · exact WuPaper.ClassicalFourthNat.BPay_7684
  · exact WuPaper.ClassicalFourthNat.BPay_7685
  · exact WuPaper.ClassicalFourthNat.BPay_7686
  · exact WuPaper.ClassicalFourthNat.BPay_7687
  · exact WuPaper.ClassicalFourthNat.BPay_7688
  · exact WuPaper.ClassicalFourthNat.BPay_7689
  · exact WuPaper.ClassicalFourthNat.BPay_7690
  · exact WuPaper.ClassicalFourthNat.BPay_7691
  · exact WuPaper.ClassicalFourthNat.BPay_7692
  · exact WuPaper.ClassicalFourthNat.BPay_7693
  · exact WuPaper.ClassicalFourthNat.BPay_7694
  · exact WuPaper.ClassicalFourthNat.BPay_7695
  · exact WuPaper.ClassicalFourthNat.BPay_7696
  · exact WuPaper.ClassicalFourthNat.BPay_7697
  · exact WuPaper.ClassicalFourthNat.BPay_7698
  · exact WuPaper.ClassicalFourthNat.BPay_7699
  · exact WuPaper.ClassicalFourthNat.BPay_7700
  · exact WuPaper.ClassicalFourthNat.BPay_7701
  · exact WuPaper.ClassicalFourthNat.BPay_7702
  · exact WuPaper.ClassicalFourthNat.BPay_7703
  · exact WuPaper.ClassicalFourthNat.BPay_7704
  · exact WuPaper.ClassicalFourthNat.BPay_7705
  · exact WuPaper.ClassicalFourthNat.BPay_7706
  · exact WuPaper.ClassicalFourthNat.BPay_7707
  · exact WuPaper.ClassicalFourthNat.BPay_7708
  · exact WuPaper.ClassicalFourthNat.BPay_7709
  · exact WuPaper.ClassicalFourthNat.BPay_7710
  · exact WuPaper.ClassicalFourthNat.BPay_7711
  · exact WuPaper.ClassicalFourthNat.BPay_7712
  · exact WuPaper.ClassicalFourthNat.BPay_7713
  · exact WuPaper.ClassicalFourthNat.BPay_7714
  · exact WuPaper.ClassicalFourthNat.BPay_7715
  · exact WuPaper.ClassicalFourthNat.BPay_7716
  · exact WuPaper.ClassicalFourthNat.BPay_7717
  · exact WuPaper.ClassicalFourthNat.BPay_7718
  · exact WuPaper.ClassicalFourthNat.BPay_7719
  · exact WuPaper.ClassicalFourthNat.BPay_7720
  · exact WuPaper.ClassicalFourthNat.BPay_7721
  · exact WuPaper.ClassicalFourthNat.BPay_7722
  · exact WuPaper.ClassicalFourthNat.BPay_7723
  · exact WuPaper.ClassicalFourthNat.BPay_7724
  · exact WuPaper.ClassicalFourthNat.BPay_7725
  · exact WuPaper.ClassicalFourthNat.BPay_7726
  · exact WuPaper.ClassicalFourthNat.BPay_7727
  · exact WuPaper.ClassicalFourthNat.BPay_7728
  · exact WuPaper.ClassicalFourthNat.BPay_7729
  · exact WuPaper.ClassicalFourthNat.BPay_7730
  · exact WuPaper.ClassicalFourthNat.BPay_7731
  · exact WuPaper.ClassicalFourthNat.BPay_7732
  · exact WuPaper.ClassicalFourthNat.BPay_7733
  · exact WuPaper.ClassicalFourthNat.BPay_7734
  · exact WuPaper.ClassicalFourthNat.BPay_7735
  · exact WuPaper.ClassicalFourthNat.BPay_7736
  · exact WuPaper.ClassicalFourthNat.BPay_7737
  · exact WuPaper.ClassicalFourthNat.BPay_7738
  · exact WuPaper.ClassicalFourthNat.BPay_7739
  · exact WuPaper.ClassicalFourthNat.BPay_7740
  · exact WuPaper.ClassicalFourthNat.BPay_7741
  · exact WuPaper.ClassicalFourthNat.BPay_7742
  · exact WuPaper.ClassicalFourthNat.BPay_7743
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_120
