import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatouterPay135
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem outerPay_block_135 (j : Fin 64) (hj : 64*135+j.val < 10540) :
    OuterPay (64*135+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.outerPay_8640
  · exact WuPaper.ClassicalFourthNat.outerPay_8641
  · exact WuPaper.ClassicalFourthNat.outerPay_8642
  · exact WuPaper.ClassicalFourthNat.outerPay_8643
  · exact WuPaper.ClassicalFourthNat.outerPay_8644
  · exact WuPaper.ClassicalFourthNat.outerPay_8645
  · exact WuPaper.ClassicalFourthNat.outerPay_8646
  · exact WuPaper.ClassicalFourthNat.outerPay_8647
  · exact WuPaper.ClassicalFourthNat.outerPay_8648
  · exact WuPaper.ClassicalFourthNat.outerPay_8649
  · exact WuPaper.ClassicalFourthNat.outerPay_8650
  · exact WuPaper.ClassicalFourthNat.outerPay_8651
  · exact WuPaper.ClassicalFourthNat.outerPay_8652
  · exact WuPaper.ClassicalFourthNat.outerPay_8653
  · exact WuPaper.ClassicalFourthNat.outerPay_8654
  · exact WuPaper.ClassicalFourthNat.outerPay_8655
  · exact WuPaper.ClassicalFourthNat.outerPay_8656
  · exact WuPaper.ClassicalFourthNat.outerPay_8657
  · exact WuPaper.ClassicalFourthNat.outerPay_8658
  · exact WuPaper.ClassicalFourthNat.outerPay_8659
  · exact WuPaper.ClassicalFourthNat.outerPay_8660
  · exact WuPaper.ClassicalFourthNat.outerPay_8661
  · exact WuPaper.ClassicalFourthNat.outerPay_8662
  · exact WuPaper.ClassicalFourthNat.outerPay_8663
  · exact WuPaper.ClassicalFourthNat.outerPay_8664
  · exact WuPaper.ClassicalFourthNat.outerPay_8665
  · exact WuPaper.ClassicalFourthNat.outerPay_8666
  · exact WuPaper.ClassicalFourthNat.outerPay_8667
  · exact WuPaper.ClassicalFourthNat.outerPay_8668
  · exact WuPaper.ClassicalFourthNat.outerPay_8669
  · exact WuPaper.ClassicalFourthNat.outerPay_8670
  · exact WuPaper.ClassicalFourthNat.outerPay_8671
  · exact WuPaper.ClassicalFourthNat.outerPay_8672
  · exact WuPaper.ClassicalFourthNat.outerPay_8673
  · exact WuPaper.ClassicalFourthNat.outerPay_8674
  · exact WuPaper.ClassicalFourthNat.outerPay_8675
  · exact WuPaper.ClassicalFourthNat.outerPay_8676
  · exact WuPaper.ClassicalFourthNat.outerPay_8677
  · exact WuPaper.ClassicalFourthNat.outerPay_8678
  · exact WuPaper.ClassicalFourthNat.outerPay_8679
  · exact WuPaper.ClassicalFourthNat.outerPay_8680
  · exact WuPaper.ClassicalFourthNat.outerPay_8681
  · exact WuPaper.ClassicalFourthNat.outerPay_8682
  · exact WuPaper.ClassicalFourthNat.outerPay_8683
  · exact WuPaper.ClassicalFourthNat.outerPay_8684
  · exact WuPaper.ClassicalFourthNat.outerPay_8685
  · exact WuPaper.ClassicalFourthNat.outerPay_8686
  · exact WuPaper.ClassicalFourthNat.outerPay_8687
  · exact WuPaper.ClassicalFourthNat.outerPay_8688
  · exact WuPaper.ClassicalFourthNat.outerPay_8689
  · exact WuPaper.ClassicalFourthNat.outerPay_8690
  · exact WuPaper.ClassicalFourthNat.outerPay_8691
  · exact WuPaper.ClassicalFourthNat.outerPay_8692
  · exact WuPaper.ClassicalFourthNat.outerPay_8693
  · exact WuPaper.ClassicalFourthNat.outerPay_8694
  · exact WuPaper.ClassicalFourthNat.outerPay_8695
  · exact WuPaper.ClassicalFourthNat.outerPay_8696
  · exact WuPaper.ClassicalFourthNat.outerPay_8697
  · exact WuPaper.ClassicalFourthNat.outerPay_8698
  · exact WuPaper.ClassicalFourthNat.outerPay_8699
  · exact WuPaper.ClassicalFourthNat.outerPay_8700
  · exact WuPaper.ClassicalFourthNat.outerPay_8701
  · exact WuPaper.ClassicalFourthNat.outerPay_8702
  · exact WuPaper.ClassicalFourthNat.outerPay_8703
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.outerPay_block_135
