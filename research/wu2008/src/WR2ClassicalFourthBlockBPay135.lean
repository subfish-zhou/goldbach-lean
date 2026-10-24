import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay135
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_135 (j : Fin 64) (hj : 64*135+j.val < 10540) :
    BPay (64*135+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_8640
  · exact WuPaper.ClassicalFourthNat.BPay_8641
  · exact WuPaper.ClassicalFourthNat.BPay_8642
  · exact WuPaper.ClassicalFourthNat.BPay_8643
  · exact WuPaper.ClassicalFourthNat.BPay_8644
  · exact WuPaper.ClassicalFourthNat.BPay_8645
  · exact WuPaper.ClassicalFourthNat.BPay_8646
  · exact WuPaper.ClassicalFourthNat.BPay_8647
  · exact WuPaper.ClassicalFourthNat.BPay_8648
  · exact WuPaper.ClassicalFourthNat.BPay_8649
  · exact WuPaper.ClassicalFourthNat.BPay_8650
  · exact WuPaper.ClassicalFourthNat.BPay_8651
  · exact WuPaper.ClassicalFourthNat.BPay_8652
  · exact WuPaper.ClassicalFourthNat.BPay_8653
  · exact WuPaper.ClassicalFourthNat.BPay_8654
  · exact WuPaper.ClassicalFourthNat.BPay_8655
  · exact WuPaper.ClassicalFourthNat.BPay_8656
  · exact WuPaper.ClassicalFourthNat.BPay_8657
  · exact WuPaper.ClassicalFourthNat.BPay_8658
  · exact WuPaper.ClassicalFourthNat.BPay_8659
  · exact WuPaper.ClassicalFourthNat.BPay_8660
  · exact WuPaper.ClassicalFourthNat.BPay_8661
  · exact WuPaper.ClassicalFourthNat.BPay_8662
  · exact WuPaper.ClassicalFourthNat.BPay_8663
  · exact WuPaper.ClassicalFourthNat.BPay_8664
  · exact WuPaper.ClassicalFourthNat.BPay_8665
  · exact WuPaper.ClassicalFourthNat.BPay_8666
  · exact WuPaper.ClassicalFourthNat.BPay_8667
  · exact WuPaper.ClassicalFourthNat.BPay_8668
  · exact WuPaper.ClassicalFourthNat.BPay_8669
  · exact WuPaper.ClassicalFourthNat.BPay_8670
  · exact WuPaper.ClassicalFourthNat.BPay_8671
  · exact WuPaper.ClassicalFourthNat.BPay_8672
  · exact WuPaper.ClassicalFourthNat.BPay_8673
  · exact WuPaper.ClassicalFourthNat.BPay_8674
  · exact WuPaper.ClassicalFourthNat.BPay_8675
  · exact WuPaper.ClassicalFourthNat.BPay_8676
  · exact WuPaper.ClassicalFourthNat.BPay_8677
  · exact WuPaper.ClassicalFourthNat.BPay_8678
  · exact WuPaper.ClassicalFourthNat.BPay_8679
  · exact WuPaper.ClassicalFourthNat.BPay_8680
  · exact WuPaper.ClassicalFourthNat.BPay_8681
  · exact WuPaper.ClassicalFourthNat.BPay_8682
  · exact WuPaper.ClassicalFourthNat.BPay_8683
  · exact WuPaper.ClassicalFourthNat.BPay_8684
  · exact WuPaper.ClassicalFourthNat.BPay_8685
  · exact WuPaper.ClassicalFourthNat.BPay_8686
  · exact WuPaper.ClassicalFourthNat.BPay_8687
  · exact WuPaper.ClassicalFourthNat.BPay_8688
  · exact WuPaper.ClassicalFourthNat.BPay_8689
  · exact WuPaper.ClassicalFourthNat.BPay_8690
  · exact WuPaper.ClassicalFourthNat.BPay_8691
  · exact WuPaper.ClassicalFourthNat.BPay_8692
  · exact WuPaper.ClassicalFourthNat.BPay_8693
  · exact WuPaper.ClassicalFourthNat.BPay_8694
  · exact WuPaper.ClassicalFourthNat.BPay_8695
  · exact WuPaper.ClassicalFourthNat.BPay_8696
  · exact WuPaper.ClassicalFourthNat.BPay_8697
  · exact WuPaper.ClassicalFourthNat.BPay_8698
  · exact WuPaper.ClassicalFourthNat.BPay_8699
  · exact WuPaper.ClassicalFourthNat.BPay_8700
  · exact WuPaper.ClassicalFourthNat.BPay_8701
  · exact WuPaper.ClassicalFourthNat.BPay_8702
  · exact WuPaper.ClassicalFourthNat.BPay_8703
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_135
