import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay152
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_152 (j : Fin 64) (hj : 64*152+j.val < 10540) :
    BPay (64*152+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_9728
  · exact WuPaper.ClassicalFourthNat.BPay_9729
  · exact WuPaper.ClassicalFourthNat.BPay_9730
  · exact WuPaper.ClassicalFourthNat.BPay_9731
  · exact WuPaper.ClassicalFourthNat.BPay_9732
  · exact WuPaper.ClassicalFourthNat.BPay_9733
  · exact WuPaper.ClassicalFourthNat.BPay_9734
  · exact WuPaper.ClassicalFourthNat.BPay_9735
  · exact WuPaper.ClassicalFourthNat.BPay_9736
  · exact WuPaper.ClassicalFourthNat.BPay_9737
  · exact WuPaper.ClassicalFourthNat.BPay_9738
  · exact WuPaper.ClassicalFourthNat.BPay_9739
  · exact WuPaper.ClassicalFourthNat.BPay_9740
  · exact WuPaper.ClassicalFourthNat.BPay_9741
  · exact WuPaper.ClassicalFourthNat.BPay_9742
  · exact WuPaper.ClassicalFourthNat.BPay_9743
  · exact WuPaper.ClassicalFourthNat.BPay_9744
  · exact WuPaper.ClassicalFourthNat.BPay_9745
  · exact WuPaper.ClassicalFourthNat.BPay_9746
  · exact WuPaper.ClassicalFourthNat.BPay_9747
  · exact WuPaper.ClassicalFourthNat.BPay_9748
  · exact WuPaper.ClassicalFourthNat.BPay_9749
  · exact WuPaper.ClassicalFourthNat.BPay_9750
  · exact WuPaper.ClassicalFourthNat.BPay_9751
  · exact WuPaper.ClassicalFourthNat.BPay_9752
  · exact WuPaper.ClassicalFourthNat.BPay_9753
  · exact WuPaper.ClassicalFourthNat.BPay_9754
  · exact WuPaper.ClassicalFourthNat.BPay_9755
  · exact WuPaper.ClassicalFourthNat.BPay_9756
  · exact WuPaper.ClassicalFourthNat.BPay_9757
  · exact WuPaper.ClassicalFourthNat.BPay_9758
  · exact WuPaper.ClassicalFourthNat.BPay_9759
  · exact WuPaper.ClassicalFourthNat.BPay_9760
  · exact WuPaper.ClassicalFourthNat.BPay_9761
  · exact WuPaper.ClassicalFourthNat.BPay_9762
  · exact WuPaper.ClassicalFourthNat.BPay_9763
  · exact WuPaper.ClassicalFourthNat.BPay_9764
  · exact WuPaper.ClassicalFourthNat.BPay_9765
  · exact WuPaper.ClassicalFourthNat.BPay_9766
  · exact WuPaper.ClassicalFourthNat.BPay_9767
  · exact WuPaper.ClassicalFourthNat.BPay_9768
  · exact WuPaper.ClassicalFourthNat.BPay_9769
  · exact WuPaper.ClassicalFourthNat.BPay_9770
  · exact WuPaper.ClassicalFourthNat.BPay_9771
  · exact WuPaper.ClassicalFourthNat.BPay_9772
  · exact WuPaper.ClassicalFourthNat.BPay_9773
  · exact WuPaper.ClassicalFourthNat.BPay_9774
  · exact WuPaper.ClassicalFourthNat.BPay_9775
  · exact WuPaper.ClassicalFourthNat.BPay_9776
  · exact WuPaper.ClassicalFourthNat.BPay_9777
  · exact WuPaper.ClassicalFourthNat.BPay_9778
  · exact WuPaper.ClassicalFourthNat.BPay_9779
  · exact WuPaper.ClassicalFourthNat.BPay_9780
  · exact WuPaper.ClassicalFourthNat.BPay_9781
  · exact WuPaper.ClassicalFourthNat.BPay_9782
  · exact WuPaper.ClassicalFourthNat.BPay_9783
  · exact WuPaper.ClassicalFourthNat.BPay_9784
  · exact WuPaper.ClassicalFourthNat.BPay_9785
  · exact WuPaper.ClassicalFourthNat.BPay_9786
  · exact WuPaper.ClassicalFourthNat.BPay_9787
  · exact WuPaper.ClassicalFourthNat.BPay_9788
  · exact WuPaper.ClassicalFourthNat.BPay_9789
  · exact WuPaper.ClassicalFourthNat.BPay_9790
  · exact WuPaper.ClassicalFourthNat.BPay_9791
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_152
