import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay154
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_154 (j : Fin 64) (hj : 64*154+j.val < 10540) :
    BPay (64*154+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_9856
  · exact WuPaper.ClassicalFourthNat.BPay_9857
  · exact WuPaper.ClassicalFourthNat.BPay_9858
  · exact WuPaper.ClassicalFourthNat.BPay_9859
  · exact WuPaper.ClassicalFourthNat.BPay_9860
  · exact WuPaper.ClassicalFourthNat.BPay_9861
  · exact WuPaper.ClassicalFourthNat.BPay_9862
  · exact WuPaper.ClassicalFourthNat.BPay_9863
  · exact WuPaper.ClassicalFourthNat.BPay_9864
  · exact WuPaper.ClassicalFourthNat.BPay_9865
  · exact WuPaper.ClassicalFourthNat.BPay_9866
  · exact WuPaper.ClassicalFourthNat.BPay_9867
  · exact WuPaper.ClassicalFourthNat.BPay_9868
  · exact WuPaper.ClassicalFourthNat.BPay_9869
  · exact WuPaper.ClassicalFourthNat.BPay_9870
  · exact WuPaper.ClassicalFourthNat.BPay_9871
  · exact WuPaper.ClassicalFourthNat.BPay_9872
  · exact WuPaper.ClassicalFourthNat.BPay_9873
  · exact WuPaper.ClassicalFourthNat.BPay_9874
  · exact WuPaper.ClassicalFourthNat.BPay_9875
  · exact WuPaper.ClassicalFourthNat.BPay_9876
  · exact WuPaper.ClassicalFourthNat.BPay_9877
  · exact WuPaper.ClassicalFourthNat.BPay_9878
  · exact WuPaper.ClassicalFourthNat.BPay_9879
  · exact WuPaper.ClassicalFourthNat.BPay_9880
  · exact WuPaper.ClassicalFourthNat.BPay_9881
  · exact WuPaper.ClassicalFourthNat.BPay_9882
  · exact WuPaper.ClassicalFourthNat.BPay_9883
  · exact WuPaper.ClassicalFourthNat.BPay_9884
  · exact WuPaper.ClassicalFourthNat.BPay_9885
  · exact WuPaper.ClassicalFourthNat.BPay_9886
  · exact WuPaper.ClassicalFourthNat.BPay_9887
  · exact WuPaper.ClassicalFourthNat.BPay_9888
  · exact WuPaper.ClassicalFourthNat.BPay_9889
  · exact WuPaper.ClassicalFourthNat.BPay_9890
  · exact WuPaper.ClassicalFourthNat.BPay_9891
  · exact WuPaper.ClassicalFourthNat.BPay_9892
  · exact WuPaper.ClassicalFourthNat.BPay_9893
  · exact WuPaper.ClassicalFourthNat.BPay_9894
  · exact WuPaper.ClassicalFourthNat.BPay_9895
  · exact WuPaper.ClassicalFourthNat.BPay_9896
  · exact WuPaper.ClassicalFourthNat.BPay_9897
  · exact WuPaper.ClassicalFourthNat.BPay_9898
  · exact WuPaper.ClassicalFourthNat.BPay_9899
  · exact WuPaper.ClassicalFourthNat.BPay_9900
  · exact WuPaper.ClassicalFourthNat.BPay_9901
  · exact WuPaper.ClassicalFourthNat.BPay_9902
  · exact WuPaper.ClassicalFourthNat.BPay_9903
  · exact WuPaper.ClassicalFourthNat.BPay_9904
  · exact WuPaper.ClassicalFourthNat.BPay_9905
  · exact WuPaper.ClassicalFourthNat.BPay_9906
  · exact WuPaper.ClassicalFourthNat.BPay_9907
  · exact WuPaper.ClassicalFourthNat.BPay_9908
  · exact WuPaper.ClassicalFourthNat.BPay_9909
  · exact WuPaper.ClassicalFourthNat.BPay_9910
  · exact WuPaper.ClassicalFourthNat.BPay_9911
  · exact WuPaper.ClassicalFourthNat.BPay_9912
  · exact WuPaper.ClassicalFourthNat.BPay_9913
  · exact WuPaper.ClassicalFourthNat.BPay_9914
  · exact WuPaper.ClassicalFourthNat.BPay_9915
  · exact WuPaper.ClassicalFourthNat.BPay_9916
  · exact WuPaper.ClassicalFourthNat.BPay_9917
  · exact WuPaper.ClassicalFourthNat.BPay_9918
  · exact WuPaper.ClassicalFourthNat.BPay_9919
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_154
