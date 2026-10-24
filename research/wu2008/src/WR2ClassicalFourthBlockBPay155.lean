import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay155
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_155 (j : Fin 64) (hj : 64*155+j.val < 10540) :
    BPay (64*155+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_9920
  · exact WuPaper.ClassicalFourthNat.BPay_9921
  · exact WuPaper.ClassicalFourthNat.BPay_9922
  · exact WuPaper.ClassicalFourthNat.BPay_9923
  · exact WuPaper.ClassicalFourthNat.BPay_9924
  · exact WuPaper.ClassicalFourthNat.BPay_9925
  · exact WuPaper.ClassicalFourthNat.BPay_9926
  · exact WuPaper.ClassicalFourthNat.BPay_9927
  · exact WuPaper.ClassicalFourthNat.BPay_9928
  · exact WuPaper.ClassicalFourthNat.BPay_9929
  · exact WuPaper.ClassicalFourthNat.BPay_9930
  · exact WuPaper.ClassicalFourthNat.BPay_9931
  · exact WuPaper.ClassicalFourthNat.BPay_9932
  · exact WuPaper.ClassicalFourthNat.BPay_9933
  · exact WuPaper.ClassicalFourthNat.BPay_9934
  · exact WuPaper.ClassicalFourthNat.BPay_9935
  · exact WuPaper.ClassicalFourthNat.BPay_9936
  · exact WuPaper.ClassicalFourthNat.BPay_9937
  · exact WuPaper.ClassicalFourthNat.BPay_9938
  · exact WuPaper.ClassicalFourthNat.BPay_9939
  · exact WuPaper.ClassicalFourthNat.BPay_9940
  · exact WuPaper.ClassicalFourthNat.BPay_9941
  · exact WuPaper.ClassicalFourthNat.BPay_9942
  · exact WuPaper.ClassicalFourthNat.BPay_9943
  · exact WuPaper.ClassicalFourthNat.BPay_9944
  · exact WuPaper.ClassicalFourthNat.BPay_9945
  · exact WuPaper.ClassicalFourthNat.BPay_9946
  · exact WuPaper.ClassicalFourthNat.BPay_9947
  · exact WuPaper.ClassicalFourthNat.BPay_9948
  · exact WuPaper.ClassicalFourthNat.BPay_9949
  · exact WuPaper.ClassicalFourthNat.BPay_9950
  · exact WuPaper.ClassicalFourthNat.BPay_9951
  · exact WuPaper.ClassicalFourthNat.BPay_9952
  · exact WuPaper.ClassicalFourthNat.BPay_9953
  · exact WuPaper.ClassicalFourthNat.BPay_9954
  · exact WuPaper.ClassicalFourthNat.BPay_9955
  · exact WuPaper.ClassicalFourthNat.BPay_9956
  · exact WuPaper.ClassicalFourthNat.BPay_9957
  · exact WuPaper.ClassicalFourthNat.BPay_9958
  · exact WuPaper.ClassicalFourthNat.BPay_9959
  · exact WuPaper.ClassicalFourthNat.BPay_9960
  · exact WuPaper.ClassicalFourthNat.BPay_9961
  · exact WuPaper.ClassicalFourthNat.BPay_9962
  · exact WuPaper.ClassicalFourthNat.BPay_9963
  · exact WuPaper.ClassicalFourthNat.BPay_9964
  · exact WuPaper.ClassicalFourthNat.BPay_9965
  · exact WuPaper.ClassicalFourthNat.BPay_9966
  · exact WuPaper.ClassicalFourthNat.BPay_9967
  · exact WuPaper.ClassicalFourthNat.BPay_9968
  · exact WuPaper.ClassicalFourthNat.BPay_9969
  · exact WuPaper.ClassicalFourthNat.BPay_9970
  · exact WuPaper.ClassicalFourthNat.BPay_9971
  · exact WuPaper.ClassicalFourthNat.BPay_9972
  · exact WuPaper.ClassicalFourthNat.BPay_9973
  · exact WuPaper.ClassicalFourthNat.BPay_9974
  · exact WuPaper.ClassicalFourthNat.BPay_9975
  · exact WuPaper.ClassicalFourthNat.BPay_9976
  · exact WuPaper.ClassicalFourthNat.BPay_9977
  · exact WuPaper.ClassicalFourthNat.BPay_9978
  · exact WuPaper.ClassicalFourthNat.BPay_9979
  · exact WuPaper.ClassicalFourthNat.BPay_9980
  · exact WuPaper.ClassicalFourthNat.BPay_9981
  · exact WuPaper.ClassicalFourthNat.BPay_9982
  · exact WuPaper.ClassicalFourthNat.BPay_9983
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_155
