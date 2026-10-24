import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatouterPay155
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem outerPay_block_155 (j : Fin 64) (hj : 64*155+j.val < 10540) :
    OuterPay (64*155+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.outerPay_9920
  · exact WuPaper.ClassicalFourthNat.outerPay_9921
  · exact WuPaper.ClassicalFourthNat.outerPay_9922
  · exact WuPaper.ClassicalFourthNat.outerPay_9923
  · exact WuPaper.ClassicalFourthNat.outerPay_9924
  · exact WuPaper.ClassicalFourthNat.outerPay_9925
  · exact WuPaper.ClassicalFourthNat.outerPay_9926
  · exact WuPaper.ClassicalFourthNat.outerPay_9927
  · exact WuPaper.ClassicalFourthNat.outerPay_9928
  · exact WuPaper.ClassicalFourthNat.outerPay_9929
  · exact WuPaper.ClassicalFourthNat.outerPay_9930
  · exact WuPaper.ClassicalFourthNat.outerPay_9931
  · exact WuPaper.ClassicalFourthNat.outerPay_9932
  · exact WuPaper.ClassicalFourthNat.outerPay_9933
  · exact WuPaper.ClassicalFourthNat.outerPay_9934
  · exact WuPaper.ClassicalFourthNat.outerPay_9935
  · exact WuPaper.ClassicalFourthNat.outerPay_9936
  · exact WuPaper.ClassicalFourthNat.outerPay_9937
  · exact WuPaper.ClassicalFourthNat.outerPay_9938
  · exact WuPaper.ClassicalFourthNat.outerPay_9939
  · exact WuPaper.ClassicalFourthNat.outerPay_9940
  · exact WuPaper.ClassicalFourthNat.outerPay_9941
  · exact WuPaper.ClassicalFourthNat.outerPay_9942
  · exact WuPaper.ClassicalFourthNat.outerPay_9943
  · exact WuPaper.ClassicalFourthNat.outerPay_9944
  · exact WuPaper.ClassicalFourthNat.outerPay_9945
  · exact WuPaper.ClassicalFourthNat.outerPay_9946
  · exact WuPaper.ClassicalFourthNat.outerPay_9947
  · exact WuPaper.ClassicalFourthNat.outerPay_9948
  · exact WuPaper.ClassicalFourthNat.outerPay_9949
  · exact WuPaper.ClassicalFourthNat.outerPay_9950
  · exact WuPaper.ClassicalFourthNat.outerPay_9951
  · exact WuPaper.ClassicalFourthNat.outerPay_9952
  · exact WuPaper.ClassicalFourthNat.outerPay_9953
  · exact WuPaper.ClassicalFourthNat.outerPay_9954
  · exact WuPaper.ClassicalFourthNat.outerPay_9955
  · exact WuPaper.ClassicalFourthNat.outerPay_9956
  · exact WuPaper.ClassicalFourthNat.outerPay_9957
  · exact WuPaper.ClassicalFourthNat.outerPay_9958
  · exact WuPaper.ClassicalFourthNat.outerPay_9959
  · exact WuPaper.ClassicalFourthNat.outerPay_9960
  · exact WuPaper.ClassicalFourthNat.outerPay_9961
  · exact WuPaper.ClassicalFourthNat.outerPay_9962
  · exact WuPaper.ClassicalFourthNat.outerPay_9963
  · exact WuPaper.ClassicalFourthNat.outerPay_9964
  · exact WuPaper.ClassicalFourthNat.outerPay_9965
  · exact WuPaper.ClassicalFourthNat.outerPay_9966
  · exact WuPaper.ClassicalFourthNat.outerPay_9967
  · exact WuPaper.ClassicalFourthNat.outerPay_9968
  · exact WuPaper.ClassicalFourthNat.outerPay_9969
  · exact WuPaper.ClassicalFourthNat.outerPay_9970
  · exact WuPaper.ClassicalFourthNat.outerPay_9971
  · exact WuPaper.ClassicalFourthNat.outerPay_9972
  · exact WuPaper.ClassicalFourthNat.outerPay_9973
  · exact WuPaper.ClassicalFourthNat.outerPay_9974
  · exact WuPaper.ClassicalFourthNat.outerPay_9975
  · exact WuPaper.ClassicalFourthNat.outerPay_9976
  · exact WuPaper.ClassicalFourthNat.outerPay_9977
  · exact WuPaper.ClassicalFourthNat.outerPay_9978
  · exact WuPaper.ClassicalFourthNat.outerPay_9979
  · exact WuPaper.ClassicalFourthNat.outerPay_9980
  · exact WuPaper.ClassicalFourthNat.outerPay_9981
  · exact WuPaper.ClassicalFourthNat.outerPay_9982
  · exact WuPaper.ClassicalFourthNat.outerPay_9983
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.outerPay_block_155
