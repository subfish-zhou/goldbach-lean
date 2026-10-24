import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatouterPay108
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem outerPay_block_108 (j : Fin 64) (hj : 64*108+j.val < 10540) :
    OuterPay (64*108+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.outerPay_6912
  · exact WuPaper.ClassicalFourthNat.outerPay_6913
  · exact WuPaper.ClassicalFourthNat.outerPay_6914
  · exact WuPaper.ClassicalFourthNat.outerPay_6915
  · exact WuPaper.ClassicalFourthNat.outerPay_6916
  · exact WuPaper.ClassicalFourthNat.outerPay_6917
  · exact WuPaper.ClassicalFourthNat.outerPay_6918
  · exact WuPaper.ClassicalFourthNat.outerPay_6919
  · exact WuPaper.ClassicalFourthNat.outerPay_6920
  · exact WuPaper.ClassicalFourthNat.outerPay_6921
  · exact WuPaper.ClassicalFourthNat.outerPay_6922
  · exact WuPaper.ClassicalFourthNat.outerPay_6923
  · exact WuPaper.ClassicalFourthNat.outerPay_6924
  · exact WuPaper.ClassicalFourthNat.outerPay_6925
  · exact WuPaper.ClassicalFourthNat.outerPay_6926
  · exact WuPaper.ClassicalFourthNat.outerPay_6927
  · exact WuPaper.ClassicalFourthNat.outerPay_6928
  · exact WuPaper.ClassicalFourthNat.outerPay_6929
  · exact WuPaper.ClassicalFourthNat.outerPay_6930
  · exact WuPaper.ClassicalFourthNat.outerPay_6931
  · exact WuPaper.ClassicalFourthNat.outerPay_6932
  · exact WuPaper.ClassicalFourthNat.outerPay_6933
  · exact WuPaper.ClassicalFourthNat.outerPay_6934
  · exact WuPaper.ClassicalFourthNat.outerPay_6935
  · exact WuPaper.ClassicalFourthNat.outerPay_6936
  · exact WuPaper.ClassicalFourthNat.outerPay_6937
  · exact WuPaper.ClassicalFourthNat.outerPay_6938
  · exact WuPaper.ClassicalFourthNat.outerPay_6939
  · exact WuPaper.ClassicalFourthNat.outerPay_6940
  · exact WuPaper.ClassicalFourthNat.outerPay_6941
  · exact WuPaper.ClassicalFourthNat.outerPay_6942
  · exact WuPaper.ClassicalFourthNat.outerPay_6943
  · exact WuPaper.ClassicalFourthNat.outerPay_6944
  · exact WuPaper.ClassicalFourthNat.outerPay_6945
  · exact WuPaper.ClassicalFourthNat.outerPay_6946
  · exact WuPaper.ClassicalFourthNat.outerPay_6947
  · exact WuPaper.ClassicalFourthNat.outerPay_6948
  · exact WuPaper.ClassicalFourthNat.outerPay_6949
  · exact WuPaper.ClassicalFourthNat.outerPay_6950
  · exact WuPaper.ClassicalFourthNat.outerPay_6951
  · exact WuPaper.ClassicalFourthNat.outerPay_6952
  · exact WuPaper.ClassicalFourthNat.outerPay_6953
  · exact WuPaper.ClassicalFourthNat.outerPay_6954
  · exact WuPaper.ClassicalFourthNat.outerPay_6955
  · exact WuPaper.ClassicalFourthNat.outerPay_6956
  · exact WuPaper.ClassicalFourthNat.outerPay_6957
  · exact WuPaper.ClassicalFourthNat.outerPay_6958
  · exact WuPaper.ClassicalFourthNat.outerPay_6959
  · exact WuPaper.ClassicalFourthNat.outerPay_6960
  · exact WuPaper.ClassicalFourthNat.outerPay_6961
  · exact WuPaper.ClassicalFourthNat.outerPay_6962
  · exact WuPaper.ClassicalFourthNat.outerPay_6963
  · exact WuPaper.ClassicalFourthNat.outerPay_6964
  · exact WuPaper.ClassicalFourthNat.outerPay_6965
  · exact WuPaper.ClassicalFourthNat.outerPay_6966
  · exact WuPaper.ClassicalFourthNat.outerPay_6967
  · exact WuPaper.ClassicalFourthNat.outerPay_6968
  · exact WuPaper.ClassicalFourthNat.outerPay_6969
  · exact WuPaper.ClassicalFourthNat.outerPay_6970
  · exact WuPaper.ClassicalFourthNat.outerPay_6971
  · exact WuPaper.ClassicalFourthNat.outerPay_6972
  · exact WuPaper.ClassicalFourthNat.outerPay_6973
  · exact WuPaper.ClassicalFourthNat.outerPay_6974
  · exact WuPaper.ClassicalFourthNat.outerPay_6975
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.outerPay_block_108
