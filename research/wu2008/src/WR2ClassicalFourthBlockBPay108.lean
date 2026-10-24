import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay108
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_108 (j : Fin 64) (hj : 64*108+j.val < 10540) :
    BPay (64*108+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_6912
  · exact WuPaper.ClassicalFourthNat.BPay_6913
  · exact WuPaper.ClassicalFourthNat.BPay_6914
  · exact WuPaper.ClassicalFourthNat.BPay_6915
  · exact WuPaper.ClassicalFourthNat.BPay_6916
  · exact WuPaper.ClassicalFourthNat.BPay_6917
  · exact WuPaper.ClassicalFourthNat.BPay_6918
  · exact WuPaper.ClassicalFourthNat.BPay_6919
  · exact WuPaper.ClassicalFourthNat.BPay_6920
  · exact WuPaper.ClassicalFourthNat.BPay_6921
  · exact WuPaper.ClassicalFourthNat.BPay_6922
  · exact WuPaper.ClassicalFourthNat.BPay_6923
  · exact WuPaper.ClassicalFourthNat.BPay_6924
  · exact WuPaper.ClassicalFourthNat.BPay_6925
  · exact WuPaper.ClassicalFourthNat.BPay_6926
  · exact WuPaper.ClassicalFourthNat.BPay_6927
  · exact WuPaper.ClassicalFourthNat.BPay_6928
  · exact WuPaper.ClassicalFourthNat.BPay_6929
  · exact WuPaper.ClassicalFourthNat.BPay_6930
  · exact WuPaper.ClassicalFourthNat.BPay_6931
  · exact WuPaper.ClassicalFourthNat.BPay_6932
  · exact WuPaper.ClassicalFourthNat.BPay_6933
  · exact WuPaper.ClassicalFourthNat.BPay_6934
  · exact WuPaper.ClassicalFourthNat.BPay_6935
  · exact WuPaper.ClassicalFourthNat.BPay_6936
  · exact WuPaper.ClassicalFourthNat.BPay_6937
  · exact WuPaper.ClassicalFourthNat.BPay_6938
  · exact WuPaper.ClassicalFourthNat.BPay_6939
  · exact WuPaper.ClassicalFourthNat.BPay_6940
  · exact WuPaper.ClassicalFourthNat.BPay_6941
  · exact WuPaper.ClassicalFourthNat.BPay_6942
  · exact WuPaper.ClassicalFourthNat.BPay_6943
  · exact WuPaper.ClassicalFourthNat.BPay_6944
  · exact WuPaper.ClassicalFourthNat.BPay_6945
  · exact WuPaper.ClassicalFourthNat.BPay_6946
  · exact WuPaper.ClassicalFourthNat.BPay_6947
  · exact WuPaper.ClassicalFourthNat.BPay_6948
  · exact WuPaper.ClassicalFourthNat.BPay_6949
  · exact WuPaper.ClassicalFourthNat.BPay_6950
  · exact WuPaper.ClassicalFourthNat.BPay_6951
  · exact WuPaper.ClassicalFourthNat.BPay_6952
  · exact WuPaper.ClassicalFourthNat.BPay_6953
  · exact WuPaper.ClassicalFourthNat.BPay_6954
  · exact WuPaper.ClassicalFourthNat.BPay_6955
  · exact WuPaper.ClassicalFourthNat.BPay_6956
  · exact WuPaper.ClassicalFourthNat.BPay_6957
  · exact WuPaper.ClassicalFourthNat.BPay_6958
  · exact WuPaper.ClassicalFourthNat.BPay_6959
  · exact WuPaper.ClassicalFourthNat.BPay_6960
  · exact WuPaper.ClassicalFourthNat.BPay_6961
  · exact WuPaper.ClassicalFourthNat.BPay_6962
  · exact WuPaper.ClassicalFourthNat.BPay_6963
  · exact WuPaper.ClassicalFourthNat.BPay_6964
  · exact WuPaper.ClassicalFourthNat.BPay_6965
  · exact WuPaper.ClassicalFourthNat.BPay_6966
  · exact WuPaper.ClassicalFourthNat.BPay_6967
  · exact WuPaper.ClassicalFourthNat.BPay_6968
  · exact WuPaper.ClassicalFourthNat.BPay_6969
  · exact WuPaper.ClassicalFourthNat.BPay_6970
  · exact WuPaper.ClassicalFourthNat.BPay_6971
  · exact WuPaper.ClassicalFourthNat.BPay_6972
  · exact WuPaper.ClassicalFourthNat.BPay_6973
  · exact WuPaper.ClassicalFourthNat.BPay_6974
  · exact WuPaper.ClassicalFourthNat.BPay_6975
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_108
