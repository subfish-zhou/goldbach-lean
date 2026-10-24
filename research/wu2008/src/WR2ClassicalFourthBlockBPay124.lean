import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay124
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_124 (j : Fin 64) (hj : 64*124+j.val < 10540) :
    BPay (64*124+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_7936
  · exact WuPaper.ClassicalFourthNat.BPay_7937
  · exact WuPaper.ClassicalFourthNat.BPay_7938
  · exact WuPaper.ClassicalFourthNat.BPay_7939
  · exact WuPaper.ClassicalFourthNat.BPay_7940
  · exact WuPaper.ClassicalFourthNat.BPay_7941
  · exact WuPaper.ClassicalFourthNat.BPay_7942
  · exact WuPaper.ClassicalFourthNat.BPay_7943
  · exact WuPaper.ClassicalFourthNat.BPay_7944
  · exact WuPaper.ClassicalFourthNat.BPay_7945
  · exact WuPaper.ClassicalFourthNat.BPay_7946
  · exact WuPaper.ClassicalFourthNat.BPay_7947
  · exact WuPaper.ClassicalFourthNat.BPay_7948
  · exact WuPaper.ClassicalFourthNat.BPay_7949
  · exact WuPaper.ClassicalFourthNat.BPay_7950
  · exact WuPaper.ClassicalFourthNat.BPay_7951
  · exact WuPaper.ClassicalFourthNat.BPay_7952
  · exact WuPaper.ClassicalFourthNat.BPay_7953
  · exact WuPaper.ClassicalFourthNat.BPay_7954
  · exact WuPaper.ClassicalFourthNat.BPay_7955
  · exact WuPaper.ClassicalFourthNat.BPay_7956
  · exact WuPaper.ClassicalFourthNat.BPay_7957
  · exact WuPaper.ClassicalFourthNat.BPay_7958
  · exact WuPaper.ClassicalFourthNat.BPay_7959
  · exact WuPaper.ClassicalFourthNat.BPay_7960
  · exact WuPaper.ClassicalFourthNat.BPay_7961
  · exact WuPaper.ClassicalFourthNat.BPay_7962
  · exact WuPaper.ClassicalFourthNat.BPay_7963
  · exact WuPaper.ClassicalFourthNat.BPay_7964
  · exact WuPaper.ClassicalFourthNat.BPay_7965
  · exact WuPaper.ClassicalFourthNat.BPay_7966
  · exact WuPaper.ClassicalFourthNat.BPay_7967
  · exact WuPaper.ClassicalFourthNat.BPay_7968
  · exact WuPaper.ClassicalFourthNat.BPay_7969
  · exact WuPaper.ClassicalFourthNat.BPay_7970
  · exact WuPaper.ClassicalFourthNat.BPay_7971
  · exact WuPaper.ClassicalFourthNat.BPay_7972
  · exact WuPaper.ClassicalFourthNat.BPay_7973
  · exact WuPaper.ClassicalFourthNat.BPay_7974
  · exact WuPaper.ClassicalFourthNat.BPay_7975
  · exact WuPaper.ClassicalFourthNat.BPay_7976
  · exact WuPaper.ClassicalFourthNat.BPay_7977
  · exact WuPaper.ClassicalFourthNat.BPay_7978
  · exact WuPaper.ClassicalFourthNat.BPay_7979
  · exact WuPaper.ClassicalFourthNat.BPay_7980
  · exact WuPaper.ClassicalFourthNat.BPay_7981
  · exact WuPaper.ClassicalFourthNat.BPay_7982
  · exact WuPaper.ClassicalFourthNat.BPay_7983
  · exact WuPaper.ClassicalFourthNat.BPay_7984
  · exact WuPaper.ClassicalFourthNat.BPay_7985
  · exact WuPaper.ClassicalFourthNat.BPay_7986
  · exact WuPaper.ClassicalFourthNat.BPay_7987
  · exact WuPaper.ClassicalFourthNat.BPay_7988
  · exact WuPaper.ClassicalFourthNat.BPay_7989
  · exact WuPaper.ClassicalFourthNat.BPay_7990
  · exact WuPaper.ClassicalFourthNat.BPay_7991
  · exact WuPaper.ClassicalFourthNat.BPay_7992
  · exact WuPaper.ClassicalFourthNat.BPay_7993
  · exact WuPaper.ClassicalFourthNat.BPay_7994
  · exact WuPaper.ClassicalFourthNat.BPay_7995
  · exact WuPaper.ClassicalFourthNat.BPay_7996
  · exact WuPaper.ClassicalFourthNat.BPay_7997
  · exact WuPaper.ClassicalFourthNat.BPay_7998
  · exact WuPaper.ClassicalFourthNat.BPay_7999
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_124
