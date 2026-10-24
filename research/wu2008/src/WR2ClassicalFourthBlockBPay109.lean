import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay109
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_109 (j : Fin 64) (hj : 64*109+j.val < 10540) :
    BPay (64*109+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_6976
  · exact WuPaper.ClassicalFourthNat.BPay_6977
  · exact WuPaper.ClassicalFourthNat.BPay_6978
  · exact WuPaper.ClassicalFourthNat.BPay_6979
  · exact WuPaper.ClassicalFourthNat.BPay_6980
  · exact WuPaper.ClassicalFourthNat.BPay_6981
  · exact WuPaper.ClassicalFourthNat.BPay_6982
  · exact WuPaper.ClassicalFourthNat.BPay_6983
  · exact WuPaper.ClassicalFourthNat.BPay_6984
  · exact WuPaper.ClassicalFourthNat.BPay_6985
  · exact WuPaper.ClassicalFourthNat.BPay_6986
  · exact WuPaper.ClassicalFourthNat.BPay_6987
  · exact WuPaper.ClassicalFourthNat.BPay_6988
  · exact WuPaper.ClassicalFourthNat.BPay_6989
  · exact WuPaper.ClassicalFourthNat.BPay_6990
  · exact WuPaper.ClassicalFourthNat.BPay_6991
  · exact WuPaper.ClassicalFourthNat.BPay_6992
  · exact WuPaper.ClassicalFourthNat.BPay_6993
  · exact WuPaper.ClassicalFourthNat.BPay_6994
  · exact WuPaper.ClassicalFourthNat.BPay_6995
  · exact WuPaper.ClassicalFourthNat.BPay_6996
  · exact WuPaper.ClassicalFourthNat.BPay_6997
  · exact WuPaper.ClassicalFourthNat.BPay_6998
  · exact WuPaper.ClassicalFourthNat.BPay_6999
  · exact WuPaper.ClassicalFourthNat.BPay_7000
  · exact WuPaper.ClassicalFourthNat.BPay_7001
  · exact WuPaper.ClassicalFourthNat.BPay_7002
  · exact WuPaper.ClassicalFourthNat.BPay_7003
  · exact WuPaper.ClassicalFourthNat.BPay_7004
  · exact WuPaper.ClassicalFourthNat.BPay_7005
  · exact WuPaper.ClassicalFourthNat.BPay_7006
  · exact WuPaper.ClassicalFourthNat.BPay_7007
  · exact WuPaper.ClassicalFourthNat.BPay_7008
  · exact WuPaper.ClassicalFourthNat.BPay_7009
  · exact WuPaper.ClassicalFourthNat.BPay_7010
  · exact WuPaper.ClassicalFourthNat.BPay_7011
  · exact WuPaper.ClassicalFourthNat.BPay_7012
  · exact WuPaper.ClassicalFourthNat.BPay_7013
  · exact WuPaper.ClassicalFourthNat.BPay_7014
  · exact WuPaper.ClassicalFourthNat.BPay_7015
  · exact WuPaper.ClassicalFourthNat.BPay_7016
  · exact WuPaper.ClassicalFourthNat.BPay_7017
  · exact WuPaper.ClassicalFourthNat.BPay_7018
  · exact WuPaper.ClassicalFourthNat.BPay_7019
  · exact WuPaper.ClassicalFourthNat.BPay_7020
  · exact WuPaper.ClassicalFourthNat.BPay_7021
  · exact WuPaper.ClassicalFourthNat.BPay_7022
  · exact WuPaper.ClassicalFourthNat.BPay_7023
  · exact WuPaper.ClassicalFourthNat.BPay_7024
  · exact WuPaper.ClassicalFourthNat.BPay_7025
  · exact WuPaper.ClassicalFourthNat.BPay_7026
  · exact WuPaper.ClassicalFourthNat.BPay_7027
  · exact WuPaper.ClassicalFourthNat.BPay_7028
  · exact WuPaper.ClassicalFourthNat.BPay_7029
  · exact WuPaper.ClassicalFourthNat.BPay_7030
  · exact WuPaper.ClassicalFourthNat.BPay_7031
  · exact WuPaper.ClassicalFourthNat.BPay_7032
  · exact WuPaper.ClassicalFourthNat.BPay_7033
  · exact WuPaper.ClassicalFourthNat.BPay_7034
  · exact WuPaper.ClassicalFourthNat.BPay_7035
  · exact WuPaper.ClassicalFourthNat.BPay_7036
  · exact WuPaper.ClassicalFourthNat.BPay_7037
  · exact WuPaper.ClassicalFourthNat.BPay_7038
  · exact WuPaper.ClassicalFourthNat.BPay_7039
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_109
