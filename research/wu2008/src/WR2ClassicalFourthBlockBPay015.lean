import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay015
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_015 (j : Fin 64) (hj : 64*15+j.val < 10540) :
    BPay (64*15+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_960
  · exact WuPaper.ClassicalFourthNat.BPay_961
  · exact WuPaper.ClassicalFourthNat.BPay_962
  · exact WuPaper.ClassicalFourthNat.BPay_963
  · exact WuPaper.ClassicalFourthNat.BPay_964
  · exact WuPaper.ClassicalFourthNat.BPay_965
  · exact WuPaper.ClassicalFourthNat.BPay_966
  · exact WuPaper.ClassicalFourthNat.BPay_967
  · exact WuPaper.ClassicalFourthNat.BPay_968
  · exact WuPaper.ClassicalFourthNat.BPay_969
  · exact WuPaper.ClassicalFourthNat.BPay_970
  · exact WuPaper.ClassicalFourthNat.BPay_971
  · exact WuPaper.ClassicalFourthNat.BPay_972
  · exact WuPaper.ClassicalFourthNat.BPay_973
  · exact WuPaper.ClassicalFourthNat.BPay_974
  · exact WuPaper.ClassicalFourthNat.BPay_975
  · exact WuPaper.ClassicalFourthNat.BPay_976
  · exact WuPaper.ClassicalFourthNat.BPay_977
  · exact WuPaper.ClassicalFourthNat.BPay_978
  · exact WuPaper.ClassicalFourthNat.BPay_979
  · exact WuPaper.ClassicalFourthNat.BPay_980
  · exact WuPaper.ClassicalFourthNat.BPay_981
  · exact WuPaper.ClassicalFourthNat.BPay_982
  · exact WuPaper.ClassicalFourthNat.BPay_983
  · exact WuPaper.ClassicalFourthNat.BPay_984
  · exact WuPaper.ClassicalFourthNat.BPay_985
  · exact WuPaper.ClassicalFourthNat.BPay_986
  · exact WuPaper.ClassicalFourthNat.BPay_987
  · exact WuPaper.ClassicalFourthNat.BPay_988
  · exact WuPaper.ClassicalFourthNat.BPay_989
  · exact WuPaper.ClassicalFourthNat.BPay_990
  · exact WuPaper.ClassicalFourthNat.BPay_991
  · exact WuPaper.ClassicalFourthNat.BPay_992
  · exact WuPaper.ClassicalFourthNat.BPay_993
  · exact WuPaper.ClassicalFourthNat.BPay_994
  · exact WuPaper.ClassicalFourthNat.BPay_995
  · exact WuPaper.ClassicalFourthNat.BPay_996
  · exact WuPaper.ClassicalFourthNat.BPay_997
  · exact WuPaper.ClassicalFourthNat.BPay_998
  · exact WuPaper.ClassicalFourthNat.BPay_999
  · exact WuPaper.ClassicalFourthNat.BPay_1000
  · exact WuPaper.ClassicalFourthNat.BPay_1001
  · exact WuPaper.ClassicalFourthNat.BPay_1002
  · exact WuPaper.ClassicalFourthNat.BPay_1003
  · exact WuPaper.ClassicalFourthNat.BPay_1004
  · exact WuPaper.ClassicalFourthNat.BPay_1005
  · exact WuPaper.ClassicalFourthNat.BPay_1006
  · exact WuPaper.ClassicalFourthNat.BPay_1007
  · exact WuPaper.ClassicalFourthNat.BPay_1008
  · exact WuPaper.ClassicalFourthNat.BPay_1009
  · exact WuPaper.ClassicalFourthNat.BPay_1010
  · exact WuPaper.ClassicalFourthNat.BPay_1011
  · exact WuPaper.ClassicalFourthNat.BPay_1012
  · exact WuPaper.ClassicalFourthNat.BPay_1013
  · exact WuPaper.ClassicalFourthNat.BPay_1014
  · exact WuPaper.ClassicalFourthNat.BPay_1015
  · exact WuPaper.ClassicalFourthNat.BPay_1016
  · exact WuPaper.ClassicalFourthNat.BPay_1017
  · exact WuPaper.ClassicalFourthNat.BPay_1018
  · exact WuPaper.ClassicalFourthNat.BPay_1019
  · exact WuPaper.ClassicalFourthNat.BPay_1020
  · exact WuPaper.ClassicalFourthNat.BPay_1021
  · exact WuPaper.ClassicalFourthNat.BPay_1022
  · exact WuPaper.ClassicalFourthNat.BPay_1023
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_015
