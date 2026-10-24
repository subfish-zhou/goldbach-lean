import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatouterPay015
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem outerPay_block_015 (j : Fin 64) (hj : 64*15+j.val < 10540) :
    OuterPay (64*15+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.outerPay_960
  · exact WuPaper.ClassicalFourthNat.outerPay_961
  · exact WuPaper.ClassicalFourthNat.outerPay_962
  · exact WuPaper.ClassicalFourthNat.outerPay_963
  · exact WuPaper.ClassicalFourthNat.outerPay_964
  · exact WuPaper.ClassicalFourthNat.outerPay_965
  · exact WuPaper.ClassicalFourthNat.outerPay_966
  · exact WuPaper.ClassicalFourthNat.outerPay_967
  · exact WuPaper.ClassicalFourthNat.outerPay_968
  · exact WuPaper.ClassicalFourthNat.outerPay_969
  · exact WuPaper.ClassicalFourthNat.outerPay_970
  · exact WuPaper.ClassicalFourthNat.outerPay_971
  · exact WuPaper.ClassicalFourthNat.outerPay_972
  · exact WuPaper.ClassicalFourthNat.outerPay_973
  · exact WuPaper.ClassicalFourthNat.outerPay_974
  · exact WuPaper.ClassicalFourthNat.outerPay_975
  · exact WuPaper.ClassicalFourthNat.outerPay_976
  · exact WuPaper.ClassicalFourthNat.outerPay_977
  · exact WuPaper.ClassicalFourthNat.outerPay_978
  · exact WuPaper.ClassicalFourthNat.outerPay_979
  · exact WuPaper.ClassicalFourthNat.outerPay_980
  · exact WuPaper.ClassicalFourthNat.outerPay_981
  · exact WuPaper.ClassicalFourthNat.outerPay_982
  · exact WuPaper.ClassicalFourthNat.outerPay_983
  · exact WuPaper.ClassicalFourthNat.outerPay_984
  · exact WuPaper.ClassicalFourthNat.outerPay_985
  · exact WuPaper.ClassicalFourthNat.outerPay_986
  · exact WuPaper.ClassicalFourthNat.outerPay_987
  · exact WuPaper.ClassicalFourthNat.outerPay_988
  · exact WuPaper.ClassicalFourthNat.outerPay_989
  · exact WuPaper.ClassicalFourthNat.outerPay_990
  · exact WuPaper.ClassicalFourthNat.outerPay_991
  · exact WuPaper.ClassicalFourthNat.outerPay_992
  · exact WuPaper.ClassicalFourthNat.outerPay_993
  · exact WuPaper.ClassicalFourthNat.outerPay_994
  · exact WuPaper.ClassicalFourthNat.outerPay_995
  · exact WuPaper.ClassicalFourthNat.outerPay_996
  · exact WuPaper.ClassicalFourthNat.outerPay_997
  · exact WuPaper.ClassicalFourthNat.outerPay_998
  · exact WuPaper.ClassicalFourthNat.outerPay_999
  · exact WuPaper.ClassicalFourthNat.outerPay_1000
  · exact WuPaper.ClassicalFourthNat.outerPay_1001
  · exact WuPaper.ClassicalFourthNat.outerPay_1002
  · exact WuPaper.ClassicalFourthNat.outerPay_1003
  · exact WuPaper.ClassicalFourthNat.outerPay_1004
  · exact WuPaper.ClassicalFourthNat.outerPay_1005
  · exact WuPaper.ClassicalFourthNat.outerPay_1006
  · exact WuPaper.ClassicalFourthNat.outerPay_1007
  · exact WuPaper.ClassicalFourthNat.outerPay_1008
  · exact WuPaper.ClassicalFourthNat.outerPay_1009
  · exact WuPaper.ClassicalFourthNat.outerPay_1010
  · exact WuPaper.ClassicalFourthNat.outerPay_1011
  · exact WuPaper.ClassicalFourthNat.outerPay_1012
  · exact WuPaper.ClassicalFourthNat.outerPay_1013
  · exact WuPaper.ClassicalFourthNat.outerPay_1014
  · exact WuPaper.ClassicalFourthNat.outerPay_1015
  · exact WuPaper.ClassicalFourthNat.outerPay_1016
  · exact WuPaper.ClassicalFourthNat.outerPay_1017
  · exact WuPaper.ClassicalFourthNat.outerPay_1018
  · exact WuPaper.ClassicalFourthNat.outerPay_1019
  · exact WuPaper.ClassicalFourthNat.outerPay_1020
  · exact WuPaper.ClassicalFourthNat.outerPay_1021
  · exact WuPaper.ClassicalFourthNat.outerPay_1022
  · exact WuPaper.ClassicalFourthNat.outerPay_1023
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.outerPay_block_015
