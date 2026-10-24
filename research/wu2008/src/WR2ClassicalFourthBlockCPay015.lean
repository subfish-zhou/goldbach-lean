import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatCPay015
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem CPay_block_015 (j : Fin 64) (hj : 64*15+j.val < 2540) :
    CPay (64*15+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.CPay_960
  · exact WuPaper.ClassicalFourthNat.CPay_961
  · exact WuPaper.ClassicalFourthNat.CPay_962
  · exact WuPaper.ClassicalFourthNat.CPay_963
  · exact WuPaper.ClassicalFourthNat.CPay_964
  · exact WuPaper.ClassicalFourthNat.CPay_965
  · exact WuPaper.ClassicalFourthNat.CPay_966
  · exact WuPaper.ClassicalFourthNat.CPay_967
  · exact WuPaper.ClassicalFourthNat.CPay_968
  · exact WuPaper.ClassicalFourthNat.CPay_969
  · exact WuPaper.ClassicalFourthNat.CPay_970
  · exact WuPaper.ClassicalFourthNat.CPay_971
  · exact WuPaper.ClassicalFourthNat.CPay_972
  · exact WuPaper.ClassicalFourthNat.CPay_973
  · exact WuPaper.ClassicalFourthNat.CPay_974
  · exact WuPaper.ClassicalFourthNat.CPay_975
  · exact WuPaper.ClassicalFourthNat.CPay_976
  · exact WuPaper.ClassicalFourthNat.CPay_977
  · exact WuPaper.ClassicalFourthNat.CPay_978
  · exact WuPaper.ClassicalFourthNat.CPay_979
  · exact WuPaper.ClassicalFourthNat.CPay_980
  · exact WuPaper.ClassicalFourthNat.CPay_981
  · exact WuPaper.ClassicalFourthNat.CPay_982
  · exact WuPaper.ClassicalFourthNat.CPay_983
  · exact WuPaper.ClassicalFourthNat.CPay_984
  · exact WuPaper.ClassicalFourthNat.CPay_985
  · exact WuPaper.ClassicalFourthNat.CPay_986
  · exact WuPaper.ClassicalFourthNat.CPay_987
  · exact WuPaper.ClassicalFourthNat.CPay_988
  · exact WuPaper.ClassicalFourthNat.CPay_989
  · exact WuPaper.ClassicalFourthNat.CPay_990
  · exact WuPaper.ClassicalFourthNat.CPay_991
  · exact WuPaper.ClassicalFourthNat.CPay_992
  · exact WuPaper.ClassicalFourthNat.CPay_993
  · exact WuPaper.ClassicalFourthNat.CPay_994
  · exact WuPaper.ClassicalFourthNat.CPay_995
  · exact WuPaper.ClassicalFourthNat.CPay_996
  · exact WuPaper.ClassicalFourthNat.CPay_997
  · exact WuPaper.ClassicalFourthNat.CPay_998
  · exact WuPaper.ClassicalFourthNat.CPay_999
  · exact WuPaper.ClassicalFourthNat.CPay_1000
  · exact WuPaper.ClassicalFourthNat.CPay_1001
  · exact WuPaper.ClassicalFourthNat.CPay_1002
  · exact WuPaper.ClassicalFourthNat.CPay_1003
  · exact WuPaper.ClassicalFourthNat.CPay_1004
  · exact WuPaper.ClassicalFourthNat.CPay_1005
  · exact WuPaper.ClassicalFourthNat.CPay_1006
  · exact WuPaper.ClassicalFourthNat.CPay_1007
  · exact WuPaper.ClassicalFourthNat.CPay_1008
  · exact WuPaper.ClassicalFourthNat.CPay_1009
  · exact WuPaper.ClassicalFourthNat.CPay_1010
  · exact WuPaper.ClassicalFourthNat.CPay_1011
  · exact WuPaper.ClassicalFourthNat.CPay_1012
  · exact WuPaper.ClassicalFourthNat.CPay_1013
  · exact WuPaper.ClassicalFourthNat.CPay_1014
  · exact WuPaper.ClassicalFourthNat.CPay_1015
  · exact WuPaper.ClassicalFourthNat.CPay_1016
  · exact WuPaper.ClassicalFourthNat.CPay_1017
  · exact WuPaper.ClassicalFourthNat.CPay_1018
  · exact WuPaper.ClassicalFourthNat.CPay_1019
  · exact WuPaper.ClassicalFourthNat.CPay_1020
  · exact WuPaper.ClassicalFourthNat.CPay_1021
  · exact WuPaper.ClassicalFourthNat.CPay_1022
  · exact WuPaper.ClassicalFourthNat.CPay_1023
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.CPay_block_015
