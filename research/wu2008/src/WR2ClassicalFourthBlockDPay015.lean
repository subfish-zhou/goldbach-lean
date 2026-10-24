import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatDPay015
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem DPay_block_015 (j : Fin 64) (hj : 64*15+j.val < 2540) :
    DPay (64*15+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.DPay_960
  · exact WuPaper.ClassicalFourthNat.DPay_961
  · exact WuPaper.ClassicalFourthNat.DPay_962
  · exact WuPaper.ClassicalFourthNat.DPay_963
  · exact WuPaper.ClassicalFourthNat.DPay_964
  · exact WuPaper.ClassicalFourthNat.DPay_965
  · exact WuPaper.ClassicalFourthNat.DPay_966
  · exact WuPaper.ClassicalFourthNat.DPay_967
  · exact WuPaper.ClassicalFourthNat.DPay_968
  · exact WuPaper.ClassicalFourthNat.DPay_969
  · exact WuPaper.ClassicalFourthNat.DPay_970
  · exact WuPaper.ClassicalFourthNat.DPay_971
  · exact WuPaper.ClassicalFourthNat.DPay_972
  · exact WuPaper.ClassicalFourthNat.DPay_973
  · exact WuPaper.ClassicalFourthNat.DPay_974
  · exact WuPaper.ClassicalFourthNat.DPay_975
  · exact WuPaper.ClassicalFourthNat.DPay_976
  · exact WuPaper.ClassicalFourthNat.DPay_977
  · exact WuPaper.ClassicalFourthNat.DPay_978
  · exact WuPaper.ClassicalFourthNat.DPay_979
  · exact WuPaper.ClassicalFourthNat.DPay_980
  · exact WuPaper.ClassicalFourthNat.DPay_981
  · exact WuPaper.ClassicalFourthNat.DPay_982
  · exact WuPaper.ClassicalFourthNat.DPay_983
  · exact WuPaper.ClassicalFourthNat.DPay_984
  · exact WuPaper.ClassicalFourthNat.DPay_985
  · exact WuPaper.ClassicalFourthNat.DPay_986
  · exact WuPaper.ClassicalFourthNat.DPay_987
  · exact WuPaper.ClassicalFourthNat.DPay_988
  · exact WuPaper.ClassicalFourthNat.DPay_989
  · exact WuPaper.ClassicalFourthNat.DPay_990
  · exact WuPaper.ClassicalFourthNat.DPay_991
  · exact WuPaper.ClassicalFourthNat.DPay_992
  · exact WuPaper.ClassicalFourthNat.DPay_993
  · exact WuPaper.ClassicalFourthNat.DPay_994
  · exact WuPaper.ClassicalFourthNat.DPay_995
  · exact WuPaper.ClassicalFourthNat.DPay_996
  · exact WuPaper.ClassicalFourthNat.DPay_997
  · exact WuPaper.ClassicalFourthNat.DPay_998
  · exact WuPaper.ClassicalFourthNat.DPay_999
  · exact WuPaper.ClassicalFourthNat.DPay_1000
  · exact WuPaper.ClassicalFourthNat.DPay_1001
  · exact WuPaper.ClassicalFourthNat.DPay_1002
  · exact WuPaper.ClassicalFourthNat.DPay_1003
  · exact WuPaper.ClassicalFourthNat.DPay_1004
  · exact WuPaper.ClassicalFourthNat.DPay_1005
  · exact WuPaper.ClassicalFourthNat.DPay_1006
  · exact WuPaper.ClassicalFourthNat.DPay_1007
  · exact WuPaper.ClassicalFourthNat.DPay_1008
  · exact WuPaper.ClassicalFourthNat.DPay_1009
  · exact WuPaper.ClassicalFourthNat.DPay_1010
  · exact WuPaper.ClassicalFourthNat.DPay_1011
  · exact WuPaper.ClassicalFourthNat.DPay_1012
  · exact WuPaper.ClassicalFourthNat.DPay_1013
  · exact WuPaper.ClassicalFourthNat.DPay_1014
  · exact WuPaper.ClassicalFourthNat.DPay_1015
  · exact WuPaper.ClassicalFourthNat.DPay_1016
  · exact WuPaper.ClassicalFourthNat.DPay_1017
  · exact WuPaper.ClassicalFourthNat.DPay_1018
  · exact WuPaper.ClassicalFourthNat.DPay_1019
  · exact WuPaper.ClassicalFourthNat.DPay_1020
  · exact WuPaper.ClassicalFourthNat.DPay_1021
  · exact WuPaper.ClassicalFourthNat.DPay_1022
  · exact WuPaper.ClassicalFourthNat.DPay_1023
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.DPay_block_015
