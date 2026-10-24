import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatDPay016
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem DPay_block_016 (j : Fin 64) (hj : 64*16+j.val < 2540) :
    DPay (64*16+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.DPay_1024
  · exact WuPaper.ClassicalFourthNat.DPay_1025
  · exact WuPaper.ClassicalFourthNat.DPay_1026
  · exact WuPaper.ClassicalFourthNat.DPay_1027
  · exact WuPaper.ClassicalFourthNat.DPay_1028
  · exact WuPaper.ClassicalFourthNat.DPay_1029
  · exact WuPaper.ClassicalFourthNat.DPay_1030
  · exact WuPaper.ClassicalFourthNat.DPay_1031
  · exact WuPaper.ClassicalFourthNat.DPay_1032
  · exact WuPaper.ClassicalFourthNat.DPay_1033
  · exact WuPaper.ClassicalFourthNat.DPay_1034
  · exact WuPaper.ClassicalFourthNat.DPay_1035
  · exact WuPaper.ClassicalFourthNat.DPay_1036
  · exact WuPaper.ClassicalFourthNat.DPay_1037
  · exact WuPaper.ClassicalFourthNat.DPay_1038
  · exact WuPaper.ClassicalFourthNat.DPay_1039
  · exact WuPaper.ClassicalFourthNat.DPay_1040
  · exact WuPaper.ClassicalFourthNat.DPay_1041
  · exact WuPaper.ClassicalFourthNat.DPay_1042
  · exact WuPaper.ClassicalFourthNat.DPay_1043
  · exact WuPaper.ClassicalFourthNat.DPay_1044
  · exact WuPaper.ClassicalFourthNat.DPay_1045
  · exact WuPaper.ClassicalFourthNat.DPay_1046
  · exact WuPaper.ClassicalFourthNat.DPay_1047
  · exact WuPaper.ClassicalFourthNat.DPay_1048
  · exact WuPaper.ClassicalFourthNat.DPay_1049
  · exact WuPaper.ClassicalFourthNat.DPay_1050
  · exact WuPaper.ClassicalFourthNat.DPay_1051
  · exact WuPaper.ClassicalFourthNat.DPay_1052
  · exact WuPaper.ClassicalFourthNat.DPay_1053
  · exact WuPaper.ClassicalFourthNat.DPay_1054
  · exact WuPaper.ClassicalFourthNat.DPay_1055
  · exact WuPaper.ClassicalFourthNat.DPay_1056
  · exact WuPaper.ClassicalFourthNat.DPay_1057
  · exact WuPaper.ClassicalFourthNat.DPay_1058
  · exact WuPaper.ClassicalFourthNat.DPay_1059
  · exact WuPaper.ClassicalFourthNat.DPay_1060
  · exact WuPaper.ClassicalFourthNat.DPay_1061
  · exact WuPaper.ClassicalFourthNat.DPay_1062
  · exact WuPaper.ClassicalFourthNat.DPay_1063
  · exact WuPaper.ClassicalFourthNat.DPay_1064
  · exact WuPaper.ClassicalFourthNat.DPay_1065
  · exact WuPaper.ClassicalFourthNat.DPay_1066
  · exact WuPaper.ClassicalFourthNat.DPay_1067
  · exact WuPaper.ClassicalFourthNat.DPay_1068
  · exact WuPaper.ClassicalFourthNat.DPay_1069
  · exact WuPaper.ClassicalFourthNat.DPay_1070
  · exact WuPaper.ClassicalFourthNat.DPay_1071
  · exact WuPaper.ClassicalFourthNat.DPay_1072
  · exact WuPaper.ClassicalFourthNat.DPay_1073
  · exact WuPaper.ClassicalFourthNat.DPay_1074
  · exact WuPaper.ClassicalFourthNat.DPay_1075
  · exact WuPaper.ClassicalFourthNat.DPay_1076
  · exact WuPaper.ClassicalFourthNat.DPay_1077
  · exact WuPaper.ClassicalFourthNat.DPay_1078
  · exact WuPaper.ClassicalFourthNat.DPay_1079
  · exact WuPaper.ClassicalFourthNat.DPay_1080
  · exact WuPaper.ClassicalFourthNat.DPay_1081
  · exact WuPaper.ClassicalFourthNat.DPay_1082
  · exact WuPaper.ClassicalFourthNat.DPay_1083
  · exact WuPaper.ClassicalFourthNat.DPay_1084
  · exact WuPaper.ClassicalFourthNat.DPay_1085
  · exact WuPaper.ClassicalFourthNat.DPay_1086
  · exact WuPaper.ClassicalFourthNat.DPay_1087
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.DPay_block_016
