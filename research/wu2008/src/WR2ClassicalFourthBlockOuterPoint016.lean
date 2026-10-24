import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatOuterPoint016
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem OuterPoint_block_016 (j : Fin 64) (hj : 64*16+j.val < 10541) :
    OuterPoint (64*16+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1024
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1025
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1026
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1027
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1028
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1029
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1030
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1031
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1032
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1033
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1034
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1035
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1036
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1037
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1038
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1039
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1040
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1041
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1042
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1043
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1044
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1045
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1046
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1047
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1048
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1049
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1050
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1051
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1052
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1053
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1054
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1055
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1056
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1057
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1058
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1059
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1060
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1061
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1062
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1063
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1064
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1065
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1066
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1067
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1068
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1069
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1070
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1071
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1072
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1073
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1074
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1075
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1076
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1077
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1078
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1079
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1080
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1081
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1082
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1083
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1084
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1085
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1086
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1087
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.OuterPoint_block_016
