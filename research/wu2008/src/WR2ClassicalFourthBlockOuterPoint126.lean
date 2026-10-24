import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatOuterPoint126
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem OuterPoint_block_126 (j : Fin 64) (hj : 64*126+j.val < 10541) :
    OuterPoint (64*126+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8064
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8065
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8066
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8067
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8068
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8069
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8070
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8071
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8072
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8073
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8074
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8075
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8076
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8077
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8078
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8079
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8080
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8081
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8082
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8083
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8084
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8085
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8086
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8087
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8088
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8089
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8090
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8091
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8092
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8093
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8094
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8095
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8096
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8097
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8098
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8099
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8100
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8101
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8102
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8103
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8104
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8105
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8106
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8107
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8108
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8109
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8110
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8111
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8112
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8113
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8114
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8115
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8116
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8117
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8118
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8119
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8120
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8121
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8122
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8123
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8124
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8125
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8126
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8127
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.OuterPoint_block_126
