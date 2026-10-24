import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatOuterPoint110
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem OuterPoint_block_110 (j : Fin 64) (hj : 64*110+j.val < 10541) :
    OuterPoint (64*110+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7040
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7041
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7042
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7043
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7044
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7045
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7046
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7047
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7048
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7049
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7050
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7051
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7052
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7053
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7054
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7055
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7056
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7057
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7058
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7059
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7060
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7061
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7062
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7063
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7064
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7065
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7066
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7067
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7068
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7069
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7070
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7071
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7072
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7073
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7074
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7075
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7076
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7077
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7078
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7079
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7080
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7081
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7082
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7083
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7084
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7085
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7086
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7087
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7088
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7089
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7090
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7091
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7092
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7093
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7094
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7095
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7096
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7097
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7098
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7099
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7100
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7101
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7102
  · exact WuPaper.ClassicalFourthNat.OuterPoint_7103
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.OuterPoint_block_110
