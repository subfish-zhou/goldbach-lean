import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatouterPay110
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem outerPay_block_110 (j : Fin 64) (hj : 64*110+j.val < 10540) :
    OuterPay (64*110+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.outerPay_7040
  · exact WuPaper.ClassicalFourthNat.outerPay_7041
  · exact WuPaper.ClassicalFourthNat.outerPay_7042
  · exact WuPaper.ClassicalFourthNat.outerPay_7043
  · exact WuPaper.ClassicalFourthNat.outerPay_7044
  · exact WuPaper.ClassicalFourthNat.outerPay_7045
  · exact WuPaper.ClassicalFourthNat.outerPay_7046
  · exact WuPaper.ClassicalFourthNat.outerPay_7047
  · exact WuPaper.ClassicalFourthNat.outerPay_7048
  · exact WuPaper.ClassicalFourthNat.outerPay_7049
  · exact WuPaper.ClassicalFourthNat.outerPay_7050
  · exact WuPaper.ClassicalFourthNat.outerPay_7051
  · exact WuPaper.ClassicalFourthNat.outerPay_7052
  · exact WuPaper.ClassicalFourthNat.outerPay_7053
  · exact WuPaper.ClassicalFourthNat.outerPay_7054
  · exact WuPaper.ClassicalFourthNat.outerPay_7055
  · exact WuPaper.ClassicalFourthNat.outerPay_7056
  · exact WuPaper.ClassicalFourthNat.outerPay_7057
  · exact WuPaper.ClassicalFourthNat.outerPay_7058
  · exact WuPaper.ClassicalFourthNat.outerPay_7059
  · exact WuPaper.ClassicalFourthNat.outerPay_7060
  · exact WuPaper.ClassicalFourthNat.outerPay_7061
  · exact WuPaper.ClassicalFourthNat.outerPay_7062
  · exact WuPaper.ClassicalFourthNat.outerPay_7063
  · exact WuPaper.ClassicalFourthNat.outerPay_7064
  · exact WuPaper.ClassicalFourthNat.outerPay_7065
  · exact WuPaper.ClassicalFourthNat.outerPay_7066
  · exact WuPaper.ClassicalFourthNat.outerPay_7067
  · exact WuPaper.ClassicalFourthNat.outerPay_7068
  · exact WuPaper.ClassicalFourthNat.outerPay_7069
  · exact WuPaper.ClassicalFourthNat.outerPay_7070
  · exact WuPaper.ClassicalFourthNat.outerPay_7071
  · exact WuPaper.ClassicalFourthNat.outerPay_7072
  · exact WuPaper.ClassicalFourthNat.outerPay_7073
  · exact WuPaper.ClassicalFourthNat.outerPay_7074
  · exact WuPaper.ClassicalFourthNat.outerPay_7075
  · exact WuPaper.ClassicalFourthNat.outerPay_7076
  · exact WuPaper.ClassicalFourthNat.outerPay_7077
  · exact WuPaper.ClassicalFourthNat.outerPay_7078
  · exact WuPaper.ClassicalFourthNat.outerPay_7079
  · exact WuPaper.ClassicalFourthNat.outerPay_7080
  · exact WuPaper.ClassicalFourthNat.outerPay_7081
  · exact WuPaper.ClassicalFourthNat.outerPay_7082
  · exact WuPaper.ClassicalFourthNat.outerPay_7083
  · exact WuPaper.ClassicalFourthNat.outerPay_7084
  · exact WuPaper.ClassicalFourthNat.outerPay_7085
  · exact WuPaper.ClassicalFourthNat.outerPay_7086
  · exact WuPaper.ClassicalFourthNat.outerPay_7087
  · exact WuPaper.ClassicalFourthNat.outerPay_7088
  · exact WuPaper.ClassicalFourthNat.outerPay_7089
  · exact WuPaper.ClassicalFourthNat.outerPay_7090
  · exact WuPaper.ClassicalFourthNat.outerPay_7091
  · exact WuPaper.ClassicalFourthNat.outerPay_7092
  · exact WuPaper.ClassicalFourthNat.outerPay_7093
  · exact WuPaper.ClassicalFourthNat.outerPay_7094
  · exact WuPaper.ClassicalFourthNat.outerPay_7095
  · exact WuPaper.ClassicalFourthNat.outerPay_7096
  · exact WuPaper.ClassicalFourthNat.outerPay_7097
  · exact WuPaper.ClassicalFourthNat.outerPay_7098
  · exact WuPaper.ClassicalFourthNat.outerPay_7099
  · exact WuPaper.ClassicalFourthNat.outerPay_7100
  · exact WuPaper.ClassicalFourthNat.outerPay_7101
  · exact WuPaper.ClassicalFourthNat.outerPay_7102
  · exact WuPaper.ClassicalFourthNat.outerPay_7103
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.outerPay_block_110
