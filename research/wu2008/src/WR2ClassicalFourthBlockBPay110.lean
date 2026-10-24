import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay110
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_110 (j : Fin 64) (hj : 64*110+j.val < 10540) :
    BPay (64*110+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_7040
  · exact WuPaper.ClassicalFourthNat.BPay_7041
  · exact WuPaper.ClassicalFourthNat.BPay_7042
  · exact WuPaper.ClassicalFourthNat.BPay_7043
  · exact WuPaper.ClassicalFourthNat.BPay_7044
  · exact WuPaper.ClassicalFourthNat.BPay_7045
  · exact WuPaper.ClassicalFourthNat.BPay_7046
  · exact WuPaper.ClassicalFourthNat.BPay_7047
  · exact WuPaper.ClassicalFourthNat.BPay_7048
  · exact WuPaper.ClassicalFourthNat.BPay_7049
  · exact WuPaper.ClassicalFourthNat.BPay_7050
  · exact WuPaper.ClassicalFourthNat.BPay_7051
  · exact WuPaper.ClassicalFourthNat.BPay_7052
  · exact WuPaper.ClassicalFourthNat.BPay_7053
  · exact WuPaper.ClassicalFourthNat.BPay_7054
  · exact WuPaper.ClassicalFourthNat.BPay_7055
  · exact WuPaper.ClassicalFourthNat.BPay_7056
  · exact WuPaper.ClassicalFourthNat.BPay_7057
  · exact WuPaper.ClassicalFourthNat.BPay_7058
  · exact WuPaper.ClassicalFourthNat.BPay_7059
  · exact WuPaper.ClassicalFourthNat.BPay_7060
  · exact WuPaper.ClassicalFourthNat.BPay_7061
  · exact WuPaper.ClassicalFourthNat.BPay_7062
  · exact WuPaper.ClassicalFourthNat.BPay_7063
  · exact WuPaper.ClassicalFourthNat.BPay_7064
  · exact WuPaper.ClassicalFourthNat.BPay_7065
  · exact WuPaper.ClassicalFourthNat.BPay_7066
  · exact WuPaper.ClassicalFourthNat.BPay_7067
  · exact WuPaper.ClassicalFourthNat.BPay_7068
  · exact WuPaper.ClassicalFourthNat.BPay_7069
  · exact WuPaper.ClassicalFourthNat.BPay_7070
  · exact WuPaper.ClassicalFourthNat.BPay_7071
  · exact WuPaper.ClassicalFourthNat.BPay_7072
  · exact WuPaper.ClassicalFourthNat.BPay_7073
  · exact WuPaper.ClassicalFourthNat.BPay_7074
  · exact WuPaper.ClassicalFourthNat.BPay_7075
  · exact WuPaper.ClassicalFourthNat.BPay_7076
  · exact WuPaper.ClassicalFourthNat.BPay_7077
  · exact WuPaper.ClassicalFourthNat.BPay_7078
  · exact WuPaper.ClassicalFourthNat.BPay_7079
  · exact WuPaper.ClassicalFourthNat.BPay_7080
  · exact WuPaper.ClassicalFourthNat.BPay_7081
  · exact WuPaper.ClassicalFourthNat.BPay_7082
  · exact WuPaper.ClassicalFourthNat.BPay_7083
  · exact WuPaper.ClassicalFourthNat.BPay_7084
  · exact WuPaper.ClassicalFourthNat.BPay_7085
  · exact WuPaper.ClassicalFourthNat.BPay_7086
  · exact WuPaper.ClassicalFourthNat.BPay_7087
  · exact WuPaper.ClassicalFourthNat.BPay_7088
  · exact WuPaper.ClassicalFourthNat.BPay_7089
  · exact WuPaper.ClassicalFourthNat.BPay_7090
  · exact WuPaper.ClassicalFourthNat.BPay_7091
  · exact WuPaper.ClassicalFourthNat.BPay_7092
  · exact WuPaper.ClassicalFourthNat.BPay_7093
  · exact WuPaper.ClassicalFourthNat.BPay_7094
  · exact WuPaper.ClassicalFourthNat.BPay_7095
  · exact WuPaper.ClassicalFourthNat.BPay_7096
  · exact WuPaper.ClassicalFourthNat.BPay_7097
  · exact WuPaper.ClassicalFourthNat.BPay_7098
  · exact WuPaper.ClassicalFourthNat.BPay_7099
  · exact WuPaper.ClassicalFourthNat.BPay_7100
  · exact WuPaper.ClassicalFourthNat.BPay_7101
  · exact WuPaper.ClassicalFourthNat.BPay_7102
  · exact WuPaper.ClassicalFourthNat.BPay_7103
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_110
