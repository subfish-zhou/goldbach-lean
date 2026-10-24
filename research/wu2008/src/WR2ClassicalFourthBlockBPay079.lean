import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay079
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_079 (j : Fin 64) (hj : 64*79+j.val < 10540) :
    BPay (64*79+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_5056
  · exact WuPaper.ClassicalFourthNat.BPay_5057
  · exact WuPaper.ClassicalFourthNat.BPay_5058
  · exact WuPaper.ClassicalFourthNat.BPay_5059
  · exact WuPaper.ClassicalFourthNat.BPay_5060
  · exact WuPaper.ClassicalFourthNat.BPay_5061
  · exact WuPaper.ClassicalFourthNat.BPay_5062
  · exact WuPaper.ClassicalFourthNat.BPay_5063
  · exact WuPaper.ClassicalFourthNat.BPay_5064
  · exact WuPaper.ClassicalFourthNat.BPay_5065
  · exact WuPaper.ClassicalFourthNat.BPay_5066
  · exact WuPaper.ClassicalFourthNat.BPay_5067
  · exact WuPaper.ClassicalFourthNat.BPay_5068
  · exact WuPaper.ClassicalFourthNat.BPay_5069
  · exact WuPaper.ClassicalFourthNat.BPay_5070
  · exact WuPaper.ClassicalFourthNat.BPay_5071
  · exact WuPaper.ClassicalFourthNat.BPay_5072
  · exact WuPaper.ClassicalFourthNat.BPay_5073
  · exact WuPaper.ClassicalFourthNat.BPay_5074
  · exact WuPaper.ClassicalFourthNat.BPay_5075
  · exact WuPaper.ClassicalFourthNat.BPay_5076
  · exact WuPaper.ClassicalFourthNat.BPay_5077
  · exact WuPaper.ClassicalFourthNat.BPay_5078
  · exact WuPaper.ClassicalFourthNat.BPay_5079
  · exact WuPaper.ClassicalFourthNat.BPay_5080
  · exact WuPaper.ClassicalFourthNat.BPay_5081
  · exact WuPaper.ClassicalFourthNat.BPay_5082
  · exact WuPaper.ClassicalFourthNat.BPay_5083
  · exact WuPaper.ClassicalFourthNat.BPay_5084
  · exact WuPaper.ClassicalFourthNat.BPay_5085
  · exact WuPaper.ClassicalFourthNat.BPay_5086
  · exact WuPaper.ClassicalFourthNat.BPay_5087
  · exact WuPaper.ClassicalFourthNat.BPay_5088
  · exact WuPaper.ClassicalFourthNat.BPay_5089
  · exact WuPaper.ClassicalFourthNat.BPay_5090
  · exact WuPaper.ClassicalFourthNat.BPay_5091
  · exact WuPaper.ClassicalFourthNat.BPay_5092
  · exact WuPaper.ClassicalFourthNat.BPay_5093
  · exact WuPaper.ClassicalFourthNat.BPay_5094
  · exact WuPaper.ClassicalFourthNat.BPay_5095
  · exact WuPaper.ClassicalFourthNat.BPay_5096
  · exact WuPaper.ClassicalFourthNat.BPay_5097
  · exact WuPaper.ClassicalFourthNat.BPay_5098
  · exact WuPaper.ClassicalFourthNat.BPay_5099
  · exact WuPaper.ClassicalFourthNat.BPay_5100
  · exact WuPaper.ClassicalFourthNat.BPay_5101
  · exact WuPaper.ClassicalFourthNat.BPay_5102
  · exact WuPaper.ClassicalFourthNat.BPay_5103
  · exact WuPaper.ClassicalFourthNat.BPay_5104
  · exact WuPaper.ClassicalFourthNat.BPay_5105
  · exact WuPaper.ClassicalFourthNat.BPay_5106
  · exact WuPaper.ClassicalFourthNat.BPay_5107
  · exact WuPaper.ClassicalFourthNat.BPay_5108
  · exact WuPaper.ClassicalFourthNat.BPay_5109
  · exact WuPaper.ClassicalFourthNat.BPay_5110
  · exact WuPaper.ClassicalFourthNat.BPay_5111
  · exact WuPaper.ClassicalFourthNat.BPay_5112
  · exact WuPaper.ClassicalFourthNat.BPay_5113
  · exact WuPaper.ClassicalFourthNat.BPay_5114
  · exact WuPaper.ClassicalFourthNat.BPay_5115
  · exact WuPaper.ClassicalFourthNat.BPay_5116
  · exact WuPaper.ClassicalFourthNat.BPay_5117
  · exact WuPaper.ClassicalFourthNat.BPay_5118
  · exact WuPaper.ClassicalFourthNat.BPay_5119
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_079
