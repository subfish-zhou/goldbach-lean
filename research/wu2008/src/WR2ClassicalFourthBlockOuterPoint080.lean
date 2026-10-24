import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatOuterPoint080
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem OuterPoint_block_080 (j : Fin 64) (hj : 64*80+j.val < 10541) :
    OuterPoint (64*80+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.OuterPoint_5120
  · exact WuPaper.ClassicalFourthNat.OuterPoint_5121
  · exact WuPaper.ClassicalFourthNat.OuterPoint_5122
  · exact WuPaper.ClassicalFourthNat.OuterPoint_5123
  · exact WuPaper.ClassicalFourthNat.OuterPoint_5124
  · exact WuPaper.ClassicalFourthNat.OuterPoint_5125
  · exact WuPaper.ClassicalFourthNat.OuterPoint_5126
  · exact WuPaper.ClassicalFourthNat.OuterPoint_5127
  · exact WuPaper.ClassicalFourthNat.OuterPoint_5128
  · exact WuPaper.ClassicalFourthNat.OuterPoint_5129
  · exact WuPaper.ClassicalFourthNat.OuterPoint_5130
  · exact WuPaper.ClassicalFourthNat.OuterPoint_5131
  · exact WuPaper.ClassicalFourthNat.OuterPoint_5132
  · exact WuPaper.ClassicalFourthNat.OuterPoint_5133
  · exact WuPaper.ClassicalFourthNat.OuterPoint_5134
  · exact WuPaper.ClassicalFourthNat.OuterPoint_5135
  · exact WuPaper.ClassicalFourthNat.OuterPoint_5136
  · exact WuPaper.ClassicalFourthNat.OuterPoint_5137
  · exact WuPaper.ClassicalFourthNat.OuterPoint_5138
  · exact WuPaper.ClassicalFourthNat.OuterPoint_5139
  · exact WuPaper.ClassicalFourthNat.OuterPoint_5140
  · exact WuPaper.ClassicalFourthNat.OuterPoint_5141
  · exact WuPaper.ClassicalFourthNat.OuterPoint_5142
  · exact WuPaper.ClassicalFourthNat.OuterPoint_5143
  · exact WuPaper.ClassicalFourthNat.OuterPoint_5144
  · exact WuPaper.ClassicalFourthNat.OuterPoint_5145
  · exact WuPaper.ClassicalFourthNat.OuterPoint_5146
  · exact WuPaper.ClassicalFourthNat.OuterPoint_5147
  · exact WuPaper.ClassicalFourthNat.OuterPoint_5148
  · exact WuPaper.ClassicalFourthNat.OuterPoint_5149
  · exact WuPaper.ClassicalFourthNat.OuterPoint_5150
  · exact WuPaper.ClassicalFourthNat.OuterPoint_5151
  · exact WuPaper.ClassicalFourthNat.OuterPoint_5152
  · exact WuPaper.ClassicalFourthNat.OuterPoint_5153
  · exact WuPaper.ClassicalFourthNat.OuterPoint_5154
  · exact WuPaper.ClassicalFourthNat.OuterPoint_5155
  · exact WuPaper.ClassicalFourthNat.OuterPoint_5156
  · exact WuPaper.ClassicalFourthNat.OuterPoint_5157
  · exact WuPaper.ClassicalFourthNat.OuterPoint_5158
  · exact WuPaper.ClassicalFourthNat.OuterPoint_5159
  · exact WuPaper.ClassicalFourthNat.OuterPoint_5160
  · exact WuPaper.ClassicalFourthNat.OuterPoint_5161
  · exact WuPaper.ClassicalFourthNat.OuterPoint_5162
  · exact WuPaper.ClassicalFourthNat.OuterPoint_5163
  · exact WuPaper.ClassicalFourthNat.OuterPoint_5164
  · exact WuPaper.ClassicalFourthNat.OuterPoint_5165
  · exact WuPaper.ClassicalFourthNat.OuterPoint_5166
  · exact WuPaper.ClassicalFourthNat.OuterPoint_5167
  · exact WuPaper.ClassicalFourthNat.OuterPoint_5168
  · exact WuPaper.ClassicalFourthNat.OuterPoint_5169
  · exact WuPaper.ClassicalFourthNat.OuterPoint_5170
  · exact WuPaper.ClassicalFourthNat.OuterPoint_5171
  · exact WuPaper.ClassicalFourthNat.OuterPoint_5172
  · exact WuPaper.ClassicalFourthNat.OuterPoint_5173
  · exact WuPaper.ClassicalFourthNat.OuterPoint_5174
  · exact WuPaper.ClassicalFourthNat.OuterPoint_5175
  · exact WuPaper.ClassicalFourthNat.OuterPoint_5176
  · exact WuPaper.ClassicalFourthNat.OuterPoint_5177
  · exact WuPaper.ClassicalFourthNat.OuterPoint_5178
  · exact WuPaper.ClassicalFourthNat.OuterPoint_5179
  · exact WuPaper.ClassicalFourthNat.OuterPoint_5180
  · exact WuPaper.ClassicalFourthNat.OuterPoint_5181
  · exact WuPaper.ClassicalFourthNat.OuterPoint_5182
  · exact WuPaper.ClassicalFourthNat.OuterPoint_5183
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.OuterPoint_block_080
