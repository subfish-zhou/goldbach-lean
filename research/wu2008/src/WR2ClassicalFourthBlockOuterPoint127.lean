import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatOuterPoint127
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem OuterPoint_block_127 (j : Fin 64) (hj : 64*127+j.val < 10541) :
    OuterPoint (64*127+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8128
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8129
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8130
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8131
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8132
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8133
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8134
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8135
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8136
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8137
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8138
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8139
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8140
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8141
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8142
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8143
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8144
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8145
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8146
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8147
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8148
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8149
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8150
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8151
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8152
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8153
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8154
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8155
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8156
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8157
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8158
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8159
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8160
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8161
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8162
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8163
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8164
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8165
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8166
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8167
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8168
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8169
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8170
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8171
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8172
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8173
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8174
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8175
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8176
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8177
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8178
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8179
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8180
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8181
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8182
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8183
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8184
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8185
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8186
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8187
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8188
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8189
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8190
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8191
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.OuterPoint_block_127
