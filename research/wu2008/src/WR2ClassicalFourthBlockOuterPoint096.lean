import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatOuterPoint096
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem OuterPoint_block_096 (j : Fin 64) (hj : 64*96+j.val < 10541) :
    OuterPoint (64*96+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6144
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6145
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6146
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6147
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6148
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6149
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6150
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6151
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6152
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6153
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6154
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6155
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6156
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6157
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6158
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6159
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6160
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6161
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6162
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6163
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6164
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6165
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6166
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6167
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6168
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6169
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6170
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6171
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6172
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6173
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6174
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6175
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6176
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6177
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6178
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6179
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6180
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6181
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6182
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6183
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6184
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6185
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6186
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6187
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6188
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6189
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6190
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6191
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6192
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6193
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6194
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6195
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6196
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6197
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6198
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6199
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6200
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6201
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6202
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6203
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6204
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6205
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6206
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6207
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.OuterPoint_block_096
