import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatOuterPoint002
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem OuterPoint_block_002 (j : Fin 64) (hj : 64*2+j.val < 10541) :
    OuterPoint (64*2+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.OuterPoint_128
  · exact WuPaper.ClassicalFourthNat.OuterPoint_129
  · exact WuPaper.ClassicalFourthNat.OuterPoint_130
  · exact WuPaper.ClassicalFourthNat.OuterPoint_131
  · exact WuPaper.ClassicalFourthNat.OuterPoint_132
  · exact WuPaper.ClassicalFourthNat.OuterPoint_133
  · exact WuPaper.ClassicalFourthNat.OuterPoint_134
  · exact WuPaper.ClassicalFourthNat.OuterPoint_135
  · exact WuPaper.ClassicalFourthNat.OuterPoint_136
  · exact WuPaper.ClassicalFourthNat.OuterPoint_137
  · exact WuPaper.ClassicalFourthNat.OuterPoint_138
  · exact WuPaper.ClassicalFourthNat.OuterPoint_139
  · exact WuPaper.ClassicalFourthNat.OuterPoint_140
  · exact WuPaper.ClassicalFourthNat.OuterPoint_141
  · exact WuPaper.ClassicalFourthNat.OuterPoint_142
  · exact WuPaper.ClassicalFourthNat.OuterPoint_143
  · exact WuPaper.ClassicalFourthNat.OuterPoint_144
  · exact WuPaper.ClassicalFourthNat.OuterPoint_145
  · exact WuPaper.ClassicalFourthNat.OuterPoint_146
  · exact WuPaper.ClassicalFourthNat.OuterPoint_147
  · exact WuPaper.ClassicalFourthNat.OuterPoint_148
  · exact WuPaper.ClassicalFourthNat.OuterPoint_149
  · exact WuPaper.ClassicalFourthNat.OuterPoint_150
  · exact WuPaper.ClassicalFourthNat.OuterPoint_151
  · exact WuPaper.ClassicalFourthNat.OuterPoint_152
  · exact WuPaper.ClassicalFourthNat.OuterPoint_153
  · exact WuPaper.ClassicalFourthNat.OuterPoint_154
  · exact WuPaper.ClassicalFourthNat.OuterPoint_155
  · exact WuPaper.ClassicalFourthNat.OuterPoint_156
  · exact WuPaper.ClassicalFourthNat.OuterPoint_157
  · exact WuPaper.ClassicalFourthNat.OuterPoint_158
  · exact WuPaper.ClassicalFourthNat.OuterPoint_159
  · exact WuPaper.ClassicalFourthNat.OuterPoint_160
  · exact WuPaper.ClassicalFourthNat.OuterPoint_161
  · exact WuPaper.ClassicalFourthNat.OuterPoint_162
  · exact WuPaper.ClassicalFourthNat.OuterPoint_163
  · exact WuPaper.ClassicalFourthNat.OuterPoint_164
  · exact WuPaper.ClassicalFourthNat.OuterPoint_165
  · exact WuPaper.ClassicalFourthNat.OuterPoint_166
  · exact WuPaper.ClassicalFourthNat.OuterPoint_167
  · exact WuPaper.ClassicalFourthNat.OuterPoint_168
  · exact WuPaper.ClassicalFourthNat.OuterPoint_169
  · exact WuPaper.ClassicalFourthNat.OuterPoint_170
  · exact WuPaper.ClassicalFourthNat.OuterPoint_171
  · exact WuPaper.ClassicalFourthNat.OuterPoint_172
  · exact WuPaper.ClassicalFourthNat.OuterPoint_173
  · exact WuPaper.ClassicalFourthNat.OuterPoint_174
  · exact WuPaper.ClassicalFourthNat.OuterPoint_175
  · exact WuPaper.ClassicalFourthNat.OuterPoint_176
  · exact WuPaper.ClassicalFourthNat.OuterPoint_177
  · exact WuPaper.ClassicalFourthNat.OuterPoint_178
  · exact WuPaper.ClassicalFourthNat.OuterPoint_179
  · exact WuPaper.ClassicalFourthNat.OuterPoint_180
  · exact WuPaper.ClassicalFourthNat.OuterPoint_181
  · exact WuPaper.ClassicalFourthNat.OuterPoint_182
  · exact WuPaper.ClassicalFourthNat.OuterPoint_183
  · exact WuPaper.ClassicalFourthNat.OuterPoint_184
  · exact WuPaper.ClassicalFourthNat.OuterPoint_185
  · exact WuPaper.ClassicalFourthNat.OuterPoint_186
  · exact WuPaper.ClassicalFourthNat.OuterPoint_187
  · exact WuPaper.ClassicalFourthNat.OuterPoint_188
  · exact WuPaper.ClassicalFourthNat.OuterPoint_189
  · exact WuPaper.ClassicalFourthNat.OuterPoint_190
  · exact WuPaper.ClassicalFourthNat.OuterPoint_191
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.OuterPoint_block_002
