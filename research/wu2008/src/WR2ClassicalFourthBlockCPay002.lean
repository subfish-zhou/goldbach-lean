import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatCPay002
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem CPay_block_002 (j : Fin 64) (hj : 64*2+j.val < 2540) :
    CPay (64*2+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.CPay_128
  · exact WuPaper.ClassicalFourthNat.CPay_129
  · exact WuPaper.ClassicalFourthNat.CPay_130
  · exact WuPaper.ClassicalFourthNat.CPay_131
  · exact WuPaper.ClassicalFourthNat.CPay_132
  · exact WuPaper.ClassicalFourthNat.CPay_133
  · exact WuPaper.ClassicalFourthNat.CPay_134
  · exact WuPaper.ClassicalFourthNat.CPay_135
  · exact WuPaper.ClassicalFourthNat.CPay_136
  · exact WuPaper.ClassicalFourthNat.CPay_137
  · exact WuPaper.ClassicalFourthNat.CPay_138
  · exact WuPaper.ClassicalFourthNat.CPay_139
  · exact WuPaper.ClassicalFourthNat.CPay_140
  · exact WuPaper.ClassicalFourthNat.CPay_141
  · exact WuPaper.ClassicalFourthNat.CPay_142
  · exact WuPaper.ClassicalFourthNat.CPay_143
  · exact WuPaper.ClassicalFourthNat.CPay_144
  · exact WuPaper.ClassicalFourthNat.CPay_145
  · exact WuPaper.ClassicalFourthNat.CPay_146
  · exact WuPaper.ClassicalFourthNat.CPay_147
  · exact WuPaper.ClassicalFourthNat.CPay_148
  · exact WuPaper.ClassicalFourthNat.CPay_149
  · exact WuPaper.ClassicalFourthNat.CPay_150
  · exact WuPaper.ClassicalFourthNat.CPay_151
  · exact WuPaper.ClassicalFourthNat.CPay_152
  · exact WuPaper.ClassicalFourthNat.CPay_153
  · exact WuPaper.ClassicalFourthNat.CPay_154
  · exact WuPaper.ClassicalFourthNat.CPay_155
  · exact WuPaper.ClassicalFourthNat.CPay_156
  · exact WuPaper.ClassicalFourthNat.CPay_157
  · exact WuPaper.ClassicalFourthNat.CPay_158
  · exact WuPaper.ClassicalFourthNat.CPay_159
  · exact WuPaper.ClassicalFourthNat.CPay_160
  · exact WuPaper.ClassicalFourthNat.CPay_161
  · exact WuPaper.ClassicalFourthNat.CPay_162
  · exact WuPaper.ClassicalFourthNat.CPay_163
  · exact WuPaper.ClassicalFourthNat.CPay_164
  · exact WuPaper.ClassicalFourthNat.CPay_165
  · exact WuPaper.ClassicalFourthNat.CPay_166
  · exact WuPaper.ClassicalFourthNat.CPay_167
  · exact WuPaper.ClassicalFourthNat.CPay_168
  · exact WuPaper.ClassicalFourthNat.CPay_169
  · exact WuPaper.ClassicalFourthNat.CPay_170
  · exact WuPaper.ClassicalFourthNat.CPay_171
  · exact WuPaper.ClassicalFourthNat.CPay_172
  · exact WuPaper.ClassicalFourthNat.CPay_173
  · exact WuPaper.ClassicalFourthNat.CPay_174
  · exact WuPaper.ClassicalFourthNat.CPay_175
  · exact WuPaper.ClassicalFourthNat.CPay_176
  · exact WuPaper.ClassicalFourthNat.CPay_177
  · exact WuPaper.ClassicalFourthNat.CPay_178
  · exact WuPaper.ClassicalFourthNat.CPay_179
  · exact WuPaper.ClassicalFourthNat.CPay_180
  · exact WuPaper.ClassicalFourthNat.CPay_181
  · exact WuPaper.ClassicalFourthNat.CPay_182
  · exact WuPaper.ClassicalFourthNat.CPay_183
  · exact WuPaper.ClassicalFourthNat.CPay_184
  · exact WuPaper.ClassicalFourthNat.CPay_185
  · exact WuPaper.ClassicalFourthNat.CPay_186
  · exact WuPaper.ClassicalFourthNat.CPay_187
  · exact WuPaper.ClassicalFourthNat.CPay_188
  · exact WuPaper.ClassicalFourthNat.CPay_189
  · exact WuPaper.ClassicalFourthNat.CPay_190
  · exact WuPaper.ClassicalFourthNat.CPay_191
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.CPay_block_002
