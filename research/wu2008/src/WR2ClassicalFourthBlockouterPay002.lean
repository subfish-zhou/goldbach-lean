import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatouterPay002
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem outerPay_block_002 (j : Fin 64) (hj : 64*2+j.val < 10540) :
    OuterPay (64*2+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.outerPay_128
  · exact WuPaper.ClassicalFourthNat.outerPay_129
  · exact WuPaper.ClassicalFourthNat.outerPay_130
  · exact WuPaper.ClassicalFourthNat.outerPay_131
  · exact WuPaper.ClassicalFourthNat.outerPay_132
  · exact WuPaper.ClassicalFourthNat.outerPay_133
  · exact WuPaper.ClassicalFourthNat.outerPay_134
  · exact WuPaper.ClassicalFourthNat.outerPay_135
  · exact WuPaper.ClassicalFourthNat.outerPay_136
  · exact WuPaper.ClassicalFourthNat.outerPay_137
  · exact WuPaper.ClassicalFourthNat.outerPay_138
  · exact WuPaper.ClassicalFourthNat.outerPay_139
  · exact WuPaper.ClassicalFourthNat.outerPay_140
  · exact WuPaper.ClassicalFourthNat.outerPay_141
  · exact WuPaper.ClassicalFourthNat.outerPay_142
  · exact WuPaper.ClassicalFourthNat.outerPay_143
  · exact WuPaper.ClassicalFourthNat.outerPay_144
  · exact WuPaper.ClassicalFourthNat.outerPay_145
  · exact WuPaper.ClassicalFourthNat.outerPay_146
  · exact WuPaper.ClassicalFourthNat.outerPay_147
  · exact WuPaper.ClassicalFourthNat.outerPay_148
  · exact WuPaper.ClassicalFourthNat.outerPay_149
  · exact WuPaper.ClassicalFourthNat.outerPay_150
  · exact WuPaper.ClassicalFourthNat.outerPay_151
  · exact WuPaper.ClassicalFourthNat.outerPay_152
  · exact WuPaper.ClassicalFourthNat.outerPay_153
  · exact WuPaper.ClassicalFourthNat.outerPay_154
  · exact WuPaper.ClassicalFourthNat.outerPay_155
  · exact WuPaper.ClassicalFourthNat.outerPay_156
  · exact WuPaper.ClassicalFourthNat.outerPay_157
  · exact WuPaper.ClassicalFourthNat.outerPay_158
  · exact WuPaper.ClassicalFourthNat.outerPay_159
  · exact WuPaper.ClassicalFourthNat.outerPay_160
  · exact WuPaper.ClassicalFourthNat.outerPay_161
  · exact WuPaper.ClassicalFourthNat.outerPay_162
  · exact WuPaper.ClassicalFourthNat.outerPay_163
  · exact WuPaper.ClassicalFourthNat.outerPay_164
  · exact WuPaper.ClassicalFourthNat.outerPay_165
  · exact WuPaper.ClassicalFourthNat.outerPay_166
  · exact WuPaper.ClassicalFourthNat.outerPay_167
  · exact WuPaper.ClassicalFourthNat.outerPay_168
  · exact WuPaper.ClassicalFourthNat.outerPay_169
  · exact WuPaper.ClassicalFourthNat.outerPay_170
  · exact WuPaper.ClassicalFourthNat.outerPay_171
  · exact WuPaper.ClassicalFourthNat.outerPay_172
  · exact WuPaper.ClassicalFourthNat.outerPay_173
  · exact WuPaper.ClassicalFourthNat.outerPay_174
  · exact WuPaper.ClassicalFourthNat.outerPay_175
  · exact WuPaper.ClassicalFourthNat.outerPay_176
  · exact WuPaper.ClassicalFourthNat.outerPay_177
  · exact WuPaper.ClassicalFourthNat.outerPay_178
  · exact WuPaper.ClassicalFourthNat.outerPay_179
  · exact WuPaper.ClassicalFourthNat.outerPay_180
  · exact WuPaper.ClassicalFourthNat.outerPay_181
  · exact WuPaper.ClassicalFourthNat.outerPay_182
  · exact WuPaper.ClassicalFourthNat.outerPay_183
  · exact WuPaper.ClassicalFourthNat.outerPay_184
  · exact WuPaper.ClassicalFourthNat.outerPay_185
  · exact WuPaper.ClassicalFourthNat.outerPay_186
  · exact WuPaper.ClassicalFourthNat.outerPay_187
  · exact WuPaper.ClassicalFourthNat.outerPay_188
  · exact WuPaper.ClassicalFourthNat.outerPay_189
  · exact WuPaper.ClassicalFourthNat.outerPay_190
  · exact WuPaper.ClassicalFourthNat.outerPay_191
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.outerPay_block_002
