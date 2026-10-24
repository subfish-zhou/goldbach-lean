import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay002
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_002 (j : Fin 64) (hj : 64*2+j.val < 10540) :
    BPay (64*2+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_128
  · exact WuPaper.ClassicalFourthNat.BPay_129
  · exact WuPaper.ClassicalFourthNat.BPay_130
  · exact WuPaper.ClassicalFourthNat.BPay_131
  · exact WuPaper.ClassicalFourthNat.BPay_132
  · exact WuPaper.ClassicalFourthNat.BPay_133
  · exact WuPaper.ClassicalFourthNat.BPay_134
  · exact WuPaper.ClassicalFourthNat.BPay_135
  · exact WuPaper.ClassicalFourthNat.BPay_136
  · exact WuPaper.ClassicalFourthNat.BPay_137
  · exact WuPaper.ClassicalFourthNat.BPay_138
  · exact WuPaper.ClassicalFourthNat.BPay_139
  · exact WuPaper.ClassicalFourthNat.BPay_140
  · exact WuPaper.ClassicalFourthNat.BPay_141
  · exact WuPaper.ClassicalFourthNat.BPay_142
  · exact WuPaper.ClassicalFourthNat.BPay_143
  · exact WuPaper.ClassicalFourthNat.BPay_144
  · exact WuPaper.ClassicalFourthNat.BPay_145
  · exact WuPaper.ClassicalFourthNat.BPay_146
  · exact WuPaper.ClassicalFourthNat.BPay_147
  · exact WuPaper.ClassicalFourthNat.BPay_148
  · exact WuPaper.ClassicalFourthNat.BPay_149
  · exact WuPaper.ClassicalFourthNat.BPay_150
  · exact WuPaper.ClassicalFourthNat.BPay_151
  · exact WuPaper.ClassicalFourthNat.BPay_152
  · exact WuPaper.ClassicalFourthNat.BPay_153
  · exact WuPaper.ClassicalFourthNat.BPay_154
  · exact WuPaper.ClassicalFourthNat.BPay_155
  · exact WuPaper.ClassicalFourthNat.BPay_156
  · exact WuPaper.ClassicalFourthNat.BPay_157
  · exact WuPaper.ClassicalFourthNat.BPay_158
  · exact WuPaper.ClassicalFourthNat.BPay_159
  · exact WuPaper.ClassicalFourthNat.BPay_160
  · exact WuPaper.ClassicalFourthNat.BPay_161
  · exact WuPaper.ClassicalFourthNat.BPay_162
  · exact WuPaper.ClassicalFourthNat.BPay_163
  · exact WuPaper.ClassicalFourthNat.BPay_164
  · exact WuPaper.ClassicalFourthNat.BPay_165
  · exact WuPaper.ClassicalFourthNat.BPay_166
  · exact WuPaper.ClassicalFourthNat.BPay_167
  · exact WuPaper.ClassicalFourthNat.BPay_168
  · exact WuPaper.ClassicalFourthNat.BPay_169
  · exact WuPaper.ClassicalFourthNat.BPay_170
  · exact WuPaper.ClassicalFourthNat.BPay_171
  · exact WuPaper.ClassicalFourthNat.BPay_172
  · exact WuPaper.ClassicalFourthNat.BPay_173
  · exact WuPaper.ClassicalFourthNat.BPay_174
  · exact WuPaper.ClassicalFourthNat.BPay_175
  · exact WuPaper.ClassicalFourthNat.BPay_176
  · exact WuPaper.ClassicalFourthNat.BPay_177
  · exact WuPaper.ClassicalFourthNat.BPay_178
  · exact WuPaper.ClassicalFourthNat.BPay_179
  · exact WuPaper.ClassicalFourthNat.BPay_180
  · exact WuPaper.ClassicalFourthNat.BPay_181
  · exact WuPaper.ClassicalFourthNat.BPay_182
  · exact WuPaper.ClassicalFourthNat.BPay_183
  · exact WuPaper.ClassicalFourthNat.BPay_184
  · exact WuPaper.ClassicalFourthNat.BPay_185
  · exact WuPaper.ClassicalFourthNat.BPay_186
  · exact WuPaper.ClassicalFourthNat.BPay_187
  · exact WuPaper.ClassicalFourthNat.BPay_188
  · exact WuPaper.ClassicalFourthNat.BPay_189
  · exact WuPaper.ClassicalFourthNat.BPay_190
  · exact WuPaper.ClassicalFourthNat.BPay_191
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_002
