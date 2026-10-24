import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatDPay002
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem DPay_block_002 (j : Fin 64) (hj : 64*2+j.val < 2540) :
    DPay (64*2+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.DPay_128
  · exact WuPaper.ClassicalFourthNat.DPay_129
  · exact WuPaper.ClassicalFourthNat.DPay_130
  · exact WuPaper.ClassicalFourthNat.DPay_131
  · exact WuPaper.ClassicalFourthNat.DPay_132
  · exact WuPaper.ClassicalFourthNat.DPay_133
  · exact WuPaper.ClassicalFourthNat.DPay_134
  · exact WuPaper.ClassicalFourthNat.DPay_135
  · exact WuPaper.ClassicalFourthNat.DPay_136
  · exact WuPaper.ClassicalFourthNat.DPay_137
  · exact WuPaper.ClassicalFourthNat.DPay_138
  · exact WuPaper.ClassicalFourthNat.DPay_139
  · exact WuPaper.ClassicalFourthNat.DPay_140
  · exact WuPaper.ClassicalFourthNat.DPay_141
  · exact WuPaper.ClassicalFourthNat.DPay_142
  · exact WuPaper.ClassicalFourthNat.DPay_143
  · exact WuPaper.ClassicalFourthNat.DPay_144
  · exact WuPaper.ClassicalFourthNat.DPay_145
  · exact WuPaper.ClassicalFourthNat.DPay_146
  · exact WuPaper.ClassicalFourthNat.DPay_147
  · exact WuPaper.ClassicalFourthNat.DPay_148
  · exact WuPaper.ClassicalFourthNat.DPay_149
  · exact WuPaper.ClassicalFourthNat.DPay_150
  · exact WuPaper.ClassicalFourthNat.DPay_151
  · exact WuPaper.ClassicalFourthNat.DPay_152
  · exact WuPaper.ClassicalFourthNat.DPay_153
  · exact WuPaper.ClassicalFourthNat.DPay_154
  · exact WuPaper.ClassicalFourthNat.DPay_155
  · exact WuPaper.ClassicalFourthNat.DPay_156
  · exact WuPaper.ClassicalFourthNat.DPay_157
  · exact WuPaper.ClassicalFourthNat.DPay_158
  · exact WuPaper.ClassicalFourthNat.DPay_159
  · exact WuPaper.ClassicalFourthNat.DPay_160
  · exact WuPaper.ClassicalFourthNat.DPay_161
  · exact WuPaper.ClassicalFourthNat.DPay_162
  · exact WuPaper.ClassicalFourthNat.DPay_163
  · exact WuPaper.ClassicalFourthNat.DPay_164
  · exact WuPaper.ClassicalFourthNat.DPay_165
  · exact WuPaper.ClassicalFourthNat.DPay_166
  · exact WuPaper.ClassicalFourthNat.DPay_167
  · exact WuPaper.ClassicalFourthNat.DPay_168
  · exact WuPaper.ClassicalFourthNat.DPay_169
  · exact WuPaper.ClassicalFourthNat.DPay_170
  · exact WuPaper.ClassicalFourthNat.DPay_171
  · exact WuPaper.ClassicalFourthNat.DPay_172
  · exact WuPaper.ClassicalFourthNat.DPay_173
  · exact WuPaper.ClassicalFourthNat.DPay_174
  · exact WuPaper.ClassicalFourthNat.DPay_175
  · exact WuPaper.ClassicalFourthNat.DPay_176
  · exact WuPaper.ClassicalFourthNat.DPay_177
  · exact WuPaper.ClassicalFourthNat.DPay_178
  · exact WuPaper.ClassicalFourthNat.DPay_179
  · exact WuPaper.ClassicalFourthNat.DPay_180
  · exact WuPaper.ClassicalFourthNat.DPay_181
  · exact WuPaper.ClassicalFourthNat.DPay_182
  · exact WuPaper.ClassicalFourthNat.DPay_183
  · exact WuPaper.ClassicalFourthNat.DPay_184
  · exact WuPaper.ClassicalFourthNat.DPay_185
  · exact WuPaper.ClassicalFourthNat.DPay_186
  · exact WuPaper.ClassicalFourthNat.DPay_187
  · exact WuPaper.ClassicalFourthNat.DPay_188
  · exact WuPaper.ClassicalFourthNat.DPay_189
  · exact WuPaper.ClassicalFourthNat.DPay_190
  · exact WuPaper.ClassicalFourthNat.DPay_191
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.DPay_block_002
