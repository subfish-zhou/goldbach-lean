import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatouterPay065
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem outerPay_block_065 (j : Fin 64) (hj : 64*65+j.val < 10540) :
    OuterPay (64*65+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.outerPay_4160
  · exact WuPaper.ClassicalFourthNat.outerPay_4161
  · exact WuPaper.ClassicalFourthNat.outerPay_4162
  · exact WuPaper.ClassicalFourthNat.outerPay_4163
  · exact WuPaper.ClassicalFourthNat.outerPay_4164
  · exact WuPaper.ClassicalFourthNat.outerPay_4165
  · exact WuPaper.ClassicalFourthNat.outerPay_4166
  · exact WuPaper.ClassicalFourthNat.outerPay_4167
  · exact WuPaper.ClassicalFourthNat.outerPay_4168
  · exact WuPaper.ClassicalFourthNat.outerPay_4169
  · exact WuPaper.ClassicalFourthNat.outerPay_4170
  · exact WuPaper.ClassicalFourthNat.outerPay_4171
  · exact WuPaper.ClassicalFourthNat.outerPay_4172
  · exact WuPaper.ClassicalFourthNat.outerPay_4173
  · exact WuPaper.ClassicalFourthNat.outerPay_4174
  · exact WuPaper.ClassicalFourthNat.outerPay_4175
  · exact WuPaper.ClassicalFourthNat.outerPay_4176
  · exact WuPaper.ClassicalFourthNat.outerPay_4177
  · exact WuPaper.ClassicalFourthNat.outerPay_4178
  · exact WuPaper.ClassicalFourthNat.outerPay_4179
  · exact WuPaper.ClassicalFourthNat.outerPay_4180
  · exact WuPaper.ClassicalFourthNat.outerPay_4181
  · exact WuPaper.ClassicalFourthNat.outerPay_4182
  · exact WuPaper.ClassicalFourthNat.outerPay_4183
  · exact WuPaper.ClassicalFourthNat.outerPay_4184
  · exact WuPaper.ClassicalFourthNat.outerPay_4185
  · exact WuPaper.ClassicalFourthNat.outerPay_4186
  · exact WuPaper.ClassicalFourthNat.outerPay_4187
  · exact WuPaper.ClassicalFourthNat.outerPay_4188
  · exact WuPaper.ClassicalFourthNat.outerPay_4189
  · exact WuPaper.ClassicalFourthNat.outerPay_4190
  · exact WuPaper.ClassicalFourthNat.outerPay_4191
  · exact WuPaper.ClassicalFourthNat.outerPay_4192
  · exact WuPaper.ClassicalFourthNat.outerPay_4193
  · exact WuPaper.ClassicalFourthNat.outerPay_4194
  · exact WuPaper.ClassicalFourthNat.outerPay_4195
  · exact WuPaper.ClassicalFourthNat.outerPay_4196
  · exact WuPaper.ClassicalFourthNat.outerPay_4197
  · exact WuPaper.ClassicalFourthNat.outerPay_4198
  · exact WuPaper.ClassicalFourthNat.outerPay_4199
  · exact WuPaper.ClassicalFourthNat.outerPay_4200
  · exact WuPaper.ClassicalFourthNat.outerPay_4201
  · exact WuPaper.ClassicalFourthNat.outerPay_4202
  · exact WuPaper.ClassicalFourthNat.outerPay_4203
  · exact WuPaper.ClassicalFourthNat.outerPay_4204
  · exact WuPaper.ClassicalFourthNat.outerPay_4205
  · exact WuPaper.ClassicalFourthNat.outerPay_4206
  · exact WuPaper.ClassicalFourthNat.outerPay_4207
  · exact WuPaper.ClassicalFourthNat.outerPay_4208
  · exact WuPaper.ClassicalFourthNat.outerPay_4209
  · exact WuPaper.ClassicalFourthNat.outerPay_4210
  · exact WuPaper.ClassicalFourthNat.outerPay_4211
  · exact WuPaper.ClassicalFourthNat.outerPay_4212
  · exact WuPaper.ClassicalFourthNat.outerPay_4213
  · exact WuPaper.ClassicalFourthNat.outerPay_4214
  · exact WuPaper.ClassicalFourthNat.outerPay_4215
  · exact WuPaper.ClassicalFourthNat.outerPay_4216
  · exact WuPaper.ClassicalFourthNat.outerPay_4217
  · exact WuPaper.ClassicalFourthNat.outerPay_4218
  · exact WuPaper.ClassicalFourthNat.outerPay_4219
  · exact WuPaper.ClassicalFourthNat.outerPay_4220
  · exact WuPaper.ClassicalFourthNat.outerPay_4221
  · exact WuPaper.ClassicalFourthNat.outerPay_4222
  · exact WuPaper.ClassicalFourthNat.outerPay_4223
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.outerPay_block_065
