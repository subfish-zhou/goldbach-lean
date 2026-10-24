import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay065
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_065 (j : Fin 64) (hj : 64*65+j.val < 10540) :
    BPay (64*65+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_4160
  · exact WuPaper.ClassicalFourthNat.BPay_4161
  · exact WuPaper.ClassicalFourthNat.BPay_4162
  · exact WuPaper.ClassicalFourthNat.BPay_4163
  · exact WuPaper.ClassicalFourthNat.BPay_4164
  · exact WuPaper.ClassicalFourthNat.BPay_4165
  · exact WuPaper.ClassicalFourthNat.BPay_4166
  · exact WuPaper.ClassicalFourthNat.BPay_4167
  · exact WuPaper.ClassicalFourthNat.BPay_4168
  · exact WuPaper.ClassicalFourthNat.BPay_4169
  · exact WuPaper.ClassicalFourthNat.BPay_4170
  · exact WuPaper.ClassicalFourthNat.BPay_4171
  · exact WuPaper.ClassicalFourthNat.BPay_4172
  · exact WuPaper.ClassicalFourthNat.BPay_4173
  · exact WuPaper.ClassicalFourthNat.BPay_4174
  · exact WuPaper.ClassicalFourthNat.BPay_4175
  · exact WuPaper.ClassicalFourthNat.BPay_4176
  · exact WuPaper.ClassicalFourthNat.BPay_4177
  · exact WuPaper.ClassicalFourthNat.BPay_4178
  · exact WuPaper.ClassicalFourthNat.BPay_4179
  · exact WuPaper.ClassicalFourthNat.BPay_4180
  · exact WuPaper.ClassicalFourthNat.BPay_4181
  · exact WuPaper.ClassicalFourthNat.BPay_4182
  · exact WuPaper.ClassicalFourthNat.BPay_4183
  · exact WuPaper.ClassicalFourthNat.BPay_4184
  · exact WuPaper.ClassicalFourthNat.BPay_4185
  · exact WuPaper.ClassicalFourthNat.BPay_4186
  · exact WuPaper.ClassicalFourthNat.BPay_4187
  · exact WuPaper.ClassicalFourthNat.BPay_4188
  · exact WuPaper.ClassicalFourthNat.BPay_4189
  · exact WuPaper.ClassicalFourthNat.BPay_4190
  · exact WuPaper.ClassicalFourthNat.BPay_4191
  · exact WuPaper.ClassicalFourthNat.BPay_4192
  · exact WuPaper.ClassicalFourthNat.BPay_4193
  · exact WuPaper.ClassicalFourthNat.BPay_4194
  · exact WuPaper.ClassicalFourthNat.BPay_4195
  · exact WuPaper.ClassicalFourthNat.BPay_4196
  · exact WuPaper.ClassicalFourthNat.BPay_4197
  · exact WuPaper.ClassicalFourthNat.BPay_4198
  · exact WuPaper.ClassicalFourthNat.BPay_4199
  · exact WuPaper.ClassicalFourthNat.BPay_4200
  · exact WuPaper.ClassicalFourthNat.BPay_4201
  · exact WuPaper.ClassicalFourthNat.BPay_4202
  · exact WuPaper.ClassicalFourthNat.BPay_4203
  · exact WuPaper.ClassicalFourthNat.BPay_4204
  · exact WuPaper.ClassicalFourthNat.BPay_4205
  · exact WuPaper.ClassicalFourthNat.BPay_4206
  · exact WuPaper.ClassicalFourthNat.BPay_4207
  · exact WuPaper.ClassicalFourthNat.BPay_4208
  · exact WuPaper.ClassicalFourthNat.BPay_4209
  · exact WuPaper.ClassicalFourthNat.BPay_4210
  · exact WuPaper.ClassicalFourthNat.BPay_4211
  · exact WuPaper.ClassicalFourthNat.BPay_4212
  · exact WuPaper.ClassicalFourthNat.BPay_4213
  · exact WuPaper.ClassicalFourthNat.BPay_4214
  · exact WuPaper.ClassicalFourthNat.BPay_4215
  · exact WuPaper.ClassicalFourthNat.BPay_4216
  · exact WuPaper.ClassicalFourthNat.BPay_4217
  · exact WuPaper.ClassicalFourthNat.BPay_4218
  · exact WuPaper.ClassicalFourthNat.BPay_4219
  · exact WuPaper.ClassicalFourthNat.BPay_4220
  · exact WuPaper.ClassicalFourthNat.BPay_4221
  · exact WuPaper.ClassicalFourthNat.BPay_4222
  · exact WuPaper.ClassicalFourthNat.BPay_4223
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_065
