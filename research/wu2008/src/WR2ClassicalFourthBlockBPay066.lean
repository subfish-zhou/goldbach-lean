import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay066
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_066 (j : Fin 64) (hj : 64*66+j.val < 10540) :
    BPay (64*66+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_4224
  · exact WuPaper.ClassicalFourthNat.BPay_4225
  · exact WuPaper.ClassicalFourthNat.BPay_4226
  · exact WuPaper.ClassicalFourthNat.BPay_4227
  · exact WuPaper.ClassicalFourthNat.BPay_4228
  · exact WuPaper.ClassicalFourthNat.BPay_4229
  · exact WuPaper.ClassicalFourthNat.BPay_4230
  · exact WuPaper.ClassicalFourthNat.BPay_4231
  · exact WuPaper.ClassicalFourthNat.BPay_4232
  · exact WuPaper.ClassicalFourthNat.BPay_4233
  · exact WuPaper.ClassicalFourthNat.BPay_4234
  · exact WuPaper.ClassicalFourthNat.BPay_4235
  · exact WuPaper.ClassicalFourthNat.BPay_4236
  · exact WuPaper.ClassicalFourthNat.BPay_4237
  · exact WuPaper.ClassicalFourthNat.BPay_4238
  · exact WuPaper.ClassicalFourthNat.BPay_4239
  · exact WuPaper.ClassicalFourthNat.BPay_4240
  · exact WuPaper.ClassicalFourthNat.BPay_4241
  · exact WuPaper.ClassicalFourthNat.BPay_4242
  · exact WuPaper.ClassicalFourthNat.BPay_4243
  · exact WuPaper.ClassicalFourthNat.BPay_4244
  · exact WuPaper.ClassicalFourthNat.BPay_4245
  · exact WuPaper.ClassicalFourthNat.BPay_4246
  · exact WuPaper.ClassicalFourthNat.BPay_4247
  · exact WuPaper.ClassicalFourthNat.BPay_4248
  · exact WuPaper.ClassicalFourthNat.BPay_4249
  · exact WuPaper.ClassicalFourthNat.BPay_4250
  · exact WuPaper.ClassicalFourthNat.BPay_4251
  · exact WuPaper.ClassicalFourthNat.BPay_4252
  · exact WuPaper.ClassicalFourthNat.BPay_4253
  · exact WuPaper.ClassicalFourthNat.BPay_4254
  · exact WuPaper.ClassicalFourthNat.BPay_4255
  · exact WuPaper.ClassicalFourthNat.BPay_4256
  · exact WuPaper.ClassicalFourthNat.BPay_4257
  · exact WuPaper.ClassicalFourthNat.BPay_4258
  · exact WuPaper.ClassicalFourthNat.BPay_4259
  · exact WuPaper.ClassicalFourthNat.BPay_4260
  · exact WuPaper.ClassicalFourthNat.BPay_4261
  · exact WuPaper.ClassicalFourthNat.BPay_4262
  · exact WuPaper.ClassicalFourthNat.BPay_4263
  · exact WuPaper.ClassicalFourthNat.BPay_4264
  · exact WuPaper.ClassicalFourthNat.BPay_4265
  · exact WuPaper.ClassicalFourthNat.BPay_4266
  · exact WuPaper.ClassicalFourthNat.BPay_4267
  · exact WuPaper.ClassicalFourthNat.BPay_4268
  · exact WuPaper.ClassicalFourthNat.BPay_4269
  · exact WuPaper.ClassicalFourthNat.BPay_4270
  · exact WuPaper.ClassicalFourthNat.BPay_4271
  · exact WuPaper.ClassicalFourthNat.BPay_4272
  · exact WuPaper.ClassicalFourthNat.BPay_4273
  · exact WuPaper.ClassicalFourthNat.BPay_4274
  · exact WuPaper.ClassicalFourthNat.BPay_4275
  · exact WuPaper.ClassicalFourthNat.BPay_4276
  · exact WuPaper.ClassicalFourthNat.BPay_4277
  · exact WuPaper.ClassicalFourthNat.BPay_4278
  · exact WuPaper.ClassicalFourthNat.BPay_4279
  · exact WuPaper.ClassicalFourthNat.BPay_4280
  · exact WuPaper.ClassicalFourthNat.BPay_4281
  · exact WuPaper.ClassicalFourthNat.BPay_4282
  · exact WuPaper.ClassicalFourthNat.BPay_4283
  · exact WuPaper.ClassicalFourthNat.BPay_4284
  · exact WuPaper.ClassicalFourthNat.BPay_4285
  · exact WuPaper.ClassicalFourthNat.BPay_4286
  · exact WuPaper.ClassicalFourthNat.BPay_4287
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_066
