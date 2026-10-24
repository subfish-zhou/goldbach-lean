import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay067
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_067 (j : Fin 64) (hj : 64*67+j.val < 10540) :
    BPay (64*67+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_4288
  · exact WuPaper.ClassicalFourthNat.BPay_4289
  · exact WuPaper.ClassicalFourthNat.BPay_4290
  · exact WuPaper.ClassicalFourthNat.BPay_4291
  · exact WuPaper.ClassicalFourthNat.BPay_4292
  · exact WuPaper.ClassicalFourthNat.BPay_4293
  · exact WuPaper.ClassicalFourthNat.BPay_4294
  · exact WuPaper.ClassicalFourthNat.BPay_4295
  · exact WuPaper.ClassicalFourthNat.BPay_4296
  · exact WuPaper.ClassicalFourthNat.BPay_4297
  · exact WuPaper.ClassicalFourthNat.BPay_4298
  · exact WuPaper.ClassicalFourthNat.BPay_4299
  · exact WuPaper.ClassicalFourthNat.BPay_4300
  · exact WuPaper.ClassicalFourthNat.BPay_4301
  · exact WuPaper.ClassicalFourthNat.BPay_4302
  · exact WuPaper.ClassicalFourthNat.BPay_4303
  · exact WuPaper.ClassicalFourthNat.BPay_4304
  · exact WuPaper.ClassicalFourthNat.BPay_4305
  · exact WuPaper.ClassicalFourthNat.BPay_4306
  · exact WuPaper.ClassicalFourthNat.BPay_4307
  · exact WuPaper.ClassicalFourthNat.BPay_4308
  · exact WuPaper.ClassicalFourthNat.BPay_4309
  · exact WuPaper.ClassicalFourthNat.BPay_4310
  · exact WuPaper.ClassicalFourthNat.BPay_4311
  · exact WuPaper.ClassicalFourthNat.BPay_4312
  · exact WuPaper.ClassicalFourthNat.BPay_4313
  · exact WuPaper.ClassicalFourthNat.BPay_4314
  · exact WuPaper.ClassicalFourthNat.BPay_4315
  · exact WuPaper.ClassicalFourthNat.BPay_4316
  · exact WuPaper.ClassicalFourthNat.BPay_4317
  · exact WuPaper.ClassicalFourthNat.BPay_4318
  · exact WuPaper.ClassicalFourthNat.BPay_4319
  · exact WuPaper.ClassicalFourthNat.BPay_4320
  · exact WuPaper.ClassicalFourthNat.BPay_4321
  · exact WuPaper.ClassicalFourthNat.BPay_4322
  · exact WuPaper.ClassicalFourthNat.BPay_4323
  · exact WuPaper.ClassicalFourthNat.BPay_4324
  · exact WuPaper.ClassicalFourthNat.BPay_4325
  · exact WuPaper.ClassicalFourthNat.BPay_4326
  · exact WuPaper.ClassicalFourthNat.BPay_4327
  · exact WuPaper.ClassicalFourthNat.BPay_4328
  · exact WuPaper.ClassicalFourthNat.BPay_4329
  · exact WuPaper.ClassicalFourthNat.BPay_4330
  · exact WuPaper.ClassicalFourthNat.BPay_4331
  · exact WuPaper.ClassicalFourthNat.BPay_4332
  · exact WuPaper.ClassicalFourthNat.BPay_4333
  · exact WuPaper.ClassicalFourthNat.BPay_4334
  · exact WuPaper.ClassicalFourthNat.BPay_4335
  · exact WuPaper.ClassicalFourthNat.BPay_4336
  · exact WuPaper.ClassicalFourthNat.BPay_4337
  · exact WuPaper.ClassicalFourthNat.BPay_4338
  · exact WuPaper.ClassicalFourthNat.BPay_4339
  · exact WuPaper.ClassicalFourthNat.BPay_4340
  · exact WuPaper.ClassicalFourthNat.BPay_4341
  · exact WuPaper.ClassicalFourthNat.BPay_4342
  · exact WuPaper.ClassicalFourthNat.BPay_4343
  · exact WuPaper.ClassicalFourthNat.BPay_4344
  · exact WuPaper.ClassicalFourthNat.BPay_4345
  · exact WuPaper.ClassicalFourthNat.BPay_4346
  · exact WuPaper.ClassicalFourthNat.BPay_4347
  · exact WuPaper.ClassicalFourthNat.BPay_4348
  · exact WuPaper.ClassicalFourthNat.BPay_4349
  · exact WuPaper.ClassicalFourthNat.BPay_4350
  · exact WuPaper.ClassicalFourthNat.BPay_4351
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_067
