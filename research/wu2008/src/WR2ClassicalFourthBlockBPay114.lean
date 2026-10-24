import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay114
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_114 (j : Fin 64) (hj : 64*114+j.val < 10540) :
    BPay (64*114+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_7296
  · exact WuPaper.ClassicalFourthNat.BPay_7297
  · exact WuPaper.ClassicalFourthNat.BPay_7298
  · exact WuPaper.ClassicalFourthNat.BPay_7299
  · exact WuPaper.ClassicalFourthNat.BPay_7300
  · exact WuPaper.ClassicalFourthNat.BPay_7301
  · exact WuPaper.ClassicalFourthNat.BPay_7302
  · exact WuPaper.ClassicalFourthNat.BPay_7303
  · exact WuPaper.ClassicalFourthNat.BPay_7304
  · exact WuPaper.ClassicalFourthNat.BPay_7305
  · exact WuPaper.ClassicalFourthNat.BPay_7306
  · exact WuPaper.ClassicalFourthNat.BPay_7307
  · exact WuPaper.ClassicalFourthNat.BPay_7308
  · exact WuPaper.ClassicalFourthNat.BPay_7309
  · exact WuPaper.ClassicalFourthNat.BPay_7310
  · exact WuPaper.ClassicalFourthNat.BPay_7311
  · exact WuPaper.ClassicalFourthNat.BPay_7312
  · exact WuPaper.ClassicalFourthNat.BPay_7313
  · exact WuPaper.ClassicalFourthNat.BPay_7314
  · exact WuPaper.ClassicalFourthNat.BPay_7315
  · exact WuPaper.ClassicalFourthNat.BPay_7316
  · exact WuPaper.ClassicalFourthNat.BPay_7317
  · exact WuPaper.ClassicalFourthNat.BPay_7318
  · exact WuPaper.ClassicalFourthNat.BPay_7319
  · exact WuPaper.ClassicalFourthNat.BPay_7320
  · exact WuPaper.ClassicalFourthNat.BPay_7321
  · exact WuPaper.ClassicalFourthNat.BPay_7322
  · exact WuPaper.ClassicalFourthNat.BPay_7323
  · exact WuPaper.ClassicalFourthNat.BPay_7324
  · exact WuPaper.ClassicalFourthNat.BPay_7325
  · exact WuPaper.ClassicalFourthNat.BPay_7326
  · exact WuPaper.ClassicalFourthNat.BPay_7327
  · exact WuPaper.ClassicalFourthNat.BPay_7328
  · exact WuPaper.ClassicalFourthNat.BPay_7329
  · exact WuPaper.ClassicalFourthNat.BPay_7330
  · exact WuPaper.ClassicalFourthNat.BPay_7331
  · exact WuPaper.ClassicalFourthNat.BPay_7332
  · exact WuPaper.ClassicalFourthNat.BPay_7333
  · exact WuPaper.ClassicalFourthNat.BPay_7334
  · exact WuPaper.ClassicalFourthNat.BPay_7335
  · exact WuPaper.ClassicalFourthNat.BPay_7336
  · exact WuPaper.ClassicalFourthNat.BPay_7337
  · exact WuPaper.ClassicalFourthNat.BPay_7338
  · exact WuPaper.ClassicalFourthNat.BPay_7339
  · exact WuPaper.ClassicalFourthNat.BPay_7340
  · exact WuPaper.ClassicalFourthNat.BPay_7341
  · exact WuPaper.ClassicalFourthNat.BPay_7342
  · exact WuPaper.ClassicalFourthNat.BPay_7343
  · exact WuPaper.ClassicalFourthNat.BPay_7344
  · exact WuPaper.ClassicalFourthNat.BPay_7345
  · exact WuPaper.ClassicalFourthNat.BPay_7346
  · exact WuPaper.ClassicalFourthNat.BPay_7347
  · exact WuPaper.ClassicalFourthNat.BPay_7348
  · exact WuPaper.ClassicalFourthNat.BPay_7349
  · exact WuPaper.ClassicalFourthNat.BPay_7350
  · exact WuPaper.ClassicalFourthNat.BPay_7351
  · exact WuPaper.ClassicalFourthNat.BPay_7352
  · exact WuPaper.ClassicalFourthNat.BPay_7353
  · exact WuPaper.ClassicalFourthNat.BPay_7354
  · exact WuPaper.ClassicalFourthNat.BPay_7355
  · exact WuPaper.ClassicalFourthNat.BPay_7356
  · exact WuPaper.ClassicalFourthNat.BPay_7357
  · exact WuPaper.ClassicalFourthNat.BPay_7358
  · exact WuPaper.ClassicalFourthNat.BPay_7359
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_114
