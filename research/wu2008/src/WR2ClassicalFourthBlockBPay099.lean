import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay099
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_099 (j : Fin 64) (hj : 64*99+j.val < 10540) :
    BPay (64*99+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_6336
  · exact WuPaper.ClassicalFourthNat.BPay_6337
  · exact WuPaper.ClassicalFourthNat.BPay_6338
  · exact WuPaper.ClassicalFourthNat.BPay_6339
  · exact WuPaper.ClassicalFourthNat.BPay_6340
  · exact WuPaper.ClassicalFourthNat.BPay_6341
  · exact WuPaper.ClassicalFourthNat.BPay_6342
  · exact WuPaper.ClassicalFourthNat.BPay_6343
  · exact WuPaper.ClassicalFourthNat.BPay_6344
  · exact WuPaper.ClassicalFourthNat.BPay_6345
  · exact WuPaper.ClassicalFourthNat.BPay_6346
  · exact WuPaper.ClassicalFourthNat.BPay_6347
  · exact WuPaper.ClassicalFourthNat.BPay_6348
  · exact WuPaper.ClassicalFourthNat.BPay_6349
  · exact WuPaper.ClassicalFourthNat.BPay_6350
  · exact WuPaper.ClassicalFourthNat.BPay_6351
  · exact WuPaper.ClassicalFourthNat.BPay_6352
  · exact WuPaper.ClassicalFourthNat.BPay_6353
  · exact WuPaper.ClassicalFourthNat.BPay_6354
  · exact WuPaper.ClassicalFourthNat.BPay_6355
  · exact WuPaper.ClassicalFourthNat.BPay_6356
  · exact WuPaper.ClassicalFourthNat.BPay_6357
  · exact WuPaper.ClassicalFourthNat.BPay_6358
  · exact WuPaper.ClassicalFourthNat.BPay_6359
  · exact WuPaper.ClassicalFourthNat.BPay_6360
  · exact WuPaper.ClassicalFourthNat.BPay_6361
  · exact WuPaper.ClassicalFourthNat.BPay_6362
  · exact WuPaper.ClassicalFourthNat.BPay_6363
  · exact WuPaper.ClassicalFourthNat.BPay_6364
  · exact WuPaper.ClassicalFourthNat.BPay_6365
  · exact WuPaper.ClassicalFourthNat.BPay_6366
  · exact WuPaper.ClassicalFourthNat.BPay_6367
  · exact WuPaper.ClassicalFourthNat.BPay_6368
  · exact WuPaper.ClassicalFourthNat.BPay_6369
  · exact WuPaper.ClassicalFourthNat.BPay_6370
  · exact WuPaper.ClassicalFourthNat.BPay_6371
  · exact WuPaper.ClassicalFourthNat.BPay_6372
  · exact WuPaper.ClassicalFourthNat.BPay_6373
  · exact WuPaper.ClassicalFourthNat.BPay_6374
  · exact WuPaper.ClassicalFourthNat.BPay_6375
  · exact WuPaper.ClassicalFourthNat.BPay_6376
  · exact WuPaper.ClassicalFourthNat.BPay_6377
  · exact WuPaper.ClassicalFourthNat.BPay_6378
  · exact WuPaper.ClassicalFourthNat.BPay_6379
  · exact WuPaper.ClassicalFourthNat.BPay_6380
  · exact WuPaper.ClassicalFourthNat.BPay_6381
  · exact WuPaper.ClassicalFourthNat.BPay_6382
  · exact WuPaper.ClassicalFourthNat.BPay_6383
  · exact WuPaper.ClassicalFourthNat.BPay_6384
  · exact WuPaper.ClassicalFourthNat.BPay_6385
  · exact WuPaper.ClassicalFourthNat.BPay_6386
  · exact WuPaper.ClassicalFourthNat.BPay_6387
  · exact WuPaper.ClassicalFourthNat.BPay_6388
  · exact WuPaper.ClassicalFourthNat.BPay_6389
  · exact WuPaper.ClassicalFourthNat.BPay_6390
  · exact WuPaper.ClassicalFourthNat.BPay_6391
  · exact WuPaper.ClassicalFourthNat.BPay_6392
  · exact WuPaper.ClassicalFourthNat.BPay_6393
  · exact WuPaper.ClassicalFourthNat.BPay_6394
  · exact WuPaper.ClassicalFourthNat.BPay_6395
  · exact WuPaper.ClassicalFourthNat.BPay_6396
  · exact WuPaper.ClassicalFourthNat.BPay_6397
  · exact WuPaper.ClassicalFourthNat.BPay_6398
  · exact WuPaper.ClassicalFourthNat.BPay_6399
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_099
