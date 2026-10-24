import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay130
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_130 (j : Fin 64) (hj : 64*130+j.val < 10540) :
    BPay (64*130+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_8320
  · exact WuPaper.ClassicalFourthNat.BPay_8321
  · exact WuPaper.ClassicalFourthNat.BPay_8322
  · exact WuPaper.ClassicalFourthNat.BPay_8323
  · exact WuPaper.ClassicalFourthNat.BPay_8324
  · exact WuPaper.ClassicalFourthNat.BPay_8325
  · exact WuPaper.ClassicalFourthNat.BPay_8326
  · exact WuPaper.ClassicalFourthNat.BPay_8327
  · exact WuPaper.ClassicalFourthNat.BPay_8328
  · exact WuPaper.ClassicalFourthNat.BPay_8329
  · exact WuPaper.ClassicalFourthNat.BPay_8330
  · exact WuPaper.ClassicalFourthNat.BPay_8331
  · exact WuPaper.ClassicalFourthNat.BPay_8332
  · exact WuPaper.ClassicalFourthNat.BPay_8333
  · exact WuPaper.ClassicalFourthNat.BPay_8334
  · exact WuPaper.ClassicalFourthNat.BPay_8335
  · exact WuPaper.ClassicalFourthNat.BPay_8336
  · exact WuPaper.ClassicalFourthNat.BPay_8337
  · exact WuPaper.ClassicalFourthNat.BPay_8338
  · exact WuPaper.ClassicalFourthNat.BPay_8339
  · exact WuPaper.ClassicalFourthNat.BPay_8340
  · exact WuPaper.ClassicalFourthNat.BPay_8341
  · exact WuPaper.ClassicalFourthNat.BPay_8342
  · exact WuPaper.ClassicalFourthNat.BPay_8343
  · exact WuPaper.ClassicalFourthNat.BPay_8344
  · exact WuPaper.ClassicalFourthNat.BPay_8345
  · exact WuPaper.ClassicalFourthNat.BPay_8346
  · exact WuPaper.ClassicalFourthNat.BPay_8347
  · exact WuPaper.ClassicalFourthNat.BPay_8348
  · exact WuPaper.ClassicalFourthNat.BPay_8349
  · exact WuPaper.ClassicalFourthNat.BPay_8350
  · exact WuPaper.ClassicalFourthNat.BPay_8351
  · exact WuPaper.ClassicalFourthNat.BPay_8352
  · exact WuPaper.ClassicalFourthNat.BPay_8353
  · exact WuPaper.ClassicalFourthNat.BPay_8354
  · exact WuPaper.ClassicalFourthNat.BPay_8355
  · exact WuPaper.ClassicalFourthNat.BPay_8356
  · exact WuPaper.ClassicalFourthNat.BPay_8357
  · exact WuPaper.ClassicalFourthNat.BPay_8358
  · exact WuPaper.ClassicalFourthNat.BPay_8359
  · exact WuPaper.ClassicalFourthNat.BPay_8360
  · exact WuPaper.ClassicalFourthNat.BPay_8361
  · exact WuPaper.ClassicalFourthNat.BPay_8362
  · exact WuPaper.ClassicalFourthNat.BPay_8363
  · exact WuPaper.ClassicalFourthNat.BPay_8364
  · exact WuPaper.ClassicalFourthNat.BPay_8365
  · exact WuPaper.ClassicalFourthNat.BPay_8366
  · exact WuPaper.ClassicalFourthNat.BPay_8367
  · exact WuPaper.ClassicalFourthNat.BPay_8368
  · exact WuPaper.ClassicalFourthNat.BPay_8369
  · exact WuPaper.ClassicalFourthNat.BPay_8370
  · exact WuPaper.ClassicalFourthNat.BPay_8371
  · exact WuPaper.ClassicalFourthNat.BPay_8372
  · exact WuPaper.ClassicalFourthNat.BPay_8373
  · exact WuPaper.ClassicalFourthNat.BPay_8374
  · exact WuPaper.ClassicalFourthNat.BPay_8375
  · exact WuPaper.ClassicalFourthNat.BPay_8376
  · exact WuPaper.ClassicalFourthNat.BPay_8377
  · exact WuPaper.ClassicalFourthNat.BPay_8378
  · exact WuPaper.ClassicalFourthNat.BPay_8379
  · exact WuPaper.ClassicalFourthNat.BPay_8380
  · exact WuPaper.ClassicalFourthNat.BPay_8381
  · exact WuPaper.ClassicalFourthNat.BPay_8382
  · exact WuPaper.ClassicalFourthNat.BPay_8383
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_130
