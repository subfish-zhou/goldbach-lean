import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatouterPay130
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem outerPay_block_130 (j : Fin 64) (hj : 64*130+j.val < 10540) :
    OuterPay (64*130+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.outerPay_8320
  · exact WuPaper.ClassicalFourthNat.outerPay_8321
  · exact WuPaper.ClassicalFourthNat.outerPay_8322
  · exact WuPaper.ClassicalFourthNat.outerPay_8323
  · exact WuPaper.ClassicalFourthNat.outerPay_8324
  · exact WuPaper.ClassicalFourthNat.outerPay_8325
  · exact WuPaper.ClassicalFourthNat.outerPay_8326
  · exact WuPaper.ClassicalFourthNat.outerPay_8327
  · exact WuPaper.ClassicalFourthNat.outerPay_8328
  · exact WuPaper.ClassicalFourthNat.outerPay_8329
  · exact WuPaper.ClassicalFourthNat.outerPay_8330
  · exact WuPaper.ClassicalFourthNat.outerPay_8331
  · exact WuPaper.ClassicalFourthNat.outerPay_8332
  · exact WuPaper.ClassicalFourthNat.outerPay_8333
  · exact WuPaper.ClassicalFourthNat.outerPay_8334
  · exact WuPaper.ClassicalFourthNat.outerPay_8335
  · exact WuPaper.ClassicalFourthNat.outerPay_8336
  · exact WuPaper.ClassicalFourthNat.outerPay_8337
  · exact WuPaper.ClassicalFourthNat.outerPay_8338
  · exact WuPaper.ClassicalFourthNat.outerPay_8339
  · exact WuPaper.ClassicalFourthNat.outerPay_8340
  · exact WuPaper.ClassicalFourthNat.outerPay_8341
  · exact WuPaper.ClassicalFourthNat.outerPay_8342
  · exact WuPaper.ClassicalFourthNat.outerPay_8343
  · exact WuPaper.ClassicalFourthNat.outerPay_8344
  · exact WuPaper.ClassicalFourthNat.outerPay_8345
  · exact WuPaper.ClassicalFourthNat.outerPay_8346
  · exact WuPaper.ClassicalFourthNat.outerPay_8347
  · exact WuPaper.ClassicalFourthNat.outerPay_8348
  · exact WuPaper.ClassicalFourthNat.outerPay_8349
  · exact WuPaper.ClassicalFourthNat.outerPay_8350
  · exact WuPaper.ClassicalFourthNat.outerPay_8351
  · exact WuPaper.ClassicalFourthNat.outerPay_8352
  · exact WuPaper.ClassicalFourthNat.outerPay_8353
  · exact WuPaper.ClassicalFourthNat.outerPay_8354
  · exact WuPaper.ClassicalFourthNat.outerPay_8355
  · exact WuPaper.ClassicalFourthNat.outerPay_8356
  · exact WuPaper.ClassicalFourthNat.outerPay_8357
  · exact WuPaper.ClassicalFourthNat.outerPay_8358
  · exact WuPaper.ClassicalFourthNat.outerPay_8359
  · exact WuPaper.ClassicalFourthNat.outerPay_8360
  · exact WuPaper.ClassicalFourthNat.outerPay_8361
  · exact WuPaper.ClassicalFourthNat.outerPay_8362
  · exact WuPaper.ClassicalFourthNat.outerPay_8363
  · exact WuPaper.ClassicalFourthNat.outerPay_8364
  · exact WuPaper.ClassicalFourthNat.outerPay_8365
  · exact WuPaper.ClassicalFourthNat.outerPay_8366
  · exact WuPaper.ClassicalFourthNat.outerPay_8367
  · exact WuPaper.ClassicalFourthNat.outerPay_8368
  · exact WuPaper.ClassicalFourthNat.outerPay_8369
  · exact WuPaper.ClassicalFourthNat.outerPay_8370
  · exact WuPaper.ClassicalFourthNat.outerPay_8371
  · exact WuPaper.ClassicalFourthNat.outerPay_8372
  · exact WuPaper.ClassicalFourthNat.outerPay_8373
  · exact WuPaper.ClassicalFourthNat.outerPay_8374
  · exact WuPaper.ClassicalFourthNat.outerPay_8375
  · exact WuPaper.ClassicalFourthNat.outerPay_8376
  · exact WuPaper.ClassicalFourthNat.outerPay_8377
  · exact WuPaper.ClassicalFourthNat.outerPay_8378
  · exact WuPaper.ClassicalFourthNat.outerPay_8379
  · exact WuPaper.ClassicalFourthNat.outerPay_8380
  · exact WuPaper.ClassicalFourthNat.outerPay_8381
  · exact WuPaper.ClassicalFourthNat.outerPay_8382
  · exact WuPaper.ClassicalFourthNat.outerPay_8383
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.outerPay_block_130
