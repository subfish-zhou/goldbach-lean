import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatouterPay131
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem outerPay_block_131 (j : Fin 64) (hj : 64*131+j.val < 10540) :
    OuterPay (64*131+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.outerPay_8384
  · exact WuPaper.ClassicalFourthNat.outerPay_8385
  · exact WuPaper.ClassicalFourthNat.outerPay_8386
  · exact WuPaper.ClassicalFourthNat.outerPay_8387
  · exact WuPaper.ClassicalFourthNat.outerPay_8388
  · exact WuPaper.ClassicalFourthNat.outerPay_8389
  · exact WuPaper.ClassicalFourthNat.outerPay_8390
  · exact WuPaper.ClassicalFourthNat.outerPay_8391
  · exact WuPaper.ClassicalFourthNat.outerPay_8392
  · exact WuPaper.ClassicalFourthNat.outerPay_8393
  · exact WuPaper.ClassicalFourthNat.outerPay_8394
  · exact WuPaper.ClassicalFourthNat.outerPay_8395
  · exact WuPaper.ClassicalFourthNat.outerPay_8396
  · exact WuPaper.ClassicalFourthNat.outerPay_8397
  · exact WuPaper.ClassicalFourthNat.outerPay_8398
  · exact WuPaper.ClassicalFourthNat.outerPay_8399
  · exact WuPaper.ClassicalFourthNat.outerPay_8400
  · exact WuPaper.ClassicalFourthNat.outerPay_8401
  · exact WuPaper.ClassicalFourthNat.outerPay_8402
  · exact WuPaper.ClassicalFourthNat.outerPay_8403
  · exact WuPaper.ClassicalFourthNat.outerPay_8404
  · exact WuPaper.ClassicalFourthNat.outerPay_8405
  · exact WuPaper.ClassicalFourthNat.outerPay_8406
  · exact WuPaper.ClassicalFourthNat.outerPay_8407
  · exact WuPaper.ClassicalFourthNat.outerPay_8408
  · exact WuPaper.ClassicalFourthNat.outerPay_8409
  · exact WuPaper.ClassicalFourthNat.outerPay_8410
  · exact WuPaper.ClassicalFourthNat.outerPay_8411
  · exact WuPaper.ClassicalFourthNat.outerPay_8412
  · exact WuPaper.ClassicalFourthNat.outerPay_8413
  · exact WuPaper.ClassicalFourthNat.outerPay_8414
  · exact WuPaper.ClassicalFourthNat.outerPay_8415
  · exact WuPaper.ClassicalFourthNat.outerPay_8416
  · exact WuPaper.ClassicalFourthNat.outerPay_8417
  · exact WuPaper.ClassicalFourthNat.outerPay_8418
  · exact WuPaper.ClassicalFourthNat.outerPay_8419
  · exact WuPaper.ClassicalFourthNat.outerPay_8420
  · exact WuPaper.ClassicalFourthNat.outerPay_8421
  · exact WuPaper.ClassicalFourthNat.outerPay_8422
  · exact WuPaper.ClassicalFourthNat.outerPay_8423
  · exact WuPaper.ClassicalFourthNat.outerPay_8424
  · exact WuPaper.ClassicalFourthNat.outerPay_8425
  · exact WuPaper.ClassicalFourthNat.outerPay_8426
  · exact WuPaper.ClassicalFourthNat.outerPay_8427
  · exact WuPaper.ClassicalFourthNat.outerPay_8428
  · exact WuPaper.ClassicalFourthNat.outerPay_8429
  · exact WuPaper.ClassicalFourthNat.outerPay_8430
  · exact WuPaper.ClassicalFourthNat.outerPay_8431
  · exact WuPaper.ClassicalFourthNat.outerPay_8432
  · exact WuPaper.ClassicalFourthNat.outerPay_8433
  · exact WuPaper.ClassicalFourthNat.outerPay_8434
  · exact WuPaper.ClassicalFourthNat.outerPay_8435
  · exact WuPaper.ClassicalFourthNat.outerPay_8436
  · exact WuPaper.ClassicalFourthNat.outerPay_8437
  · exact WuPaper.ClassicalFourthNat.outerPay_8438
  · exact WuPaper.ClassicalFourthNat.outerPay_8439
  · exact WuPaper.ClassicalFourthNat.outerPay_8440
  · exact WuPaper.ClassicalFourthNat.outerPay_8441
  · exact WuPaper.ClassicalFourthNat.outerPay_8442
  · exact WuPaper.ClassicalFourthNat.outerPay_8443
  · exact WuPaper.ClassicalFourthNat.outerPay_8444
  · exact WuPaper.ClassicalFourthNat.outerPay_8445
  · exact WuPaper.ClassicalFourthNat.outerPay_8446
  · exact WuPaper.ClassicalFourthNat.outerPay_8447
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.outerPay_block_131
