import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay131
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_131 (j : Fin 64) (hj : 64*131+j.val < 10540) :
    BPay (64*131+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_8384
  · exact WuPaper.ClassicalFourthNat.BPay_8385
  · exact WuPaper.ClassicalFourthNat.BPay_8386
  · exact WuPaper.ClassicalFourthNat.BPay_8387
  · exact WuPaper.ClassicalFourthNat.BPay_8388
  · exact WuPaper.ClassicalFourthNat.BPay_8389
  · exact WuPaper.ClassicalFourthNat.BPay_8390
  · exact WuPaper.ClassicalFourthNat.BPay_8391
  · exact WuPaper.ClassicalFourthNat.BPay_8392
  · exact WuPaper.ClassicalFourthNat.BPay_8393
  · exact WuPaper.ClassicalFourthNat.BPay_8394
  · exact WuPaper.ClassicalFourthNat.BPay_8395
  · exact WuPaper.ClassicalFourthNat.BPay_8396
  · exact WuPaper.ClassicalFourthNat.BPay_8397
  · exact WuPaper.ClassicalFourthNat.BPay_8398
  · exact WuPaper.ClassicalFourthNat.BPay_8399
  · exact WuPaper.ClassicalFourthNat.BPay_8400
  · exact WuPaper.ClassicalFourthNat.BPay_8401
  · exact WuPaper.ClassicalFourthNat.BPay_8402
  · exact WuPaper.ClassicalFourthNat.BPay_8403
  · exact WuPaper.ClassicalFourthNat.BPay_8404
  · exact WuPaper.ClassicalFourthNat.BPay_8405
  · exact WuPaper.ClassicalFourthNat.BPay_8406
  · exact WuPaper.ClassicalFourthNat.BPay_8407
  · exact WuPaper.ClassicalFourthNat.BPay_8408
  · exact WuPaper.ClassicalFourthNat.BPay_8409
  · exact WuPaper.ClassicalFourthNat.BPay_8410
  · exact WuPaper.ClassicalFourthNat.BPay_8411
  · exact WuPaper.ClassicalFourthNat.BPay_8412
  · exact WuPaper.ClassicalFourthNat.BPay_8413
  · exact WuPaper.ClassicalFourthNat.BPay_8414
  · exact WuPaper.ClassicalFourthNat.BPay_8415
  · exact WuPaper.ClassicalFourthNat.BPay_8416
  · exact WuPaper.ClassicalFourthNat.BPay_8417
  · exact WuPaper.ClassicalFourthNat.BPay_8418
  · exact WuPaper.ClassicalFourthNat.BPay_8419
  · exact WuPaper.ClassicalFourthNat.BPay_8420
  · exact WuPaper.ClassicalFourthNat.BPay_8421
  · exact WuPaper.ClassicalFourthNat.BPay_8422
  · exact WuPaper.ClassicalFourthNat.BPay_8423
  · exact WuPaper.ClassicalFourthNat.BPay_8424
  · exact WuPaper.ClassicalFourthNat.BPay_8425
  · exact WuPaper.ClassicalFourthNat.BPay_8426
  · exact WuPaper.ClassicalFourthNat.BPay_8427
  · exact WuPaper.ClassicalFourthNat.BPay_8428
  · exact WuPaper.ClassicalFourthNat.BPay_8429
  · exact WuPaper.ClassicalFourthNat.BPay_8430
  · exact WuPaper.ClassicalFourthNat.BPay_8431
  · exact WuPaper.ClassicalFourthNat.BPay_8432
  · exact WuPaper.ClassicalFourthNat.BPay_8433
  · exact WuPaper.ClassicalFourthNat.BPay_8434
  · exact WuPaper.ClassicalFourthNat.BPay_8435
  · exact WuPaper.ClassicalFourthNat.BPay_8436
  · exact WuPaper.ClassicalFourthNat.BPay_8437
  · exact WuPaper.ClassicalFourthNat.BPay_8438
  · exact WuPaper.ClassicalFourthNat.BPay_8439
  · exact WuPaper.ClassicalFourthNat.BPay_8440
  · exact WuPaper.ClassicalFourthNat.BPay_8441
  · exact WuPaper.ClassicalFourthNat.BPay_8442
  · exact WuPaper.ClassicalFourthNat.BPay_8443
  · exact WuPaper.ClassicalFourthNat.BPay_8444
  · exact WuPaper.ClassicalFourthNat.BPay_8445
  · exact WuPaper.ClassicalFourthNat.BPay_8446
  · exact WuPaper.ClassicalFourthNat.BPay_8447
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_131
