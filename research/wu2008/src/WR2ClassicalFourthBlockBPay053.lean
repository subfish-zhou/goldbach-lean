import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay053
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_053 (j : Fin 64) (hj : 64*53+j.val < 10540) :
    BPay (64*53+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_3392
  · exact WuPaper.ClassicalFourthNat.BPay_3393
  · exact WuPaper.ClassicalFourthNat.BPay_3394
  · exact WuPaper.ClassicalFourthNat.BPay_3395
  · exact WuPaper.ClassicalFourthNat.BPay_3396
  · exact WuPaper.ClassicalFourthNat.BPay_3397
  · exact WuPaper.ClassicalFourthNat.BPay_3398
  · exact WuPaper.ClassicalFourthNat.BPay_3399
  · exact WuPaper.ClassicalFourthNat.BPay_3400
  · exact WuPaper.ClassicalFourthNat.BPay_3401
  · exact WuPaper.ClassicalFourthNat.BPay_3402
  · exact WuPaper.ClassicalFourthNat.BPay_3403
  · exact WuPaper.ClassicalFourthNat.BPay_3404
  · exact WuPaper.ClassicalFourthNat.BPay_3405
  · exact WuPaper.ClassicalFourthNat.BPay_3406
  · exact WuPaper.ClassicalFourthNat.BPay_3407
  · exact WuPaper.ClassicalFourthNat.BPay_3408
  · exact WuPaper.ClassicalFourthNat.BPay_3409
  · exact WuPaper.ClassicalFourthNat.BPay_3410
  · exact WuPaper.ClassicalFourthNat.BPay_3411
  · exact WuPaper.ClassicalFourthNat.BPay_3412
  · exact WuPaper.ClassicalFourthNat.BPay_3413
  · exact WuPaper.ClassicalFourthNat.BPay_3414
  · exact WuPaper.ClassicalFourthNat.BPay_3415
  · exact WuPaper.ClassicalFourthNat.BPay_3416
  · exact WuPaper.ClassicalFourthNat.BPay_3417
  · exact WuPaper.ClassicalFourthNat.BPay_3418
  · exact WuPaper.ClassicalFourthNat.BPay_3419
  · exact WuPaper.ClassicalFourthNat.BPay_3420
  · exact WuPaper.ClassicalFourthNat.BPay_3421
  · exact WuPaper.ClassicalFourthNat.BPay_3422
  · exact WuPaper.ClassicalFourthNat.BPay_3423
  · exact WuPaper.ClassicalFourthNat.BPay_3424
  · exact WuPaper.ClassicalFourthNat.BPay_3425
  · exact WuPaper.ClassicalFourthNat.BPay_3426
  · exact WuPaper.ClassicalFourthNat.BPay_3427
  · exact WuPaper.ClassicalFourthNat.BPay_3428
  · exact WuPaper.ClassicalFourthNat.BPay_3429
  · exact WuPaper.ClassicalFourthNat.BPay_3430
  · exact WuPaper.ClassicalFourthNat.BPay_3431
  · exact WuPaper.ClassicalFourthNat.BPay_3432
  · exact WuPaper.ClassicalFourthNat.BPay_3433
  · exact WuPaper.ClassicalFourthNat.BPay_3434
  · exact WuPaper.ClassicalFourthNat.BPay_3435
  · exact WuPaper.ClassicalFourthNat.BPay_3436
  · exact WuPaper.ClassicalFourthNat.BPay_3437
  · exact WuPaper.ClassicalFourthNat.BPay_3438
  · exact WuPaper.ClassicalFourthNat.BPay_3439
  · exact WuPaper.ClassicalFourthNat.BPay_3440
  · exact WuPaper.ClassicalFourthNat.BPay_3441
  · exact WuPaper.ClassicalFourthNat.BPay_3442
  · exact WuPaper.ClassicalFourthNat.BPay_3443
  · exact WuPaper.ClassicalFourthNat.BPay_3444
  · exact WuPaper.ClassicalFourthNat.BPay_3445
  · exact WuPaper.ClassicalFourthNat.BPay_3446
  · exact WuPaper.ClassicalFourthNat.BPay_3447
  · exact WuPaper.ClassicalFourthNat.BPay_3448
  · exact WuPaper.ClassicalFourthNat.BPay_3449
  · exact WuPaper.ClassicalFourthNat.BPay_3450
  · exact WuPaper.ClassicalFourthNat.BPay_3451
  · exact WuPaper.ClassicalFourthNat.BPay_3452
  · exact WuPaper.ClassicalFourthNat.BPay_3453
  · exact WuPaper.ClassicalFourthNat.BPay_3454
  · exact WuPaper.ClassicalFourthNat.BPay_3455
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_053
