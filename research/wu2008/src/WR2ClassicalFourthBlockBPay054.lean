import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay054
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_054 (j : Fin 64) (hj : 64*54+j.val < 10540) :
    BPay (64*54+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_3456
  · exact WuPaper.ClassicalFourthNat.BPay_3457
  · exact WuPaper.ClassicalFourthNat.BPay_3458
  · exact WuPaper.ClassicalFourthNat.BPay_3459
  · exact WuPaper.ClassicalFourthNat.BPay_3460
  · exact WuPaper.ClassicalFourthNat.BPay_3461
  · exact WuPaper.ClassicalFourthNat.BPay_3462
  · exact WuPaper.ClassicalFourthNat.BPay_3463
  · exact WuPaper.ClassicalFourthNat.BPay_3464
  · exact WuPaper.ClassicalFourthNat.BPay_3465
  · exact WuPaper.ClassicalFourthNat.BPay_3466
  · exact WuPaper.ClassicalFourthNat.BPay_3467
  · exact WuPaper.ClassicalFourthNat.BPay_3468
  · exact WuPaper.ClassicalFourthNat.BPay_3469
  · exact WuPaper.ClassicalFourthNat.BPay_3470
  · exact WuPaper.ClassicalFourthNat.BPay_3471
  · exact WuPaper.ClassicalFourthNat.BPay_3472
  · exact WuPaper.ClassicalFourthNat.BPay_3473
  · exact WuPaper.ClassicalFourthNat.BPay_3474
  · exact WuPaper.ClassicalFourthNat.BPay_3475
  · exact WuPaper.ClassicalFourthNat.BPay_3476
  · exact WuPaper.ClassicalFourthNat.BPay_3477
  · exact WuPaper.ClassicalFourthNat.BPay_3478
  · exact WuPaper.ClassicalFourthNat.BPay_3479
  · exact WuPaper.ClassicalFourthNat.BPay_3480
  · exact WuPaper.ClassicalFourthNat.BPay_3481
  · exact WuPaper.ClassicalFourthNat.BPay_3482
  · exact WuPaper.ClassicalFourthNat.BPay_3483
  · exact WuPaper.ClassicalFourthNat.BPay_3484
  · exact WuPaper.ClassicalFourthNat.BPay_3485
  · exact WuPaper.ClassicalFourthNat.BPay_3486
  · exact WuPaper.ClassicalFourthNat.BPay_3487
  · exact WuPaper.ClassicalFourthNat.BPay_3488
  · exact WuPaper.ClassicalFourthNat.BPay_3489
  · exact WuPaper.ClassicalFourthNat.BPay_3490
  · exact WuPaper.ClassicalFourthNat.BPay_3491
  · exact WuPaper.ClassicalFourthNat.BPay_3492
  · exact WuPaper.ClassicalFourthNat.BPay_3493
  · exact WuPaper.ClassicalFourthNat.BPay_3494
  · exact WuPaper.ClassicalFourthNat.BPay_3495
  · exact WuPaper.ClassicalFourthNat.BPay_3496
  · exact WuPaper.ClassicalFourthNat.BPay_3497
  · exact WuPaper.ClassicalFourthNat.BPay_3498
  · exact WuPaper.ClassicalFourthNat.BPay_3499
  · exact WuPaper.ClassicalFourthNat.BPay_3500
  · exact WuPaper.ClassicalFourthNat.BPay_3501
  · exact WuPaper.ClassicalFourthNat.BPay_3502
  · exact WuPaper.ClassicalFourthNat.BPay_3503
  · exact WuPaper.ClassicalFourthNat.BPay_3504
  · exact WuPaper.ClassicalFourthNat.BPay_3505
  · exact WuPaper.ClassicalFourthNat.BPay_3506
  · exact WuPaper.ClassicalFourthNat.BPay_3507
  · exact WuPaper.ClassicalFourthNat.BPay_3508
  · exact WuPaper.ClassicalFourthNat.BPay_3509
  · exact WuPaper.ClassicalFourthNat.BPay_3510
  · exact WuPaper.ClassicalFourthNat.BPay_3511
  · exact WuPaper.ClassicalFourthNat.BPay_3512
  · exact WuPaper.ClassicalFourthNat.BPay_3513
  · exact WuPaper.ClassicalFourthNat.BPay_3514
  · exact WuPaper.ClassicalFourthNat.BPay_3515
  · exact WuPaper.ClassicalFourthNat.BPay_3516
  · exact WuPaper.ClassicalFourthNat.BPay_3517
  · exact WuPaper.ClassicalFourthNat.BPay_3518
  · exact WuPaper.ClassicalFourthNat.BPay_3519
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_054
