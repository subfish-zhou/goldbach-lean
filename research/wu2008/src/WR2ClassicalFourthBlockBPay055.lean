import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay055
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_055 (j : Fin 64) (hj : 64*55+j.val < 10540) :
    BPay (64*55+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_3520
  · exact WuPaper.ClassicalFourthNat.BPay_3521
  · exact WuPaper.ClassicalFourthNat.BPay_3522
  · exact WuPaper.ClassicalFourthNat.BPay_3523
  · exact WuPaper.ClassicalFourthNat.BPay_3524
  · exact WuPaper.ClassicalFourthNat.BPay_3525
  · exact WuPaper.ClassicalFourthNat.BPay_3526
  · exact WuPaper.ClassicalFourthNat.BPay_3527
  · exact WuPaper.ClassicalFourthNat.BPay_3528
  · exact WuPaper.ClassicalFourthNat.BPay_3529
  · exact WuPaper.ClassicalFourthNat.BPay_3530
  · exact WuPaper.ClassicalFourthNat.BPay_3531
  · exact WuPaper.ClassicalFourthNat.BPay_3532
  · exact WuPaper.ClassicalFourthNat.BPay_3533
  · exact WuPaper.ClassicalFourthNat.BPay_3534
  · exact WuPaper.ClassicalFourthNat.BPay_3535
  · exact WuPaper.ClassicalFourthNat.BPay_3536
  · exact WuPaper.ClassicalFourthNat.BPay_3537
  · exact WuPaper.ClassicalFourthNat.BPay_3538
  · exact WuPaper.ClassicalFourthNat.BPay_3539
  · exact WuPaper.ClassicalFourthNat.BPay_3540
  · exact WuPaper.ClassicalFourthNat.BPay_3541
  · exact WuPaper.ClassicalFourthNat.BPay_3542
  · exact WuPaper.ClassicalFourthNat.BPay_3543
  · exact WuPaper.ClassicalFourthNat.BPay_3544
  · exact WuPaper.ClassicalFourthNat.BPay_3545
  · exact WuPaper.ClassicalFourthNat.BPay_3546
  · exact WuPaper.ClassicalFourthNat.BPay_3547
  · exact WuPaper.ClassicalFourthNat.BPay_3548
  · exact WuPaper.ClassicalFourthNat.BPay_3549
  · exact WuPaper.ClassicalFourthNat.BPay_3550
  · exact WuPaper.ClassicalFourthNat.BPay_3551
  · exact WuPaper.ClassicalFourthNat.BPay_3552
  · exact WuPaper.ClassicalFourthNat.BPay_3553
  · exact WuPaper.ClassicalFourthNat.BPay_3554
  · exact WuPaper.ClassicalFourthNat.BPay_3555
  · exact WuPaper.ClassicalFourthNat.BPay_3556
  · exact WuPaper.ClassicalFourthNat.BPay_3557
  · exact WuPaper.ClassicalFourthNat.BPay_3558
  · exact WuPaper.ClassicalFourthNat.BPay_3559
  · exact WuPaper.ClassicalFourthNat.BPay_3560
  · exact WuPaper.ClassicalFourthNat.BPay_3561
  · exact WuPaper.ClassicalFourthNat.BPay_3562
  · exact WuPaper.ClassicalFourthNat.BPay_3563
  · exact WuPaper.ClassicalFourthNat.BPay_3564
  · exact WuPaper.ClassicalFourthNat.BPay_3565
  · exact WuPaper.ClassicalFourthNat.BPay_3566
  · exact WuPaper.ClassicalFourthNat.BPay_3567
  · exact WuPaper.ClassicalFourthNat.BPay_3568
  · exact WuPaper.ClassicalFourthNat.BPay_3569
  · exact WuPaper.ClassicalFourthNat.BPay_3570
  · exact WuPaper.ClassicalFourthNat.BPay_3571
  · exact WuPaper.ClassicalFourthNat.BPay_3572
  · exact WuPaper.ClassicalFourthNat.BPay_3573
  · exact WuPaper.ClassicalFourthNat.BPay_3574
  · exact WuPaper.ClassicalFourthNat.BPay_3575
  · exact WuPaper.ClassicalFourthNat.BPay_3576
  · exact WuPaper.ClassicalFourthNat.BPay_3577
  · exact WuPaper.ClassicalFourthNat.BPay_3578
  · exact WuPaper.ClassicalFourthNat.BPay_3579
  · exact WuPaper.ClassicalFourthNat.BPay_3580
  · exact WuPaper.ClassicalFourthNat.BPay_3581
  · exact WuPaper.ClassicalFourthNat.BPay_3582
  · exact WuPaper.ClassicalFourthNat.BPay_3583
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_055
