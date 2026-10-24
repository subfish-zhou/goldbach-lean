import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay056
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_056 (j : Fin 64) (hj : 64*56+j.val < 10540) :
    BPay (64*56+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_3584
  · exact WuPaper.ClassicalFourthNat.BPay_3585
  · exact WuPaper.ClassicalFourthNat.BPay_3586
  · exact WuPaper.ClassicalFourthNat.BPay_3587
  · exact WuPaper.ClassicalFourthNat.BPay_3588
  · exact WuPaper.ClassicalFourthNat.BPay_3589
  · exact WuPaper.ClassicalFourthNat.BPay_3590
  · exact WuPaper.ClassicalFourthNat.BPay_3591
  · exact WuPaper.ClassicalFourthNat.BPay_3592
  · exact WuPaper.ClassicalFourthNat.BPay_3593
  · exact WuPaper.ClassicalFourthNat.BPay_3594
  · exact WuPaper.ClassicalFourthNat.BPay_3595
  · exact WuPaper.ClassicalFourthNat.BPay_3596
  · exact WuPaper.ClassicalFourthNat.BPay_3597
  · exact WuPaper.ClassicalFourthNat.BPay_3598
  · exact WuPaper.ClassicalFourthNat.BPay_3599
  · exact WuPaper.ClassicalFourthNat.BPay_3600
  · exact WuPaper.ClassicalFourthNat.BPay_3601
  · exact WuPaper.ClassicalFourthNat.BPay_3602
  · exact WuPaper.ClassicalFourthNat.BPay_3603
  · exact WuPaper.ClassicalFourthNat.BPay_3604
  · exact WuPaper.ClassicalFourthNat.BPay_3605
  · exact WuPaper.ClassicalFourthNat.BPay_3606
  · exact WuPaper.ClassicalFourthNat.BPay_3607
  · exact WuPaper.ClassicalFourthNat.BPay_3608
  · exact WuPaper.ClassicalFourthNat.BPay_3609
  · exact WuPaper.ClassicalFourthNat.BPay_3610
  · exact WuPaper.ClassicalFourthNat.BPay_3611
  · exact WuPaper.ClassicalFourthNat.BPay_3612
  · exact WuPaper.ClassicalFourthNat.BPay_3613
  · exact WuPaper.ClassicalFourthNat.BPay_3614
  · exact WuPaper.ClassicalFourthNat.BPay_3615
  · exact WuPaper.ClassicalFourthNat.BPay_3616
  · exact WuPaper.ClassicalFourthNat.BPay_3617
  · exact WuPaper.ClassicalFourthNat.BPay_3618
  · exact WuPaper.ClassicalFourthNat.BPay_3619
  · exact WuPaper.ClassicalFourthNat.BPay_3620
  · exact WuPaper.ClassicalFourthNat.BPay_3621
  · exact WuPaper.ClassicalFourthNat.BPay_3622
  · exact WuPaper.ClassicalFourthNat.BPay_3623
  · exact WuPaper.ClassicalFourthNat.BPay_3624
  · exact WuPaper.ClassicalFourthNat.BPay_3625
  · exact WuPaper.ClassicalFourthNat.BPay_3626
  · exact WuPaper.ClassicalFourthNat.BPay_3627
  · exact WuPaper.ClassicalFourthNat.BPay_3628
  · exact WuPaper.ClassicalFourthNat.BPay_3629
  · exact WuPaper.ClassicalFourthNat.BPay_3630
  · exact WuPaper.ClassicalFourthNat.BPay_3631
  · exact WuPaper.ClassicalFourthNat.BPay_3632
  · exact WuPaper.ClassicalFourthNat.BPay_3633
  · exact WuPaper.ClassicalFourthNat.BPay_3634
  · exact WuPaper.ClassicalFourthNat.BPay_3635
  · exact WuPaper.ClassicalFourthNat.BPay_3636
  · exact WuPaper.ClassicalFourthNat.BPay_3637
  · exact WuPaper.ClassicalFourthNat.BPay_3638
  · exact WuPaper.ClassicalFourthNat.BPay_3639
  · exact WuPaper.ClassicalFourthNat.BPay_3640
  · exact WuPaper.ClassicalFourthNat.BPay_3641
  · exact WuPaper.ClassicalFourthNat.BPay_3642
  · exact WuPaper.ClassicalFourthNat.BPay_3643
  · exact WuPaper.ClassicalFourthNat.BPay_3644
  · exact WuPaper.ClassicalFourthNat.BPay_3645
  · exact WuPaper.ClassicalFourthNat.BPay_3646
  · exact WuPaper.ClassicalFourthNat.BPay_3647
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_056
