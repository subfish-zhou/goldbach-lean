import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay164
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_164 (j : Fin 64) (hj : 64*164+j.val < 10540) :
    BPay (64*164+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_10496
  · exact WuPaper.ClassicalFourthNat.BPay_10497
  · exact WuPaper.ClassicalFourthNat.BPay_10498
  · exact WuPaper.ClassicalFourthNat.BPay_10499
  · exact WuPaper.ClassicalFourthNat.BPay_10500
  · exact WuPaper.ClassicalFourthNat.BPay_10501
  · exact WuPaper.ClassicalFourthNat.BPay_10502
  · exact WuPaper.ClassicalFourthNat.BPay_10503
  · exact WuPaper.ClassicalFourthNat.BPay_10504
  · exact WuPaper.ClassicalFourthNat.BPay_10505
  · exact WuPaper.ClassicalFourthNat.BPay_10506
  · exact WuPaper.ClassicalFourthNat.BPay_10507
  · exact WuPaper.ClassicalFourthNat.BPay_10508
  · exact WuPaper.ClassicalFourthNat.BPay_10509
  · exact WuPaper.ClassicalFourthNat.BPay_10510
  · exact WuPaper.ClassicalFourthNat.BPay_10511
  · exact WuPaper.ClassicalFourthNat.BPay_10512
  · exact WuPaper.ClassicalFourthNat.BPay_10513
  · exact WuPaper.ClassicalFourthNat.BPay_10514
  · exact WuPaper.ClassicalFourthNat.BPay_10515
  · exact WuPaper.ClassicalFourthNat.BPay_10516
  · exact WuPaper.ClassicalFourthNat.BPay_10517
  · exact WuPaper.ClassicalFourthNat.BPay_10518
  · exact WuPaper.ClassicalFourthNat.BPay_10519
  · exact WuPaper.ClassicalFourthNat.BPay_10520
  · exact WuPaper.ClassicalFourthNat.BPay_10521
  · exact WuPaper.ClassicalFourthNat.BPay_10522
  · exact WuPaper.ClassicalFourthNat.BPay_10523
  · exact WuPaper.ClassicalFourthNat.BPay_10524
  · exact WuPaper.ClassicalFourthNat.BPay_10525
  · exact WuPaper.ClassicalFourthNat.BPay_10526
  · exact WuPaper.ClassicalFourthNat.BPay_10527
  · exact WuPaper.ClassicalFourthNat.BPay_10528
  · exact WuPaper.ClassicalFourthNat.BPay_10529
  · exact WuPaper.ClassicalFourthNat.BPay_10530
  · exact WuPaper.ClassicalFourthNat.BPay_10531
  · exact WuPaper.ClassicalFourthNat.BPay_10532
  · exact WuPaper.ClassicalFourthNat.BPay_10533
  · exact WuPaper.ClassicalFourthNat.BPay_10534
  · exact WuPaper.ClassicalFourthNat.BPay_10535
  · exact WuPaper.ClassicalFourthNat.BPay_10536
  · exact WuPaper.ClassicalFourthNat.BPay_10537
  · exact WuPaper.ClassicalFourthNat.BPay_10538
  · exact WuPaper.ClassicalFourthNat.BPay_10539
  · norm_num at hj
  · norm_num at hj
  · norm_num at hj
  · norm_num at hj
  · norm_num at hj
  · norm_num at hj
  · norm_num at hj
  · norm_num at hj
  · norm_num at hj
  · norm_num at hj
  · norm_num at hj
  · norm_num at hj
  · norm_num at hj
  · norm_num at hj
  · norm_num at hj
  · norm_num at hj
  · norm_num at hj
  · norm_num at hj
  · norm_num at hj
  · norm_num at hj
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_164
