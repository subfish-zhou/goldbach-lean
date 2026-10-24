import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatouterPay164
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem outerPay_block_164 (j : Fin 64) (hj : 64*164+j.val < 10540) :
    OuterPay (64*164+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.outerPay_10496
  · exact WuPaper.ClassicalFourthNat.outerPay_10497
  · exact WuPaper.ClassicalFourthNat.outerPay_10498
  · exact WuPaper.ClassicalFourthNat.outerPay_10499
  · exact WuPaper.ClassicalFourthNat.outerPay_10500
  · exact WuPaper.ClassicalFourthNat.outerPay_10501
  · exact WuPaper.ClassicalFourthNat.outerPay_10502
  · exact WuPaper.ClassicalFourthNat.outerPay_10503
  · exact WuPaper.ClassicalFourthNat.outerPay_10504
  · exact WuPaper.ClassicalFourthNat.outerPay_10505
  · exact WuPaper.ClassicalFourthNat.outerPay_10506
  · exact WuPaper.ClassicalFourthNat.outerPay_10507
  · exact WuPaper.ClassicalFourthNat.outerPay_10508
  · exact WuPaper.ClassicalFourthNat.outerPay_10509
  · exact WuPaper.ClassicalFourthNat.outerPay_10510
  · exact WuPaper.ClassicalFourthNat.outerPay_10511
  · exact WuPaper.ClassicalFourthNat.outerPay_10512
  · exact WuPaper.ClassicalFourthNat.outerPay_10513
  · exact WuPaper.ClassicalFourthNat.outerPay_10514
  · exact WuPaper.ClassicalFourthNat.outerPay_10515
  · exact WuPaper.ClassicalFourthNat.outerPay_10516
  · exact WuPaper.ClassicalFourthNat.outerPay_10517
  · exact WuPaper.ClassicalFourthNat.outerPay_10518
  · exact WuPaper.ClassicalFourthNat.outerPay_10519
  · exact WuPaper.ClassicalFourthNat.outerPay_10520
  · exact WuPaper.ClassicalFourthNat.outerPay_10521
  · exact WuPaper.ClassicalFourthNat.outerPay_10522
  · exact WuPaper.ClassicalFourthNat.outerPay_10523
  · exact WuPaper.ClassicalFourthNat.outerPay_10524
  · exact WuPaper.ClassicalFourthNat.outerPay_10525
  · exact WuPaper.ClassicalFourthNat.outerPay_10526
  · exact WuPaper.ClassicalFourthNat.outerPay_10527
  · exact WuPaper.ClassicalFourthNat.outerPay_10528
  · exact WuPaper.ClassicalFourthNat.outerPay_10529
  · exact WuPaper.ClassicalFourthNat.outerPay_10530
  · exact WuPaper.ClassicalFourthNat.outerPay_10531
  · exact WuPaper.ClassicalFourthNat.outerPay_10532
  · exact WuPaper.ClassicalFourthNat.outerPay_10533
  · exact WuPaper.ClassicalFourthNat.outerPay_10534
  · exact WuPaper.ClassicalFourthNat.outerPay_10535
  · exact WuPaper.ClassicalFourthNat.outerPay_10536
  · exact WuPaper.ClassicalFourthNat.outerPay_10537
  · exact WuPaper.ClassicalFourthNat.outerPay_10538
  · exact WuPaper.ClassicalFourthNat.outerPay_10539
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
#print axioms WuPaper.ClassicalFourthConditions.outerPay_block_164
