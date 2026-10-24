import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatOuterPoint164
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem OuterPoint_block_164 (j : Fin 64) (hj : 64*164+j.val < 10541) :
    OuterPoint (64*164+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10496
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10497
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10498
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10499
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10500
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10501
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10502
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10503
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10504
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10505
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10506
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10507
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10508
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10509
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10510
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10511
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10512
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10513
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10514
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10515
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10516
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10517
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10518
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10519
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10520
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10521
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10522
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10523
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10524
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10525
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10526
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10527
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10528
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10529
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10530
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10531
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10532
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10533
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10534
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10535
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10536
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10537
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10538
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10539
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10540
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
#print axioms WuPaper.ClassicalFourthConditions.OuterPoint_block_164
