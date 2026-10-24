import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatOuterPoint101
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem OuterPoint_block_101 (j : Fin 64) (hj : 64*101+j.val < 10541) :
    OuterPoint (64*101+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6464
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6465
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6466
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6467
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6468
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6469
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6470
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6471
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6472
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6473
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6474
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6475
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6476
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6477
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6478
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6479
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6480
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6481
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6482
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6483
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6484
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6485
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6486
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6487
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6488
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6489
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6490
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6491
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6492
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6493
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6494
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6495
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6496
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6497
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6498
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6499
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6500
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6501
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6502
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6503
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6504
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6505
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6506
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6507
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6508
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6509
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6510
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6511
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6512
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6513
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6514
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6515
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6516
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6517
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6518
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6519
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6520
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6521
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6522
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6523
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6524
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6525
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6526
  · exact WuPaper.ClassicalFourthNat.OuterPoint_6527
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.OuterPoint_block_101
