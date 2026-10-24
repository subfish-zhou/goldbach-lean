import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatouterPay101
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem outerPay_block_101 (j : Fin 64) (hj : 64*101+j.val < 10540) :
    OuterPay (64*101+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.outerPay_6464
  · exact WuPaper.ClassicalFourthNat.outerPay_6465
  · exact WuPaper.ClassicalFourthNat.outerPay_6466
  · exact WuPaper.ClassicalFourthNat.outerPay_6467
  · exact WuPaper.ClassicalFourthNat.outerPay_6468
  · exact WuPaper.ClassicalFourthNat.outerPay_6469
  · exact WuPaper.ClassicalFourthNat.outerPay_6470
  · exact WuPaper.ClassicalFourthNat.outerPay_6471
  · exact WuPaper.ClassicalFourthNat.outerPay_6472
  · exact WuPaper.ClassicalFourthNat.outerPay_6473
  · exact WuPaper.ClassicalFourthNat.outerPay_6474
  · exact WuPaper.ClassicalFourthNat.outerPay_6475
  · exact WuPaper.ClassicalFourthNat.outerPay_6476
  · exact WuPaper.ClassicalFourthNat.outerPay_6477
  · exact WuPaper.ClassicalFourthNat.outerPay_6478
  · exact WuPaper.ClassicalFourthNat.outerPay_6479
  · exact WuPaper.ClassicalFourthNat.outerPay_6480
  · exact WuPaper.ClassicalFourthNat.outerPay_6481
  · exact WuPaper.ClassicalFourthNat.outerPay_6482
  · exact WuPaper.ClassicalFourthNat.outerPay_6483
  · exact WuPaper.ClassicalFourthNat.outerPay_6484
  · exact WuPaper.ClassicalFourthNat.outerPay_6485
  · exact WuPaper.ClassicalFourthNat.outerPay_6486
  · exact WuPaper.ClassicalFourthNat.outerPay_6487
  · exact WuPaper.ClassicalFourthNat.outerPay_6488
  · exact WuPaper.ClassicalFourthNat.outerPay_6489
  · exact WuPaper.ClassicalFourthNat.outerPay_6490
  · exact WuPaper.ClassicalFourthNat.outerPay_6491
  · exact WuPaper.ClassicalFourthNat.outerPay_6492
  · exact WuPaper.ClassicalFourthNat.outerPay_6493
  · exact WuPaper.ClassicalFourthNat.outerPay_6494
  · exact WuPaper.ClassicalFourthNat.outerPay_6495
  · exact WuPaper.ClassicalFourthNat.outerPay_6496
  · exact WuPaper.ClassicalFourthNat.outerPay_6497
  · exact WuPaper.ClassicalFourthNat.outerPay_6498
  · exact WuPaper.ClassicalFourthNat.outerPay_6499
  · exact WuPaper.ClassicalFourthNat.outerPay_6500
  · exact WuPaper.ClassicalFourthNat.outerPay_6501
  · exact WuPaper.ClassicalFourthNat.outerPay_6502
  · exact WuPaper.ClassicalFourthNat.outerPay_6503
  · exact WuPaper.ClassicalFourthNat.outerPay_6504
  · exact WuPaper.ClassicalFourthNat.outerPay_6505
  · exact WuPaper.ClassicalFourthNat.outerPay_6506
  · exact WuPaper.ClassicalFourthNat.outerPay_6507
  · exact WuPaper.ClassicalFourthNat.outerPay_6508
  · exact WuPaper.ClassicalFourthNat.outerPay_6509
  · exact WuPaper.ClassicalFourthNat.outerPay_6510
  · exact WuPaper.ClassicalFourthNat.outerPay_6511
  · exact WuPaper.ClassicalFourthNat.outerPay_6512
  · exact WuPaper.ClassicalFourthNat.outerPay_6513
  · exact WuPaper.ClassicalFourthNat.outerPay_6514
  · exact WuPaper.ClassicalFourthNat.outerPay_6515
  · exact WuPaper.ClassicalFourthNat.outerPay_6516
  · exact WuPaper.ClassicalFourthNat.outerPay_6517
  · exact WuPaper.ClassicalFourthNat.outerPay_6518
  · exact WuPaper.ClassicalFourthNat.outerPay_6519
  · exact WuPaper.ClassicalFourthNat.outerPay_6520
  · exact WuPaper.ClassicalFourthNat.outerPay_6521
  · exact WuPaper.ClassicalFourthNat.outerPay_6522
  · exact WuPaper.ClassicalFourthNat.outerPay_6523
  · exact WuPaper.ClassicalFourthNat.outerPay_6524
  · exact WuPaper.ClassicalFourthNat.outerPay_6525
  · exact WuPaper.ClassicalFourthNat.outerPay_6526
  · exact WuPaper.ClassicalFourthNat.outerPay_6527
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.outerPay_block_101
