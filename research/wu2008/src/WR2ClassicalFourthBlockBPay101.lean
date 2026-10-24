import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay101
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_101 (j : Fin 64) (hj : 64*101+j.val < 10540) :
    BPay (64*101+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_6464
  · exact WuPaper.ClassicalFourthNat.BPay_6465
  · exact WuPaper.ClassicalFourthNat.BPay_6466
  · exact WuPaper.ClassicalFourthNat.BPay_6467
  · exact WuPaper.ClassicalFourthNat.BPay_6468
  · exact WuPaper.ClassicalFourthNat.BPay_6469
  · exact WuPaper.ClassicalFourthNat.BPay_6470
  · exact WuPaper.ClassicalFourthNat.BPay_6471
  · exact WuPaper.ClassicalFourthNat.BPay_6472
  · exact WuPaper.ClassicalFourthNat.BPay_6473
  · exact WuPaper.ClassicalFourthNat.BPay_6474
  · exact WuPaper.ClassicalFourthNat.BPay_6475
  · exact WuPaper.ClassicalFourthNat.BPay_6476
  · exact WuPaper.ClassicalFourthNat.BPay_6477
  · exact WuPaper.ClassicalFourthNat.BPay_6478
  · exact WuPaper.ClassicalFourthNat.BPay_6479
  · exact WuPaper.ClassicalFourthNat.BPay_6480
  · exact WuPaper.ClassicalFourthNat.BPay_6481
  · exact WuPaper.ClassicalFourthNat.BPay_6482
  · exact WuPaper.ClassicalFourthNat.BPay_6483
  · exact WuPaper.ClassicalFourthNat.BPay_6484
  · exact WuPaper.ClassicalFourthNat.BPay_6485
  · exact WuPaper.ClassicalFourthNat.BPay_6486
  · exact WuPaper.ClassicalFourthNat.BPay_6487
  · exact WuPaper.ClassicalFourthNat.BPay_6488
  · exact WuPaper.ClassicalFourthNat.BPay_6489
  · exact WuPaper.ClassicalFourthNat.BPay_6490
  · exact WuPaper.ClassicalFourthNat.BPay_6491
  · exact WuPaper.ClassicalFourthNat.BPay_6492
  · exact WuPaper.ClassicalFourthNat.BPay_6493
  · exact WuPaper.ClassicalFourthNat.BPay_6494
  · exact WuPaper.ClassicalFourthNat.BPay_6495
  · exact WuPaper.ClassicalFourthNat.BPay_6496
  · exact WuPaper.ClassicalFourthNat.BPay_6497
  · exact WuPaper.ClassicalFourthNat.BPay_6498
  · exact WuPaper.ClassicalFourthNat.BPay_6499
  · exact WuPaper.ClassicalFourthNat.BPay_6500
  · exact WuPaper.ClassicalFourthNat.BPay_6501
  · exact WuPaper.ClassicalFourthNat.BPay_6502
  · exact WuPaper.ClassicalFourthNat.BPay_6503
  · exact WuPaper.ClassicalFourthNat.BPay_6504
  · exact WuPaper.ClassicalFourthNat.BPay_6505
  · exact WuPaper.ClassicalFourthNat.BPay_6506
  · exact WuPaper.ClassicalFourthNat.BPay_6507
  · exact WuPaper.ClassicalFourthNat.BPay_6508
  · exact WuPaper.ClassicalFourthNat.BPay_6509
  · exact WuPaper.ClassicalFourthNat.BPay_6510
  · exact WuPaper.ClassicalFourthNat.BPay_6511
  · exact WuPaper.ClassicalFourthNat.BPay_6512
  · exact WuPaper.ClassicalFourthNat.BPay_6513
  · exact WuPaper.ClassicalFourthNat.BPay_6514
  · exact WuPaper.ClassicalFourthNat.BPay_6515
  · exact WuPaper.ClassicalFourthNat.BPay_6516
  · exact WuPaper.ClassicalFourthNat.BPay_6517
  · exact WuPaper.ClassicalFourthNat.BPay_6518
  · exact WuPaper.ClassicalFourthNat.BPay_6519
  · exact WuPaper.ClassicalFourthNat.BPay_6520
  · exact WuPaper.ClassicalFourthNat.BPay_6521
  · exact WuPaper.ClassicalFourthNat.BPay_6522
  · exact WuPaper.ClassicalFourthNat.BPay_6523
  · exact WuPaper.ClassicalFourthNat.BPay_6524
  · exact WuPaper.ClassicalFourthNat.BPay_6525
  · exact WuPaper.ClassicalFourthNat.BPay_6526
  · exact WuPaper.ClassicalFourthNat.BPay_6527
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_101
