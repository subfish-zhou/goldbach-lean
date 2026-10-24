import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay086
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_086 (j : Fin 64) (hj : 64*86+j.val < 10540) :
    BPay (64*86+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_5504
  · exact WuPaper.ClassicalFourthNat.BPay_5505
  · exact WuPaper.ClassicalFourthNat.BPay_5506
  · exact WuPaper.ClassicalFourthNat.BPay_5507
  · exact WuPaper.ClassicalFourthNat.BPay_5508
  · exact WuPaper.ClassicalFourthNat.BPay_5509
  · exact WuPaper.ClassicalFourthNat.BPay_5510
  · exact WuPaper.ClassicalFourthNat.BPay_5511
  · exact WuPaper.ClassicalFourthNat.BPay_5512
  · exact WuPaper.ClassicalFourthNat.BPay_5513
  · exact WuPaper.ClassicalFourthNat.BPay_5514
  · exact WuPaper.ClassicalFourthNat.BPay_5515
  · exact WuPaper.ClassicalFourthNat.BPay_5516
  · exact WuPaper.ClassicalFourthNat.BPay_5517
  · exact WuPaper.ClassicalFourthNat.BPay_5518
  · exact WuPaper.ClassicalFourthNat.BPay_5519
  · exact WuPaper.ClassicalFourthNat.BPay_5520
  · exact WuPaper.ClassicalFourthNat.BPay_5521
  · exact WuPaper.ClassicalFourthNat.BPay_5522
  · exact WuPaper.ClassicalFourthNat.BPay_5523
  · exact WuPaper.ClassicalFourthNat.BPay_5524
  · exact WuPaper.ClassicalFourthNat.BPay_5525
  · exact WuPaper.ClassicalFourthNat.BPay_5526
  · exact WuPaper.ClassicalFourthNat.BPay_5527
  · exact WuPaper.ClassicalFourthNat.BPay_5528
  · exact WuPaper.ClassicalFourthNat.BPay_5529
  · exact WuPaper.ClassicalFourthNat.BPay_5530
  · exact WuPaper.ClassicalFourthNat.BPay_5531
  · exact WuPaper.ClassicalFourthNat.BPay_5532
  · exact WuPaper.ClassicalFourthNat.BPay_5533
  · exact WuPaper.ClassicalFourthNat.BPay_5534
  · exact WuPaper.ClassicalFourthNat.BPay_5535
  · exact WuPaper.ClassicalFourthNat.BPay_5536
  · exact WuPaper.ClassicalFourthNat.BPay_5537
  · exact WuPaper.ClassicalFourthNat.BPay_5538
  · exact WuPaper.ClassicalFourthNat.BPay_5539
  · exact WuPaper.ClassicalFourthNat.BPay_5540
  · exact WuPaper.ClassicalFourthNat.BPay_5541
  · exact WuPaper.ClassicalFourthNat.BPay_5542
  · exact WuPaper.ClassicalFourthNat.BPay_5543
  · exact WuPaper.ClassicalFourthNat.BPay_5544
  · exact WuPaper.ClassicalFourthNat.BPay_5545
  · exact WuPaper.ClassicalFourthNat.BPay_5546
  · exact WuPaper.ClassicalFourthNat.BPay_5547
  · exact WuPaper.ClassicalFourthNat.BPay_5548
  · exact WuPaper.ClassicalFourthNat.BPay_5549
  · exact WuPaper.ClassicalFourthNat.BPay_5550
  · exact WuPaper.ClassicalFourthNat.BPay_5551
  · exact WuPaper.ClassicalFourthNat.BPay_5552
  · exact WuPaper.ClassicalFourthNat.BPay_5553
  · exact WuPaper.ClassicalFourthNat.BPay_5554
  · exact WuPaper.ClassicalFourthNat.BPay_5555
  · exact WuPaper.ClassicalFourthNat.BPay_5556
  · exact WuPaper.ClassicalFourthNat.BPay_5557
  · exact WuPaper.ClassicalFourthNat.BPay_5558
  · exact WuPaper.ClassicalFourthNat.BPay_5559
  · exact WuPaper.ClassicalFourthNat.BPay_5560
  · exact WuPaper.ClassicalFourthNat.BPay_5561
  · exact WuPaper.ClassicalFourthNat.BPay_5562
  · exact WuPaper.ClassicalFourthNat.BPay_5563
  · exact WuPaper.ClassicalFourthNat.BPay_5564
  · exact WuPaper.ClassicalFourthNat.BPay_5565
  · exact WuPaper.ClassicalFourthNat.BPay_5566
  · exact WuPaper.ClassicalFourthNat.BPay_5567
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_086
