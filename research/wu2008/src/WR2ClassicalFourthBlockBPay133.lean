import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay133
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_133 (j : Fin 64) (hj : 64*133+j.val < 10540) :
    BPay (64*133+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_8512
  · exact WuPaper.ClassicalFourthNat.BPay_8513
  · exact WuPaper.ClassicalFourthNat.BPay_8514
  · exact WuPaper.ClassicalFourthNat.BPay_8515
  · exact WuPaper.ClassicalFourthNat.BPay_8516
  · exact WuPaper.ClassicalFourthNat.BPay_8517
  · exact WuPaper.ClassicalFourthNat.BPay_8518
  · exact WuPaper.ClassicalFourthNat.BPay_8519
  · exact WuPaper.ClassicalFourthNat.BPay_8520
  · exact WuPaper.ClassicalFourthNat.BPay_8521
  · exact WuPaper.ClassicalFourthNat.BPay_8522
  · exact WuPaper.ClassicalFourthNat.BPay_8523
  · exact WuPaper.ClassicalFourthNat.BPay_8524
  · exact WuPaper.ClassicalFourthNat.BPay_8525
  · exact WuPaper.ClassicalFourthNat.BPay_8526
  · exact WuPaper.ClassicalFourthNat.BPay_8527
  · exact WuPaper.ClassicalFourthNat.BPay_8528
  · exact WuPaper.ClassicalFourthNat.BPay_8529
  · exact WuPaper.ClassicalFourthNat.BPay_8530
  · exact WuPaper.ClassicalFourthNat.BPay_8531
  · exact WuPaper.ClassicalFourthNat.BPay_8532
  · exact WuPaper.ClassicalFourthNat.BPay_8533
  · exact WuPaper.ClassicalFourthNat.BPay_8534
  · exact WuPaper.ClassicalFourthNat.BPay_8535
  · exact WuPaper.ClassicalFourthNat.BPay_8536
  · exact WuPaper.ClassicalFourthNat.BPay_8537
  · exact WuPaper.ClassicalFourthNat.BPay_8538
  · exact WuPaper.ClassicalFourthNat.BPay_8539
  · exact WuPaper.ClassicalFourthNat.BPay_8540
  · exact WuPaper.ClassicalFourthNat.BPay_8541
  · exact WuPaper.ClassicalFourthNat.BPay_8542
  · exact WuPaper.ClassicalFourthNat.BPay_8543
  · exact WuPaper.ClassicalFourthNat.BPay_8544
  · exact WuPaper.ClassicalFourthNat.BPay_8545
  · exact WuPaper.ClassicalFourthNat.BPay_8546
  · exact WuPaper.ClassicalFourthNat.BPay_8547
  · exact WuPaper.ClassicalFourthNat.BPay_8548
  · exact WuPaper.ClassicalFourthNat.BPay_8549
  · exact WuPaper.ClassicalFourthNat.BPay_8550
  · exact WuPaper.ClassicalFourthNat.BPay_8551
  · exact WuPaper.ClassicalFourthNat.BPay_8552
  · exact WuPaper.ClassicalFourthNat.BPay_8553
  · exact WuPaper.ClassicalFourthNat.BPay_8554
  · exact WuPaper.ClassicalFourthNat.BPay_8555
  · exact WuPaper.ClassicalFourthNat.BPay_8556
  · exact WuPaper.ClassicalFourthNat.BPay_8557
  · exact WuPaper.ClassicalFourthNat.BPay_8558
  · exact WuPaper.ClassicalFourthNat.BPay_8559
  · exact WuPaper.ClassicalFourthNat.BPay_8560
  · exact WuPaper.ClassicalFourthNat.BPay_8561
  · exact WuPaper.ClassicalFourthNat.BPay_8562
  · exact WuPaper.ClassicalFourthNat.BPay_8563
  · exact WuPaper.ClassicalFourthNat.BPay_8564
  · exact WuPaper.ClassicalFourthNat.BPay_8565
  · exact WuPaper.ClassicalFourthNat.BPay_8566
  · exact WuPaper.ClassicalFourthNat.BPay_8567
  · exact WuPaper.ClassicalFourthNat.BPay_8568
  · exact WuPaper.ClassicalFourthNat.BPay_8569
  · exact WuPaper.ClassicalFourthNat.BPay_8570
  · exact WuPaper.ClassicalFourthNat.BPay_8571
  · exact WuPaper.ClassicalFourthNat.BPay_8572
  · exact WuPaper.ClassicalFourthNat.BPay_8573
  · exact WuPaper.ClassicalFourthNat.BPay_8574
  · exact WuPaper.ClassicalFourthNat.BPay_8575
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_133
