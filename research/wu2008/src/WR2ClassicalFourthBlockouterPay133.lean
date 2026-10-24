import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatouterPay133
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem outerPay_block_133 (j : Fin 64) (hj : 64*133+j.val < 10540) :
    OuterPay (64*133+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.outerPay_8512
  · exact WuPaper.ClassicalFourthNat.outerPay_8513
  · exact WuPaper.ClassicalFourthNat.outerPay_8514
  · exact WuPaper.ClassicalFourthNat.outerPay_8515
  · exact WuPaper.ClassicalFourthNat.outerPay_8516
  · exact WuPaper.ClassicalFourthNat.outerPay_8517
  · exact WuPaper.ClassicalFourthNat.outerPay_8518
  · exact WuPaper.ClassicalFourthNat.outerPay_8519
  · exact WuPaper.ClassicalFourthNat.outerPay_8520
  · exact WuPaper.ClassicalFourthNat.outerPay_8521
  · exact WuPaper.ClassicalFourthNat.outerPay_8522
  · exact WuPaper.ClassicalFourthNat.outerPay_8523
  · exact WuPaper.ClassicalFourthNat.outerPay_8524
  · exact WuPaper.ClassicalFourthNat.outerPay_8525
  · exact WuPaper.ClassicalFourthNat.outerPay_8526
  · exact WuPaper.ClassicalFourthNat.outerPay_8527
  · exact WuPaper.ClassicalFourthNat.outerPay_8528
  · exact WuPaper.ClassicalFourthNat.outerPay_8529
  · exact WuPaper.ClassicalFourthNat.outerPay_8530
  · exact WuPaper.ClassicalFourthNat.outerPay_8531
  · exact WuPaper.ClassicalFourthNat.outerPay_8532
  · exact WuPaper.ClassicalFourthNat.outerPay_8533
  · exact WuPaper.ClassicalFourthNat.outerPay_8534
  · exact WuPaper.ClassicalFourthNat.outerPay_8535
  · exact WuPaper.ClassicalFourthNat.outerPay_8536
  · exact WuPaper.ClassicalFourthNat.outerPay_8537
  · exact WuPaper.ClassicalFourthNat.outerPay_8538
  · exact WuPaper.ClassicalFourthNat.outerPay_8539
  · exact WuPaper.ClassicalFourthNat.outerPay_8540
  · exact WuPaper.ClassicalFourthNat.outerPay_8541
  · exact WuPaper.ClassicalFourthNat.outerPay_8542
  · exact WuPaper.ClassicalFourthNat.outerPay_8543
  · exact WuPaper.ClassicalFourthNat.outerPay_8544
  · exact WuPaper.ClassicalFourthNat.outerPay_8545
  · exact WuPaper.ClassicalFourthNat.outerPay_8546
  · exact WuPaper.ClassicalFourthNat.outerPay_8547
  · exact WuPaper.ClassicalFourthNat.outerPay_8548
  · exact WuPaper.ClassicalFourthNat.outerPay_8549
  · exact WuPaper.ClassicalFourthNat.outerPay_8550
  · exact WuPaper.ClassicalFourthNat.outerPay_8551
  · exact WuPaper.ClassicalFourthNat.outerPay_8552
  · exact WuPaper.ClassicalFourthNat.outerPay_8553
  · exact WuPaper.ClassicalFourthNat.outerPay_8554
  · exact WuPaper.ClassicalFourthNat.outerPay_8555
  · exact WuPaper.ClassicalFourthNat.outerPay_8556
  · exact WuPaper.ClassicalFourthNat.outerPay_8557
  · exact WuPaper.ClassicalFourthNat.outerPay_8558
  · exact WuPaper.ClassicalFourthNat.outerPay_8559
  · exact WuPaper.ClassicalFourthNat.outerPay_8560
  · exact WuPaper.ClassicalFourthNat.outerPay_8561
  · exact WuPaper.ClassicalFourthNat.outerPay_8562
  · exact WuPaper.ClassicalFourthNat.outerPay_8563
  · exact WuPaper.ClassicalFourthNat.outerPay_8564
  · exact WuPaper.ClassicalFourthNat.outerPay_8565
  · exact WuPaper.ClassicalFourthNat.outerPay_8566
  · exact WuPaper.ClassicalFourthNat.outerPay_8567
  · exact WuPaper.ClassicalFourthNat.outerPay_8568
  · exact WuPaper.ClassicalFourthNat.outerPay_8569
  · exact WuPaper.ClassicalFourthNat.outerPay_8570
  · exact WuPaper.ClassicalFourthNat.outerPay_8571
  · exact WuPaper.ClassicalFourthNat.outerPay_8572
  · exact WuPaper.ClassicalFourthNat.outerPay_8573
  · exact WuPaper.ClassicalFourthNat.outerPay_8574
  · exact WuPaper.ClassicalFourthNat.outerPay_8575
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.outerPay_block_133
