import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatouterPay150
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem outerPay_block_150 (j : Fin 64) (hj : 64*150+j.val < 10540) :
    OuterPay (64*150+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.outerPay_9600
  · exact WuPaper.ClassicalFourthNat.outerPay_9601
  · exact WuPaper.ClassicalFourthNat.outerPay_9602
  · exact WuPaper.ClassicalFourthNat.outerPay_9603
  · exact WuPaper.ClassicalFourthNat.outerPay_9604
  · exact WuPaper.ClassicalFourthNat.outerPay_9605
  · exact WuPaper.ClassicalFourthNat.outerPay_9606
  · exact WuPaper.ClassicalFourthNat.outerPay_9607
  · exact WuPaper.ClassicalFourthNat.outerPay_9608
  · exact WuPaper.ClassicalFourthNat.outerPay_9609
  · exact WuPaper.ClassicalFourthNat.outerPay_9610
  · exact WuPaper.ClassicalFourthNat.outerPay_9611
  · exact WuPaper.ClassicalFourthNat.outerPay_9612
  · exact WuPaper.ClassicalFourthNat.outerPay_9613
  · exact WuPaper.ClassicalFourthNat.outerPay_9614
  · exact WuPaper.ClassicalFourthNat.outerPay_9615
  · exact WuPaper.ClassicalFourthNat.outerPay_9616
  · exact WuPaper.ClassicalFourthNat.outerPay_9617
  · exact WuPaper.ClassicalFourthNat.outerPay_9618
  · exact WuPaper.ClassicalFourthNat.outerPay_9619
  · exact WuPaper.ClassicalFourthNat.outerPay_9620
  · exact WuPaper.ClassicalFourthNat.outerPay_9621
  · exact WuPaper.ClassicalFourthNat.outerPay_9622
  · exact WuPaper.ClassicalFourthNat.outerPay_9623
  · exact WuPaper.ClassicalFourthNat.outerPay_9624
  · exact WuPaper.ClassicalFourthNat.outerPay_9625
  · exact WuPaper.ClassicalFourthNat.outerPay_9626
  · exact WuPaper.ClassicalFourthNat.outerPay_9627
  · exact WuPaper.ClassicalFourthNat.outerPay_9628
  · exact WuPaper.ClassicalFourthNat.outerPay_9629
  · exact WuPaper.ClassicalFourthNat.outerPay_9630
  · exact WuPaper.ClassicalFourthNat.outerPay_9631
  · exact WuPaper.ClassicalFourthNat.outerPay_9632
  · exact WuPaper.ClassicalFourthNat.outerPay_9633
  · exact WuPaper.ClassicalFourthNat.outerPay_9634
  · exact WuPaper.ClassicalFourthNat.outerPay_9635
  · exact WuPaper.ClassicalFourthNat.outerPay_9636
  · exact WuPaper.ClassicalFourthNat.outerPay_9637
  · exact WuPaper.ClassicalFourthNat.outerPay_9638
  · exact WuPaper.ClassicalFourthNat.outerPay_9639
  · exact WuPaper.ClassicalFourthNat.outerPay_9640
  · exact WuPaper.ClassicalFourthNat.outerPay_9641
  · exact WuPaper.ClassicalFourthNat.outerPay_9642
  · exact WuPaper.ClassicalFourthNat.outerPay_9643
  · exact WuPaper.ClassicalFourthNat.outerPay_9644
  · exact WuPaper.ClassicalFourthNat.outerPay_9645
  · exact WuPaper.ClassicalFourthNat.outerPay_9646
  · exact WuPaper.ClassicalFourthNat.outerPay_9647
  · exact WuPaper.ClassicalFourthNat.outerPay_9648
  · exact WuPaper.ClassicalFourthNat.outerPay_9649
  · exact WuPaper.ClassicalFourthNat.outerPay_9650
  · exact WuPaper.ClassicalFourthNat.outerPay_9651
  · exact WuPaper.ClassicalFourthNat.outerPay_9652
  · exact WuPaper.ClassicalFourthNat.outerPay_9653
  · exact WuPaper.ClassicalFourthNat.outerPay_9654
  · exact WuPaper.ClassicalFourthNat.outerPay_9655
  · exact WuPaper.ClassicalFourthNat.outerPay_9656
  · exact WuPaper.ClassicalFourthNat.outerPay_9657
  · exact WuPaper.ClassicalFourthNat.outerPay_9658
  · exact WuPaper.ClassicalFourthNat.outerPay_9659
  · exact WuPaper.ClassicalFourthNat.outerPay_9660
  · exact WuPaper.ClassicalFourthNat.outerPay_9661
  · exact WuPaper.ClassicalFourthNat.outerPay_9662
  · exact WuPaper.ClassicalFourthNat.outerPay_9663
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.outerPay_block_150
