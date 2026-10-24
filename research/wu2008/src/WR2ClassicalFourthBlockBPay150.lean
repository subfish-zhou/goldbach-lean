import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay150
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_150 (j : Fin 64) (hj : 64*150+j.val < 10540) :
    BPay (64*150+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_9600
  · exact WuPaper.ClassicalFourthNat.BPay_9601
  · exact WuPaper.ClassicalFourthNat.BPay_9602
  · exact WuPaper.ClassicalFourthNat.BPay_9603
  · exact WuPaper.ClassicalFourthNat.BPay_9604
  · exact WuPaper.ClassicalFourthNat.BPay_9605
  · exact WuPaper.ClassicalFourthNat.BPay_9606
  · exact WuPaper.ClassicalFourthNat.BPay_9607
  · exact WuPaper.ClassicalFourthNat.BPay_9608
  · exact WuPaper.ClassicalFourthNat.BPay_9609
  · exact WuPaper.ClassicalFourthNat.BPay_9610
  · exact WuPaper.ClassicalFourthNat.BPay_9611
  · exact WuPaper.ClassicalFourthNat.BPay_9612
  · exact WuPaper.ClassicalFourthNat.BPay_9613
  · exact WuPaper.ClassicalFourthNat.BPay_9614
  · exact WuPaper.ClassicalFourthNat.BPay_9615
  · exact WuPaper.ClassicalFourthNat.BPay_9616
  · exact WuPaper.ClassicalFourthNat.BPay_9617
  · exact WuPaper.ClassicalFourthNat.BPay_9618
  · exact WuPaper.ClassicalFourthNat.BPay_9619
  · exact WuPaper.ClassicalFourthNat.BPay_9620
  · exact WuPaper.ClassicalFourthNat.BPay_9621
  · exact WuPaper.ClassicalFourthNat.BPay_9622
  · exact WuPaper.ClassicalFourthNat.BPay_9623
  · exact WuPaper.ClassicalFourthNat.BPay_9624
  · exact WuPaper.ClassicalFourthNat.BPay_9625
  · exact WuPaper.ClassicalFourthNat.BPay_9626
  · exact WuPaper.ClassicalFourthNat.BPay_9627
  · exact WuPaper.ClassicalFourthNat.BPay_9628
  · exact WuPaper.ClassicalFourthNat.BPay_9629
  · exact WuPaper.ClassicalFourthNat.BPay_9630
  · exact WuPaper.ClassicalFourthNat.BPay_9631
  · exact WuPaper.ClassicalFourthNat.BPay_9632
  · exact WuPaper.ClassicalFourthNat.BPay_9633
  · exact WuPaper.ClassicalFourthNat.BPay_9634
  · exact WuPaper.ClassicalFourthNat.BPay_9635
  · exact WuPaper.ClassicalFourthNat.BPay_9636
  · exact WuPaper.ClassicalFourthNat.BPay_9637
  · exact WuPaper.ClassicalFourthNat.BPay_9638
  · exact WuPaper.ClassicalFourthNat.BPay_9639
  · exact WuPaper.ClassicalFourthNat.BPay_9640
  · exact WuPaper.ClassicalFourthNat.BPay_9641
  · exact WuPaper.ClassicalFourthNat.BPay_9642
  · exact WuPaper.ClassicalFourthNat.BPay_9643
  · exact WuPaper.ClassicalFourthNat.BPay_9644
  · exact WuPaper.ClassicalFourthNat.BPay_9645
  · exact WuPaper.ClassicalFourthNat.BPay_9646
  · exact WuPaper.ClassicalFourthNat.BPay_9647
  · exact WuPaper.ClassicalFourthNat.BPay_9648
  · exact WuPaper.ClassicalFourthNat.BPay_9649
  · exact WuPaper.ClassicalFourthNat.BPay_9650
  · exact WuPaper.ClassicalFourthNat.BPay_9651
  · exact WuPaper.ClassicalFourthNat.BPay_9652
  · exact WuPaper.ClassicalFourthNat.BPay_9653
  · exact WuPaper.ClassicalFourthNat.BPay_9654
  · exact WuPaper.ClassicalFourthNat.BPay_9655
  · exact WuPaper.ClassicalFourthNat.BPay_9656
  · exact WuPaper.ClassicalFourthNat.BPay_9657
  · exact WuPaper.ClassicalFourthNat.BPay_9658
  · exact WuPaper.ClassicalFourthNat.BPay_9659
  · exact WuPaper.ClassicalFourthNat.BPay_9660
  · exact WuPaper.ClassicalFourthNat.BPay_9661
  · exact WuPaper.ClassicalFourthNat.BPay_9662
  · exact WuPaper.ClassicalFourthNat.BPay_9663
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_150
