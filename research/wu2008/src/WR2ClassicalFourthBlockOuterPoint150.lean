import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatOuterPoint150
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem OuterPoint_block_150 (j : Fin 64) (hj : 64*150+j.val < 10541) :
    OuterPoint (64*150+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9600
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9601
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9602
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9603
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9604
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9605
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9606
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9607
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9608
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9609
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9610
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9611
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9612
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9613
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9614
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9615
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9616
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9617
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9618
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9619
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9620
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9621
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9622
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9623
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9624
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9625
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9626
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9627
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9628
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9629
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9630
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9631
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9632
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9633
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9634
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9635
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9636
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9637
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9638
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9639
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9640
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9641
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9642
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9643
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9644
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9645
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9646
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9647
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9648
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9649
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9650
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9651
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9652
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9653
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9654
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9655
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9656
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9657
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9658
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9659
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9660
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9661
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9662
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9663
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.OuterPoint_block_150
