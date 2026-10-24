import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatouterPay009
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem outerPay_block_009 (j : Fin 64) (hj : 64*9+j.val < 10540) :
    OuterPay (64*9+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.outerPay_576
  · exact WuPaper.ClassicalFourthNat.outerPay_577
  · exact WuPaper.ClassicalFourthNat.outerPay_578
  · exact WuPaper.ClassicalFourthNat.outerPay_579
  · exact WuPaper.ClassicalFourthNat.outerPay_580
  · exact WuPaper.ClassicalFourthNat.outerPay_581
  · exact WuPaper.ClassicalFourthNat.outerPay_582
  · exact WuPaper.ClassicalFourthNat.outerPay_583
  · exact WuPaper.ClassicalFourthNat.outerPay_584
  · exact WuPaper.ClassicalFourthNat.outerPay_585
  · exact WuPaper.ClassicalFourthNat.outerPay_586
  · exact WuPaper.ClassicalFourthNat.outerPay_587
  · exact WuPaper.ClassicalFourthNat.outerPay_588
  · exact WuPaper.ClassicalFourthNat.outerPay_589
  · exact WuPaper.ClassicalFourthNat.outerPay_590
  · exact WuPaper.ClassicalFourthNat.outerPay_591
  · exact WuPaper.ClassicalFourthNat.outerPay_592
  · exact WuPaper.ClassicalFourthNat.outerPay_593
  · exact WuPaper.ClassicalFourthNat.outerPay_594
  · exact WuPaper.ClassicalFourthNat.outerPay_595
  · exact WuPaper.ClassicalFourthNat.outerPay_596
  · exact WuPaper.ClassicalFourthNat.outerPay_597
  · exact WuPaper.ClassicalFourthNat.outerPay_598
  · exact WuPaper.ClassicalFourthNat.outerPay_599
  · exact WuPaper.ClassicalFourthNat.outerPay_600
  · exact WuPaper.ClassicalFourthNat.outerPay_601
  · exact WuPaper.ClassicalFourthNat.outerPay_602
  · exact WuPaper.ClassicalFourthNat.outerPay_603
  · exact WuPaper.ClassicalFourthNat.outerPay_604
  · exact WuPaper.ClassicalFourthNat.outerPay_605
  · exact WuPaper.ClassicalFourthNat.outerPay_606
  · exact WuPaper.ClassicalFourthNat.outerPay_607
  · exact WuPaper.ClassicalFourthNat.outerPay_608
  · exact WuPaper.ClassicalFourthNat.outerPay_609
  · exact WuPaper.ClassicalFourthNat.outerPay_610
  · exact WuPaper.ClassicalFourthNat.outerPay_611
  · exact WuPaper.ClassicalFourthNat.outerPay_612
  · exact WuPaper.ClassicalFourthNat.outerPay_613
  · exact WuPaper.ClassicalFourthNat.outerPay_614
  · exact WuPaper.ClassicalFourthNat.outerPay_615
  · exact WuPaper.ClassicalFourthNat.outerPay_616
  · exact WuPaper.ClassicalFourthNat.outerPay_617
  · exact WuPaper.ClassicalFourthNat.outerPay_618
  · exact WuPaper.ClassicalFourthNat.outerPay_619
  · exact WuPaper.ClassicalFourthNat.outerPay_620
  · exact WuPaper.ClassicalFourthNat.outerPay_621
  · exact WuPaper.ClassicalFourthNat.outerPay_622
  · exact WuPaper.ClassicalFourthNat.outerPay_623
  · exact WuPaper.ClassicalFourthNat.outerPay_624
  · exact WuPaper.ClassicalFourthNat.outerPay_625
  · exact WuPaper.ClassicalFourthNat.outerPay_626
  · exact WuPaper.ClassicalFourthNat.outerPay_627
  · exact WuPaper.ClassicalFourthNat.outerPay_628
  · exact WuPaper.ClassicalFourthNat.outerPay_629
  · exact WuPaper.ClassicalFourthNat.outerPay_630
  · exact WuPaper.ClassicalFourthNat.outerPay_631
  · exact WuPaper.ClassicalFourthNat.outerPay_632
  · exact WuPaper.ClassicalFourthNat.outerPay_633
  · exact WuPaper.ClassicalFourthNat.outerPay_634
  · exact WuPaper.ClassicalFourthNat.outerPay_635
  · exact WuPaper.ClassicalFourthNat.outerPay_636
  · exact WuPaper.ClassicalFourthNat.outerPay_637
  · exact WuPaper.ClassicalFourthNat.outerPay_638
  · exact WuPaper.ClassicalFourthNat.outerPay_639
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.outerPay_block_009
