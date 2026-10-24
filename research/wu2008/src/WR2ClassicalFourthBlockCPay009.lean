import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatCPay009
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem CPay_block_009 (j : Fin 64) (hj : 64*9+j.val < 2540) :
    CPay (64*9+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.CPay_576
  · exact WuPaper.ClassicalFourthNat.CPay_577
  · exact WuPaper.ClassicalFourthNat.CPay_578
  · exact WuPaper.ClassicalFourthNat.CPay_579
  · exact WuPaper.ClassicalFourthNat.CPay_580
  · exact WuPaper.ClassicalFourthNat.CPay_581
  · exact WuPaper.ClassicalFourthNat.CPay_582
  · exact WuPaper.ClassicalFourthNat.CPay_583
  · exact WuPaper.ClassicalFourthNat.CPay_584
  · exact WuPaper.ClassicalFourthNat.CPay_585
  · exact WuPaper.ClassicalFourthNat.CPay_586
  · exact WuPaper.ClassicalFourthNat.CPay_587
  · exact WuPaper.ClassicalFourthNat.CPay_588
  · exact WuPaper.ClassicalFourthNat.CPay_589
  · exact WuPaper.ClassicalFourthNat.CPay_590
  · exact WuPaper.ClassicalFourthNat.CPay_591
  · exact WuPaper.ClassicalFourthNat.CPay_592
  · exact WuPaper.ClassicalFourthNat.CPay_593
  · exact WuPaper.ClassicalFourthNat.CPay_594
  · exact WuPaper.ClassicalFourthNat.CPay_595
  · exact WuPaper.ClassicalFourthNat.CPay_596
  · exact WuPaper.ClassicalFourthNat.CPay_597
  · exact WuPaper.ClassicalFourthNat.CPay_598
  · exact WuPaper.ClassicalFourthNat.CPay_599
  · exact WuPaper.ClassicalFourthNat.CPay_600
  · exact WuPaper.ClassicalFourthNat.CPay_601
  · exact WuPaper.ClassicalFourthNat.CPay_602
  · exact WuPaper.ClassicalFourthNat.CPay_603
  · exact WuPaper.ClassicalFourthNat.CPay_604
  · exact WuPaper.ClassicalFourthNat.CPay_605
  · exact WuPaper.ClassicalFourthNat.CPay_606
  · exact WuPaper.ClassicalFourthNat.CPay_607
  · exact WuPaper.ClassicalFourthNat.CPay_608
  · exact WuPaper.ClassicalFourthNat.CPay_609
  · exact WuPaper.ClassicalFourthNat.CPay_610
  · exact WuPaper.ClassicalFourthNat.CPay_611
  · exact WuPaper.ClassicalFourthNat.CPay_612
  · exact WuPaper.ClassicalFourthNat.CPay_613
  · exact WuPaper.ClassicalFourthNat.CPay_614
  · exact WuPaper.ClassicalFourthNat.CPay_615
  · exact WuPaper.ClassicalFourthNat.CPay_616
  · exact WuPaper.ClassicalFourthNat.CPay_617
  · exact WuPaper.ClassicalFourthNat.CPay_618
  · exact WuPaper.ClassicalFourthNat.CPay_619
  · exact WuPaper.ClassicalFourthNat.CPay_620
  · exact WuPaper.ClassicalFourthNat.CPay_621
  · exact WuPaper.ClassicalFourthNat.CPay_622
  · exact WuPaper.ClassicalFourthNat.CPay_623
  · exact WuPaper.ClassicalFourthNat.CPay_624
  · exact WuPaper.ClassicalFourthNat.CPay_625
  · exact WuPaper.ClassicalFourthNat.CPay_626
  · exact WuPaper.ClassicalFourthNat.CPay_627
  · exact WuPaper.ClassicalFourthNat.CPay_628
  · exact WuPaper.ClassicalFourthNat.CPay_629
  · exact WuPaper.ClassicalFourthNat.CPay_630
  · exact WuPaper.ClassicalFourthNat.CPay_631
  · exact WuPaper.ClassicalFourthNat.CPay_632
  · exact WuPaper.ClassicalFourthNat.CPay_633
  · exact WuPaper.ClassicalFourthNat.CPay_634
  · exact WuPaper.ClassicalFourthNat.CPay_635
  · exact WuPaper.ClassicalFourthNat.CPay_636
  · exact WuPaper.ClassicalFourthNat.CPay_637
  · exact WuPaper.ClassicalFourthNat.CPay_638
  · exact WuPaper.ClassicalFourthNat.CPay_639
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.CPay_block_009
