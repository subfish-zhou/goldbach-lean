import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatOuterPoint009
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem OuterPoint_block_009 (j : Fin 64) (hj : 64*9+j.val < 10541) :
    OuterPoint (64*9+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.OuterPoint_576
  · exact WuPaper.ClassicalFourthNat.OuterPoint_577
  · exact WuPaper.ClassicalFourthNat.OuterPoint_578
  · exact WuPaper.ClassicalFourthNat.OuterPoint_579
  · exact WuPaper.ClassicalFourthNat.OuterPoint_580
  · exact WuPaper.ClassicalFourthNat.OuterPoint_581
  · exact WuPaper.ClassicalFourthNat.OuterPoint_582
  · exact WuPaper.ClassicalFourthNat.OuterPoint_583
  · exact WuPaper.ClassicalFourthNat.OuterPoint_584
  · exact WuPaper.ClassicalFourthNat.OuterPoint_585
  · exact WuPaper.ClassicalFourthNat.OuterPoint_586
  · exact WuPaper.ClassicalFourthNat.OuterPoint_587
  · exact WuPaper.ClassicalFourthNat.OuterPoint_588
  · exact WuPaper.ClassicalFourthNat.OuterPoint_589
  · exact WuPaper.ClassicalFourthNat.OuterPoint_590
  · exact WuPaper.ClassicalFourthNat.OuterPoint_591
  · exact WuPaper.ClassicalFourthNat.OuterPoint_592
  · exact WuPaper.ClassicalFourthNat.OuterPoint_593
  · exact WuPaper.ClassicalFourthNat.OuterPoint_594
  · exact WuPaper.ClassicalFourthNat.OuterPoint_595
  · exact WuPaper.ClassicalFourthNat.OuterPoint_596
  · exact WuPaper.ClassicalFourthNat.OuterPoint_597
  · exact WuPaper.ClassicalFourthNat.OuterPoint_598
  · exact WuPaper.ClassicalFourthNat.OuterPoint_599
  · exact WuPaper.ClassicalFourthNat.OuterPoint_600
  · exact WuPaper.ClassicalFourthNat.OuterPoint_601
  · exact WuPaper.ClassicalFourthNat.OuterPoint_602
  · exact WuPaper.ClassicalFourthNat.OuterPoint_603
  · exact WuPaper.ClassicalFourthNat.OuterPoint_604
  · exact WuPaper.ClassicalFourthNat.OuterPoint_605
  · exact WuPaper.ClassicalFourthNat.OuterPoint_606
  · exact WuPaper.ClassicalFourthNat.OuterPoint_607
  · exact WuPaper.ClassicalFourthNat.OuterPoint_608
  · exact WuPaper.ClassicalFourthNat.OuterPoint_609
  · exact WuPaper.ClassicalFourthNat.OuterPoint_610
  · exact WuPaper.ClassicalFourthNat.OuterPoint_611
  · exact WuPaper.ClassicalFourthNat.OuterPoint_612
  · exact WuPaper.ClassicalFourthNat.OuterPoint_613
  · exact WuPaper.ClassicalFourthNat.OuterPoint_614
  · exact WuPaper.ClassicalFourthNat.OuterPoint_615
  · exact WuPaper.ClassicalFourthNat.OuterPoint_616
  · exact WuPaper.ClassicalFourthNat.OuterPoint_617
  · exact WuPaper.ClassicalFourthNat.OuterPoint_618
  · exact WuPaper.ClassicalFourthNat.OuterPoint_619
  · exact WuPaper.ClassicalFourthNat.OuterPoint_620
  · exact WuPaper.ClassicalFourthNat.OuterPoint_621
  · exact WuPaper.ClassicalFourthNat.OuterPoint_622
  · exact WuPaper.ClassicalFourthNat.OuterPoint_623
  · exact WuPaper.ClassicalFourthNat.OuterPoint_624
  · exact WuPaper.ClassicalFourthNat.OuterPoint_625
  · exact WuPaper.ClassicalFourthNat.OuterPoint_626
  · exact WuPaper.ClassicalFourthNat.OuterPoint_627
  · exact WuPaper.ClassicalFourthNat.OuterPoint_628
  · exact WuPaper.ClassicalFourthNat.OuterPoint_629
  · exact WuPaper.ClassicalFourthNat.OuterPoint_630
  · exact WuPaper.ClassicalFourthNat.OuterPoint_631
  · exact WuPaper.ClassicalFourthNat.OuterPoint_632
  · exact WuPaper.ClassicalFourthNat.OuterPoint_633
  · exact WuPaper.ClassicalFourthNat.OuterPoint_634
  · exact WuPaper.ClassicalFourthNat.OuterPoint_635
  · exact WuPaper.ClassicalFourthNat.OuterPoint_636
  · exact WuPaper.ClassicalFourthNat.OuterPoint_637
  · exact WuPaper.ClassicalFourthNat.OuterPoint_638
  · exact WuPaper.ClassicalFourthNat.OuterPoint_639
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.OuterPoint_block_009
