import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatDPay009
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem DPay_block_009 (j : Fin 64) (hj : 64*9+j.val < 2540) :
    DPay (64*9+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.DPay_576
  · exact WuPaper.ClassicalFourthNat.DPay_577
  · exact WuPaper.ClassicalFourthNat.DPay_578
  · exact WuPaper.ClassicalFourthNat.DPay_579
  · exact WuPaper.ClassicalFourthNat.DPay_580
  · exact WuPaper.ClassicalFourthNat.DPay_581
  · exact WuPaper.ClassicalFourthNat.DPay_582
  · exact WuPaper.ClassicalFourthNat.DPay_583
  · exact WuPaper.ClassicalFourthNat.DPay_584
  · exact WuPaper.ClassicalFourthNat.DPay_585
  · exact WuPaper.ClassicalFourthNat.DPay_586
  · exact WuPaper.ClassicalFourthNat.DPay_587
  · exact WuPaper.ClassicalFourthNat.DPay_588
  · exact WuPaper.ClassicalFourthNat.DPay_589
  · exact WuPaper.ClassicalFourthNat.DPay_590
  · exact WuPaper.ClassicalFourthNat.DPay_591
  · exact WuPaper.ClassicalFourthNat.DPay_592
  · exact WuPaper.ClassicalFourthNat.DPay_593
  · exact WuPaper.ClassicalFourthNat.DPay_594
  · exact WuPaper.ClassicalFourthNat.DPay_595
  · exact WuPaper.ClassicalFourthNat.DPay_596
  · exact WuPaper.ClassicalFourthNat.DPay_597
  · exact WuPaper.ClassicalFourthNat.DPay_598
  · exact WuPaper.ClassicalFourthNat.DPay_599
  · exact WuPaper.ClassicalFourthNat.DPay_600
  · exact WuPaper.ClassicalFourthNat.DPay_601
  · exact WuPaper.ClassicalFourthNat.DPay_602
  · exact WuPaper.ClassicalFourthNat.DPay_603
  · exact WuPaper.ClassicalFourthNat.DPay_604
  · exact WuPaper.ClassicalFourthNat.DPay_605
  · exact WuPaper.ClassicalFourthNat.DPay_606
  · exact WuPaper.ClassicalFourthNat.DPay_607
  · exact WuPaper.ClassicalFourthNat.DPay_608
  · exact WuPaper.ClassicalFourthNat.DPay_609
  · exact WuPaper.ClassicalFourthNat.DPay_610
  · exact WuPaper.ClassicalFourthNat.DPay_611
  · exact WuPaper.ClassicalFourthNat.DPay_612
  · exact WuPaper.ClassicalFourthNat.DPay_613
  · exact WuPaper.ClassicalFourthNat.DPay_614
  · exact WuPaper.ClassicalFourthNat.DPay_615
  · exact WuPaper.ClassicalFourthNat.DPay_616
  · exact WuPaper.ClassicalFourthNat.DPay_617
  · exact WuPaper.ClassicalFourthNat.DPay_618
  · exact WuPaper.ClassicalFourthNat.DPay_619
  · exact WuPaper.ClassicalFourthNat.DPay_620
  · exact WuPaper.ClassicalFourthNat.DPay_621
  · exact WuPaper.ClassicalFourthNat.DPay_622
  · exact WuPaper.ClassicalFourthNat.DPay_623
  · exact WuPaper.ClassicalFourthNat.DPay_624
  · exact WuPaper.ClassicalFourthNat.DPay_625
  · exact WuPaper.ClassicalFourthNat.DPay_626
  · exact WuPaper.ClassicalFourthNat.DPay_627
  · exact WuPaper.ClassicalFourthNat.DPay_628
  · exact WuPaper.ClassicalFourthNat.DPay_629
  · exact WuPaper.ClassicalFourthNat.DPay_630
  · exact WuPaper.ClassicalFourthNat.DPay_631
  · exact WuPaper.ClassicalFourthNat.DPay_632
  · exact WuPaper.ClassicalFourthNat.DPay_633
  · exact WuPaper.ClassicalFourthNat.DPay_634
  · exact WuPaper.ClassicalFourthNat.DPay_635
  · exact WuPaper.ClassicalFourthNat.DPay_636
  · exact WuPaper.ClassicalFourthNat.DPay_637
  · exact WuPaper.ClassicalFourthNat.DPay_638
  · exact WuPaper.ClassicalFourthNat.DPay_639
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.DPay_block_009
