import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay009
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_009 (j : Fin 64) (hj : 64*9+j.val < 10540) :
    BPay (64*9+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_576
  · exact WuPaper.ClassicalFourthNat.BPay_577
  · exact WuPaper.ClassicalFourthNat.BPay_578
  · exact WuPaper.ClassicalFourthNat.BPay_579
  · exact WuPaper.ClassicalFourthNat.BPay_580
  · exact WuPaper.ClassicalFourthNat.BPay_581
  · exact WuPaper.ClassicalFourthNat.BPay_582
  · exact WuPaper.ClassicalFourthNat.BPay_583
  · exact WuPaper.ClassicalFourthNat.BPay_584
  · exact WuPaper.ClassicalFourthNat.BPay_585
  · exact WuPaper.ClassicalFourthNat.BPay_586
  · exact WuPaper.ClassicalFourthNat.BPay_587
  · exact WuPaper.ClassicalFourthNat.BPay_588
  · exact WuPaper.ClassicalFourthNat.BPay_589
  · exact WuPaper.ClassicalFourthNat.BPay_590
  · exact WuPaper.ClassicalFourthNat.BPay_591
  · exact WuPaper.ClassicalFourthNat.BPay_592
  · exact WuPaper.ClassicalFourthNat.BPay_593
  · exact WuPaper.ClassicalFourthNat.BPay_594
  · exact WuPaper.ClassicalFourthNat.BPay_595
  · exact WuPaper.ClassicalFourthNat.BPay_596
  · exact WuPaper.ClassicalFourthNat.BPay_597
  · exact WuPaper.ClassicalFourthNat.BPay_598
  · exact WuPaper.ClassicalFourthNat.BPay_599
  · exact WuPaper.ClassicalFourthNat.BPay_600
  · exact WuPaper.ClassicalFourthNat.BPay_601
  · exact WuPaper.ClassicalFourthNat.BPay_602
  · exact WuPaper.ClassicalFourthNat.BPay_603
  · exact WuPaper.ClassicalFourthNat.BPay_604
  · exact WuPaper.ClassicalFourthNat.BPay_605
  · exact WuPaper.ClassicalFourthNat.BPay_606
  · exact WuPaper.ClassicalFourthNat.BPay_607
  · exact WuPaper.ClassicalFourthNat.BPay_608
  · exact WuPaper.ClassicalFourthNat.BPay_609
  · exact WuPaper.ClassicalFourthNat.BPay_610
  · exact WuPaper.ClassicalFourthNat.BPay_611
  · exact WuPaper.ClassicalFourthNat.BPay_612
  · exact WuPaper.ClassicalFourthNat.BPay_613
  · exact WuPaper.ClassicalFourthNat.BPay_614
  · exact WuPaper.ClassicalFourthNat.BPay_615
  · exact WuPaper.ClassicalFourthNat.BPay_616
  · exact WuPaper.ClassicalFourthNat.BPay_617
  · exact WuPaper.ClassicalFourthNat.BPay_618
  · exact WuPaper.ClassicalFourthNat.BPay_619
  · exact WuPaper.ClassicalFourthNat.BPay_620
  · exact WuPaper.ClassicalFourthNat.BPay_621
  · exact WuPaper.ClassicalFourthNat.BPay_622
  · exact WuPaper.ClassicalFourthNat.BPay_623
  · exact WuPaper.ClassicalFourthNat.BPay_624
  · exact WuPaper.ClassicalFourthNat.BPay_625
  · exact WuPaper.ClassicalFourthNat.BPay_626
  · exact WuPaper.ClassicalFourthNat.BPay_627
  · exact WuPaper.ClassicalFourthNat.BPay_628
  · exact WuPaper.ClassicalFourthNat.BPay_629
  · exact WuPaper.ClassicalFourthNat.BPay_630
  · exact WuPaper.ClassicalFourthNat.BPay_631
  · exact WuPaper.ClassicalFourthNat.BPay_632
  · exact WuPaper.ClassicalFourthNat.BPay_633
  · exact WuPaper.ClassicalFourthNat.BPay_634
  · exact WuPaper.ClassicalFourthNat.BPay_635
  · exact WuPaper.ClassicalFourthNat.BPay_636
  · exact WuPaper.ClassicalFourthNat.BPay_637
  · exact WuPaper.ClassicalFourthNat.BPay_638
  · exact WuPaper.ClassicalFourthNat.BPay_639
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_009
