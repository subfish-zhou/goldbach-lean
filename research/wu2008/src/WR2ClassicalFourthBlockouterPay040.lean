import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatouterPay040
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem outerPay_block_040 (j : Fin 64) (hj : 64*40+j.val < 10540) :
    OuterPay (64*40+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.outerPay_2560
  · exact WuPaper.ClassicalFourthNat.outerPay_2561
  · exact WuPaper.ClassicalFourthNat.outerPay_2562
  · exact WuPaper.ClassicalFourthNat.outerPay_2563
  · exact WuPaper.ClassicalFourthNat.outerPay_2564
  · exact WuPaper.ClassicalFourthNat.outerPay_2565
  · exact WuPaper.ClassicalFourthNat.outerPay_2566
  · exact WuPaper.ClassicalFourthNat.outerPay_2567
  · exact WuPaper.ClassicalFourthNat.outerPay_2568
  · exact WuPaper.ClassicalFourthNat.outerPay_2569
  · exact WuPaper.ClassicalFourthNat.outerPay_2570
  · exact WuPaper.ClassicalFourthNat.outerPay_2571
  · exact WuPaper.ClassicalFourthNat.outerPay_2572
  · exact WuPaper.ClassicalFourthNat.outerPay_2573
  · exact WuPaper.ClassicalFourthNat.outerPay_2574
  · exact WuPaper.ClassicalFourthNat.outerPay_2575
  · exact WuPaper.ClassicalFourthNat.outerPay_2576
  · exact WuPaper.ClassicalFourthNat.outerPay_2577
  · exact WuPaper.ClassicalFourthNat.outerPay_2578
  · exact WuPaper.ClassicalFourthNat.outerPay_2579
  · exact WuPaper.ClassicalFourthNat.outerPay_2580
  · exact WuPaper.ClassicalFourthNat.outerPay_2581
  · exact WuPaper.ClassicalFourthNat.outerPay_2582
  · exact WuPaper.ClassicalFourthNat.outerPay_2583
  · exact WuPaper.ClassicalFourthNat.outerPay_2584
  · exact WuPaper.ClassicalFourthNat.outerPay_2585
  · exact WuPaper.ClassicalFourthNat.outerPay_2586
  · exact WuPaper.ClassicalFourthNat.outerPay_2587
  · exact WuPaper.ClassicalFourthNat.outerPay_2588
  · exact WuPaper.ClassicalFourthNat.outerPay_2589
  · exact WuPaper.ClassicalFourthNat.outerPay_2590
  · exact WuPaper.ClassicalFourthNat.outerPay_2591
  · exact WuPaper.ClassicalFourthNat.outerPay_2592
  · exact WuPaper.ClassicalFourthNat.outerPay_2593
  · exact WuPaper.ClassicalFourthNat.outerPay_2594
  · exact WuPaper.ClassicalFourthNat.outerPay_2595
  · exact WuPaper.ClassicalFourthNat.outerPay_2596
  · exact WuPaper.ClassicalFourthNat.outerPay_2597
  · exact WuPaper.ClassicalFourthNat.outerPay_2598
  · exact WuPaper.ClassicalFourthNat.outerPay_2599
  · exact WuPaper.ClassicalFourthNat.outerPay_2600
  · exact WuPaper.ClassicalFourthNat.outerPay_2601
  · exact WuPaper.ClassicalFourthNat.outerPay_2602
  · exact WuPaper.ClassicalFourthNat.outerPay_2603
  · exact WuPaper.ClassicalFourthNat.outerPay_2604
  · exact WuPaper.ClassicalFourthNat.outerPay_2605
  · exact WuPaper.ClassicalFourthNat.outerPay_2606
  · exact WuPaper.ClassicalFourthNat.outerPay_2607
  · exact WuPaper.ClassicalFourthNat.outerPay_2608
  · exact WuPaper.ClassicalFourthNat.outerPay_2609
  · exact WuPaper.ClassicalFourthNat.outerPay_2610
  · exact WuPaper.ClassicalFourthNat.outerPay_2611
  · exact WuPaper.ClassicalFourthNat.outerPay_2612
  · exact WuPaper.ClassicalFourthNat.outerPay_2613
  · exact WuPaper.ClassicalFourthNat.outerPay_2614
  · exact WuPaper.ClassicalFourthNat.outerPay_2615
  · exact WuPaper.ClassicalFourthNat.outerPay_2616
  · exact WuPaper.ClassicalFourthNat.outerPay_2617
  · exact WuPaper.ClassicalFourthNat.outerPay_2618
  · exact WuPaper.ClassicalFourthNat.outerPay_2619
  · exact WuPaper.ClassicalFourthNat.outerPay_2620
  · exact WuPaper.ClassicalFourthNat.outerPay_2621
  · exact WuPaper.ClassicalFourthNat.outerPay_2622
  · exact WuPaper.ClassicalFourthNat.outerPay_2623
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.outerPay_block_040
