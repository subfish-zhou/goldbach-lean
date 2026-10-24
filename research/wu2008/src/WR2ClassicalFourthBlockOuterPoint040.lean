import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatOuterPoint040
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem OuterPoint_block_040 (j : Fin 64) (hj : 64*40+j.val < 10541) :
    OuterPoint (64*40+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2560
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2561
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2562
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2563
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2564
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2565
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2566
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2567
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2568
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2569
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2570
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2571
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2572
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2573
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2574
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2575
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2576
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2577
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2578
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2579
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2580
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2581
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2582
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2583
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2584
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2585
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2586
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2587
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2588
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2589
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2590
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2591
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2592
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2593
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2594
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2595
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2596
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2597
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2598
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2599
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2600
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2601
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2602
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2603
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2604
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2605
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2606
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2607
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2608
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2609
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2610
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2611
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2612
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2613
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2614
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2615
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2616
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2617
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2618
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2619
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2620
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2621
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2622
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2623
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.OuterPoint_block_040
