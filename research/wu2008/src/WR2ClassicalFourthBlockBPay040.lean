import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay040
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_040 (j : Fin 64) (hj : 64*40+j.val < 10540) :
    BPay (64*40+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_2560
  · exact WuPaper.ClassicalFourthNat.BPay_2561
  · exact WuPaper.ClassicalFourthNat.BPay_2562
  · exact WuPaper.ClassicalFourthNat.BPay_2563
  · exact WuPaper.ClassicalFourthNat.BPay_2564
  · exact WuPaper.ClassicalFourthNat.BPay_2565
  · exact WuPaper.ClassicalFourthNat.BPay_2566
  · exact WuPaper.ClassicalFourthNat.BPay_2567
  · exact WuPaper.ClassicalFourthNat.BPay_2568
  · exact WuPaper.ClassicalFourthNat.BPay_2569
  · exact WuPaper.ClassicalFourthNat.BPay_2570
  · exact WuPaper.ClassicalFourthNat.BPay_2571
  · exact WuPaper.ClassicalFourthNat.BPay_2572
  · exact WuPaper.ClassicalFourthNat.BPay_2573
  · exact WuPaper.ClassicalFourthNat.BPay_2574
  · exact WuPaper.ClassicalFourthNat.BPay_2575
  · exact WuPaper.ClassicalFourthNat.BPay_2576
  · exact WuPaper.ClassicalFourthNat.BPay_2577
  · exact WuPaper.ClassicalFourthNat.BPay_2578
  · exact WuPaper.ClassicalFourthNat.BPay_2579
  · exact WuPaper.ClassicalFourthNat.BPay_2580
  · exact WuPaper.ClassicalFourthNat.BPay_2581
  · exact WuPaper.ClassicalFourthNat.BPay_2582
  · exact WuPaper.ClassicalFourthNat.BPay_2583
  · exact WuPaper.ClassicalFourthNat.BPay_2584
  · exact WuPaper.ClassicalFourthNat.BPay_2585
  · exact WuPaper.ClassicalFourthNat.BPay_2586
  · exact WuPaper.ClassicalFourthNat.BPay_2587
  · exact WuPaper.ClassicalFourthNat.BPay_2588
  · exact WuPaper.ClassicalFourthNat.BPay_2589
  · exact WuPaper.ClassicalFourthNat.BPay_2590
  · exact WuPaper.ClassicalFourthNat.BPay_2591
  · exact WuPaper.ClassicalFourthNat.BPay_2592
  · exact WuPaper.ClassicalFourthNat.BPay_2593
  · exact WuPaper.ClassicalFourthNat.BPay_2594
  · exact WuPaper.ClassicalFourthNat.BPay_2595
  · exact WuPaper.ClassicalFourthNat.BPay_2596
  · exact WuPaper.ClassicalFourthNat.BPay_2597
  · exact WuPaper.ClassicalFourthNat.BPay_2598
  · exact WuPaper.ClassicalFourthNat.BPay_2599
  · exact WuPaper.ClassicalFourthNat.BPay_2600
  · exact WuPaper.ClassicalFourthNat.BPay_2601
  · exact WuPaper.ClassicalFourthNat.BPay_2602
  · exact WuPaper.ClassicalFourthNat.BPay_2603
  · exact WuPaper.ClassicalFourthNat.BPay_2604
  · exact WuPaper.ClassicalFourthNat.BPay_2605
  · exact WuPaper.ClassicalFourthNat.BPay_2606
  · exact WuPaper.ClassicalFourthNat.BPay_2607
  · exact WuPaper.ClassicalFourthNat.BPay_2608
  · exact WuPaper.ClassicalFourthNat.BPay_2609
  · exact WuPaper.ClassicalFourthNat.BPay_2610
  · exact WuPaper.ClassicalFourthNat.BPay_2611
  · exact WuPaper.ClassicalFourthNat.BPay_2612
  · exact WuPaper.ClassicalFourthNat.BPay_2613
  · exact WuPaper.ClassicalFourthNat.BPay_2614
  · exact WuPaper.ClassicalFourthNat.BPay_2615
  · exact WuPaper.ClassicalFourthNat.BPay_2616
  · exact WuPaper.ClassicalFourthNat.BPay_2617
  · exact WuPaper.ClassicalFourthNat.BPay_2618
  · exact WuPaper.ClassicalFourthNat.BPay_2619
  · exact WuPaper.ClassicalFourthNat.BPay_2620
  · exact WuPaper.ClassicalFourthNat.BPay_2621
  · exact WuPaper.ClassicalFourthNat.BPay_2622
  · exact WuPaper.ClassicalFourthNat.BPay_2623
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_040
