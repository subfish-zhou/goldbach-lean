import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay041
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_041 (j : Fin 64) (hj : 64*41+j.val < 10540) :
    BPay (64*41+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_2624
  · exact WuPaper.ClassicalFourthNat.BPay_2625
  · exact WuPaper.ClassicalFourthNat.BPay_2626
  · exact WuPaper.ClassicalFourthNat.BPay_2627
  · exact WuPaper.ClassicalFourthNat.BPay_2628
  · exact WuPaper.ClassicalFourthNat.BPay_2629
  · exact WuPaper.ClassicalFourthNat.BPay_2630
  · exact WuPaper.ClassicalFourthNat.BPay_2631
  · exact WuPaper.ClassicalFourthNat.BPay_2632
  · exact WuPaper.ClassicalFourthNat.BPay_2633
  · exact WuPaper.ClassicalFourthNat.BPay_2634
  · exact WuPaper.ClassicalFourthNat.BPay_2635
  · exact WuPaper.ClassicalFourthNat.BPay_2636
  · exact WuPaper.ClassicalFourthNat.BPay_2637
  · exact WuPaper.ClassicalFourthNat.BPay_2638
  · exact WuPaper.ClassicalFourthNat.BPay_2639
  · exact WuPaper.ClassicalFourthNat.BPay_2640
  · exact WuPaper.ClassicalFourthNat.BPay_2641
  · exact WuPaper.ClassicalFourthNat.BPay_2642
  · exact WuPaper.ClassicalFourthNat.BPay_2643
  · exact WuPaper.ClassicalFourthNat.BPay_2644
  · exact WuPaper.ClassicalFourthNat.BPay_2645
  · exact WuPaper.ClassicalFourthNat.BPay_2646
  · exact WuPaper.ClassicalFourthNat.BPay_2647
  · exact WuPaper.ClassicalFourthNat.BPay_2648
  · exact WuPaper.ClassicalFourthNat.BPay_2649
  · exact WuPaper.ClassicalFourthNat.BPay_2650
  · exact WuPaper.ClassicalFourthNat.BPay_2651
  · exact WuPaper.ClassicalFourthNat.BPay_2652
  · exact WuPaper.ClassicalFourthNat.BPay_2653
  · exact WuPaper.ClassicalFourthNat.BPay_2654
  · exact WuPaper.ClassicalFourthNat.BPay_2655
  · exact WuPaper.ClassicalFourthNat.BPay_2656
  · exact WuPaper.ClassicalFourthNat.BPay_2657
  · exact WuPaper.ClassicalFourthNat.BPay_2658
  · exact WuPaper.ClassicalFourthNat.BPay_2659
  · exact WuPaper.ClassicalFourthNat.BPay_2660
  · exact WuPaper.ClassicalFourthNat.BPay_2661
  · exact WuPaper.ClassicalFourthNat.BPay_2662
  · exact WuPaper.ClassicalFourthNat.BPay_2663
  · exact WuPaper.ClassicalFourthNat.BPay_2664
  · exact WuPaper.ClassicalFourthNat.BPay_2665
  · exact WuPaper.ClassicalFourthNat.BPay_2666
  · exact WuPaper.ClassicalFourthNat.BPay_2667
  · exact WuPaper.ClassicalFourthNat.BPay_2668
  · exact WuPaper.ClassicalFourthNat.BPay_2669
  · exact WuPaper.ClassicalFourthNat.BPay_2670
  · exact WuPaper.ClassicalFourthNat.BPay_2671
  · exact WuPaper.ClassicalFourthNat.BPay_2672
  · exact WuPaper.ClassicalFourthNat.BPay_2673
  · exact WuPaper.ClassicalFourthNat.BPay_2674
  · exact WuPaper.ClassicalFourthNat.BPay_2675
  · exact WuPaper.ClassicalFourthNat.BPay_2676
  · exact WuPaper.ClassicalFourthNat.BPay_2677
  · exact WuPaper.ClassicalFourthNat.BPay_2678
  · exact WuPaper.ClassicalFourthNat.BPay_2679
  · exact WuPaper.ClassicalFourthNat.BPay_2680
  · exact WuPaper.ClassicalFourthNat.BPay_2681
  · exact WuPaper.ClassicalFourthNat.BPay_2682
  · exact WuPaper.ClassicalFourthNat.BPay_2683
  · exact WuPaper.ClassicalFourthNat.BPay_2684
  · exact WuPaper.ClassicalFourthNat.BPay_2685
  · exact WuPaper.ClassicalFourthNat.BPay_2686
  · exact WuPaper.ClassicalFourthNat.BPay_2687
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_041
