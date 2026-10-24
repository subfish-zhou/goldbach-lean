import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay042
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_042 (j : Fin 64) (hj : 64*42+j.val < 10540) :
    BPay (64*42+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_2688
  · exact WuPaper.ClassicalFourthNat.BPay_2689
  · exact WuPaper.ClassicalFourthNat.BPay_2690
  · exact WuPaper.ClassicalFourthNat.BPay_2691
  · exact WuPaper.ClassicalFourthNat.BPay_2692
  · exact WuPaper.ClassicalFourthNat.BPay_2693
  · exact WuPaper.ClassicalFourthNat.BPay_2694
  · exact WuPaper.ClassicalFourthNat.BPay_2695
  · exact WuPaper.ClassicalFourthNat.BPay_2696
  · exact WuPaper.ClassicalFourthNat.BPay_2697
  · exact WuPaper.ClassicalFourthNat.BPay_2698
  · exact WuPaper.ClassicalFourthNat.BPay_2699
  · exact WuPaper.ClassicalFourthNat.BPay_2700
  · exact WuPaper.ClassicalFourthNat.BPay_2701
  · exact WuPaper.ClassicalFourthNat.BPay_2702
  · exact WuPaper.ClassicalFourthNat.BPay_2703
  · exact WuPaper.ClassicalFourthNat.BPay_2704
  · exact WuPaper.ClassicalFourthNat.BPay_2705
  · exact WuPaper.ClassicalFourthNat.BPay_2706
  · exact WuPaper.ClassicalFourthNat.BPay_2707
  · exact WuPaper.ClassicalFourthNat.BPay_2708
  · exact WuPaper.ClassicalFourthNat.BPay_2709
  · exact WuPaper.ClassicalFourthNat.BPay_2710
  · exact WuPaper.ClassicalFourthNat.BPay_2711
  · exact WuPaper.ClassicalFourthNat.BPay_2712
  · exact WuPaper.ClassicalFourthNat.BPay_2713
  · exact WuPaper.ClassicalFourthNat.BPay_2714
  · exact WuPaper.ClassicalFourthNat.BPay_2715
  · exact WuPaper.ClassicalFourthNat.BPay_2716
  · exact WuPaper.ClassicalFourthNat.BPay_2717
  · exact WuPaper.ClassicalFourthNat.BPay_2718
  · exact WuPaper.ClassicalFourthNat.BPay_2719
  · exact WuPaper.ClassicalFourthNat.BPay_2720
  · exact WuPaper.ClassicalFourthNat.BPay_2721
  · exact WuPaper.ClassicalFourthNat.BPay_2722
  · exact WuPaper.ClassicalFourthNat.BPay_2723
  · exact WuPaper.ClassicalFourthNat.BPay_2724
  · exact WuPaper.ClassicalFourthNat.BPay_2725
  · exact WuPaper.ClassicalFourthNat.BPay_2726
  · exact WuPaper.ClassicalFourthNat.BPay_2727
  · exact WuPaper.ClassicalFourthNat.BPay_2728
  · exact WuPaper.ClassicalFourthNat.BPay_2729
  · exact WuPaper.ClassicalFourthNat.BPay_2730
  · exact WuPaper.ClassicalFourthNat.BPay_2731
  · exact WuPaper.ClassicalFourthNat.BPay_2732
  · exact WuPaper.ClassicalFourthNat.BPay_2733
  · exact WuPaper.ClassicalFourthNat.BPay_2734
  · exact WuPaper.ClassicalFourthNat.BPay_2735
  · exact WuPaper.ClassicalFourthNat.BPay_2736
  · exact WuPaper.ClassicalFourthNat.BPay_2737
  · exact WuPaper.ClassicalFourthNat.BPay_2738
  · exact WuPaper.ClassicalFourthNat.BPay_2739
  · exact WuPaper.ClassicalFourthNat.BPay_2740
  · exact WuPaper.ClassicalFourthNat.BPay_2741
  · exact WuPaper.ClassicalFourthNat.BPay_2742
  · exact WuPaper.ClassicalFourthNat.BPay_2743
  · exact WuPaper.ClassicalFourthNat.BPay_2744
  · exact WuPaper.ClassicalFourthNat.BPay_2745
  · exact WuPaper.ClassicalFourthNat.BPay_2746
  · exact WuPaper.ClassicalFourthNat.BPay_2747
  · exact WuPaper.ClassicalFourthNat.BPay_2748
  · exact WuPaper.ClassicalFourthNat.BPay_2749
  · exact WuPaper.ClassicalFourthNat.BPay_2750
  · exact WuPaper.ClassicalFourthNat.BPay_2751
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_042
