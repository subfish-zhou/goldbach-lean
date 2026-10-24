import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay043
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_043 (j : Fin 64) (hj : 64*43+j.val < 10540) :
    BPay (64*43+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_2752
  · exact WuPaper.ClassicalFourthNat.BPay_2753
  · exact WuPaper.ClassicalFourthNat.BPay_2754
  · exact WuPaper.ClassicalFourthNat.BPay_2755
  · exact WuPaper.ClassicalFourthNat.BPay_2756
  · exact WuPaper.ClassicalFourthNat.BPay_2757
  · exact WuPaper.ClassicalFourthNat.BPay_2758
  · exact WuPaper.ClassicalFourthNat.BPay_2759
  · exact WuPaper.ClassicalFourthNat.BPay_2760
  · exact WuPaper.ClassicalFourthNat.BPay_2761
  · exact WuPaper.ClassicalFourthNat.BPay_2762
  · exact WuPaper.ClassicalFourthNat.BPay_2763
  · exact WuPaper.ClassicalFourthNat.BPay_2764
  · exact WuPaper.ClassicalFourthNat.BPay_2765
  · exact WuPaper.ClassicalFourthNat.BPay_2766
  · exact WuPaper.ClassicalFourthNat.BPay_2767
  · exact WuPaper.ClassicalFourthNat.BPay_2768
  · exact WuPaper.ClassicalFourthNat.BPay_2769
  · exact WuPaper.ClassicalFourthNat.BPay_2770
  · exact WuPaper.ClassicalFourthNat.BPay_2771
  · exact WuPaper.ClassicalFourthNat.BPay_2772
  · exact WuPaper.ClassicalFourthNat.BPay_2773
  · exact WuPaper.ClassicalFourthNat.BPay_2774
  · exact WuPaper.ClassicalFourthNat.BPay_2775
  · exact WuPaper.ClassicalFourthNat.BPay_2776
  · exact WuPaper.ClassicalFourthNat.BPay_2777
  · exact WuPaper.ClassicalFourthNat.BPay_2778
  · exact WuPaper.ClassicalFourthNat.BPay_2779
  · exact WuPaper.ClassicalFourthNat.BPay_2780
  · exact WuPaper.ClassicalFourthNat.BPay_2781
  · exact WuPaper.ClassicalFourthNat.BPay_2782
  · exact WuPaper.ClassicalFourthNat.BPay_2783
  · exact WuPaper.ClassicalFourthNat.BPay_2784
  · exact WuPaper.ClassicalFourthNat.BPay_2785
  · exact WuPaper.ClassicalFourthNat.BPay_2786
  · exact WuPaper.ClassicalFourthNat.BPay_2787
  · exact WuPaper.ClassicalFourthNat.BPay_2788
  · exact WuPaper.ClassicalFourthNat.BPay_2789
  · exact WuPaper.ClassicalFourthNat.BPay_2790
  · exact WuPaper.ClassicalFourthNat.BPay_2791
  · exact WuPaper.ClassicalFourthNat.BPay_2792
  · exact WuPaper.ClassicalFourthNat.BPay_2793
  · exact WuPaper.ClassicalFourthNat.BPay_2794
  · exact WuPaper.ClassicalFourthNat.BPay_2795
  · exact WuPaper.ClassicalFourthNat.BPay_2796
  · exact WuPaper.ClassicalFourthNat.BPay_2797
  · exact WuPaper.ClassicalFourthNat.BPay_2798
  · exact WuPaper.ClassicalFourthNat.BPay_2799
  · exact WuPaper.ClassicalFourthNat.BPay_2800
  · exact WuPaper.ClassicalFourthNat.BPay_2801
  · exact WuPaper.ClassicalFourthNat.BPay_2802
  · exact WuPaper.ClassicalFourthNat.BPay_2803
  · exact WuPaper.ClassicalFourthNat.BPay_2804
  · exact WuPaper.ClassicalFourthNat.BPay_2805
  · exact WuPaper.ClassicalFourthNat.BPay_2806
  · exact WuPaper.ClassicalFourthNat.BPay_2807
  · exact WuPaper.ClassicalFourthNat.BPay_2808
  · exact WuPaper.ClassicalFourthNat.BPay_2809
  · exact WuPaper.ClassicalFourthNat.BPay_2810
  · exact WuPaper.ClassicalFourthNat.BPay_2811
  · exact WuPaper.ClassicalFourthNat.BPay_2812
  · exact WuPaper.ClassicalFourthNat.BPay_2813
  · exact WuPaper.ClassicalFourthNat.BPay_2814
  · exact WuPaper.ClassicalFourthNat.BPay_2815
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_043
