import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay044
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_044 (j : Fin 64) (hj : 64*44+j.val < 10540) :
    BPay (64*44+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_2816
  · exact WuPaper.ClassicalFourthNat.BPay_2817
  · exact WuPaper.ClassicalFourthNat.BPay_2818
  · exact WuPaper.ClassicalFourthNat.BPay_2819
  · exact WuPaper.ClassicalFourthNat.BPay_2820
  · exact WuPaper.ClassicalFourthNat.BPay_2821
  · exact WuPaper.ClassicalFourthNat.BPay_2822
  · exact WuPaper.ClassicalFourthNat.BPay_2823
  · exact WuPaper.ClassicalFourthNat.BPay_2824
  · exact WuPaper.ClassicalFourthNat.BPay_2825
  · exact WuPaper.ClassicalFourthNat.BPay_2826
  · exact WuPaper.ClassicalFourthNat.BPay_2827
  · exact WuPaper.ClassicalFourthNat.BPay_2828
  · exact WuPaper.ClassicalFourthNat.BPay_2829
  · exact WuPaper.ClassicalFourthNat.BPay_2830
  · exact WuPaper.ClassicalFourthNat.BPay_2831
  · exact WuPaper.ClassicalFourthNat.BPay_2832
  · exact WuPaper.ClassicalFourthNat.BPay_2833
  · exact WuPaper.ClassicalFourthNat.BPay_2834
  · exact WuPaper.ClassicalFourthNat.BPay_2835
  · exact WuPaper.ClassicalFourthNat.BPay_2836
  · exact WuPaper.ClassicalFourthNat.BPay_2837
  · exact WuPaper.ClassicalFourthNat.BPay_2838
  · exact WuPaper.ClassicalFourthNat.BPay_2839
  · exact WuPaper.ClassicalFourthNat.BPay_2840
  · exact WuPaper.ClassicalFourthNat.BPay_2841
  · exact WuPaper.ClassicalFourthNat.BPay_2842
  · exact WuPaper.ClassicalFourthNat.BPay_2843
  · exact WuPaper.ClassicalFourthNat.BPay_2844
  · exact WuPaper.ClassicalFourthNat.BPay_2845
  · exact WuPaper.ClassicalFourthNat.BPay_2846
  · exact WuPaper.ClassicalFourthNat.BPay_2847
  · exact WuPaper.ClassicalFourthNat.BPay_2848
  · exact WuPaper.ClassicalFourthNat.BPay_2849
  · exact WuPaper.ClassicalFourthNat.BPay_2850
  · exact WuPaper.ClassicalFourthNat.BPay_2851
  · exact WuPaper.ClassicalFourthNat.BPay_2852
  · exact WuPaper.ClassicalFourthNat.BPay_2853
  · exact WuPaper.ClassicalFourthNat.BPay_2854
  · exact WuPaper.ClassicalFourthNat.BPay_2855
  · exact WuPaper.ClassicalFourthNat.BPay_2856
  · exact WuPaper.ClassicalFourthNat.BPay_2857
  · exact WuPaper.ClassicalFourthNat.BPay_2858
  · exact WuPaper.ClassicalFourthNat.BPay_2859
  · exact WuPaper.ClassicalFourthNat.BPay_2860
  · exact WuPaper.ClassicalFourthNat.BPay_2861
  · exact WuPaper.ClassicalFourthNat.BPay_2862
  · exact WuPaper.ClassicalFourthNat.BPay_2863
  · exact WuPaper.ClassicalFourthNat.BPay_2864
  · exact WuPaper.ClassicalFourthNat.BPay_2865
  · exact WuPaper.ClassicalFourthNat.BPay_2866
  · exact WuPaper.ClassicalFourthNat.BPay_2867
  · exact WuPaper.ClassicalFourthNat.BPay_2868
  · exact WuPaper.ClassicalFourthNat.BPay_2869
  · exact WuPaper.ClassicalFourthNat.BPay_2870
  · exact WuPaper.ClassicalFourthNat.BPay_2871
  · exact WuPaper.ClassicalFourthNat.BPay_2872
  · exact WuPaper.ClassicalFourthNat.BPay_2873
  · exact WuPaper.ClassicalFourthNat.BPay_2874
  · exact WuPaper.ClassicalFourthNat.BPay_2875
  · exact WuPaper.ClassicalFourthNat.BPay_2876
  · exact WuPaper.ClassicalFourthNat.BPay_2877
  · exact WuPaper.ClassicalFourthNat.BPay_2878
  · exact WuPaper.ClassicalFourthNat.BPay_2879
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_044
