import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay045
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_045 (j : Fin 64) (hj : 64*45+j.val < 10540) :
    BPay (64*45+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_2880
  · exact WuPaper.ClassicalFourthNat.BPay_2881
  · exact WuPaper.ClassicalFourthNat.BPay_2882
  · exact WuPaper.ClassicalFourthNat.BPay_2883
  · exact WuPaper.ClassicalFourthNat.BPay_2884
  · exact WuPaper.ClassicalFourthNat.BPay_2885
  · exact WuPaper.ClassicalFourthNat.BPay_2886
  · exact WuPaper.ClassicalFourthNat.BPay_2887
  · exact WuPaper.ClassicalFourthNat.BPay_2888
  · exact WuPaper.ClassicalFourthNat.BPay_2889
  · exact WuPaper.ClassicalFourthNat.BPay_2890
  · exact WuPaper.ClassicalFourthNat.BPay_2891
  · exact WuPaper.ClassicalFourthNat.BPay_2892
  · exact WuPaper.ClassicalFourthNat.BPay_2893
  · exact WuPaper.ClassicalFourthNat.BPay_2894
  · exact WuPaper.ClassicalFourthNat.BPay_2895
  · exact WuPaper.ClassicalFourthNat.BPay_2896
  · exact WuPaper.ClassicalFourthNat.BPay_2897
  · exact WuPaper.ClassicalFourthNat.BPay_2898
  · exact WuPaper.ClassicalFourthNat.BPay_2899
  · exact WuPaper.ClassicalFourthNat.BPay_2900
  · exact WuPaper.ClassicalFourthNat.BPay_2901
  · exact WuPaper.ClassicalFourthNat.BPay_2902
  · exact WuPaper.ClassicalFourthNat.BPay_2903
  · exact WuPaper.ClassicalFourthNat.BPay_2904
  · exact WuPaper.ClassicalFourthNat.BPay_2905
  · exact WuPaper.ClassicalFourthNat.BPay_2906
  · exact WuPaper.ClassicalFourthNat.BPay_2907
  · exact WuPaper.ClassicalFourthNat.BPay_2908
  · exact WuPaper.ClassicalFourthNat.BPay_2909
  · exact WuPaper.ClassicalFourthNat.BPay_2910
  · exact WuPaper.ClassicalFourthNat.BPay_2911
  · exact WuPaper.ClassicalFourthNat.BPay_2912
  · exact WuPaper.ClassicalFourthNat.BPay_2913
  · exact WuPaper.ClassicalFourthNat.BPay_2914
  · exact WuPaper.ClassicalFourthNat.BPay_2915
  · exact WuPaper.ClassicalFourthNat.BPay_2916
  · exact WuPaper.ClassicalFourthNat.BPay_2917
  · exact WuPaper.ClassicalFourthNat.BPay_2918
  · exact WuPaper.ClassicalFourthNat.BPay_2919
  · exact WuPaper.ClassicalFourthNat.BPay_2920
  · exact WuPaper.ClassicalFourthNat.BPay_2921
  · exact WuPaper.ClassicalFourthNat.BPay_2922
  · exact WuPaper.ClassicalFourthNat.BPay_2923
  · exact WuPaper.ClassicalFourthNat.BPay_2924
  · exact WuPaper.ClassicalFourthNat.BPay_2925
  · exact WuPaper.ClassicalFourthNat.BPay_2926
  · exact WuPaper.ClassicalFourthNat.BPay_2927
  · exact WuPaper.ClassicalFourthNat.BPay_2928
  · exact WuPaper.ClassicalFourthNat.BPay_2929
  · exact WuPaper.ClassicalFourthNat.BPay_2930
  · exact WuPaper.ClassicalFourthNat.BPay_2931
  · exact WuPaper.ClassicalFourthNat.BPay_2932
  · exact WuPaper.ClassicalFourthNat.BPay_2933
  · exact WuPaper.ClassicalFourthNat.BPay_2934
  · exact WuPaper.ClassicalFourthNat.BPay_2935
  · exact WuPaper.ClassicalFourthNat.BPay_2936
  · exact WuPaper.ClassicalFourthNat.BPay_2937
  · exact WuPaper.ClassicalFourthNat.BPay_2938
  · exact WuPaper.ClassicalFourthNat.BPay_2939
  · exact WuPaper.ClassicalFourthNat.BPay_2940
  · exact WuPaper.ClassicalFourthNat.BPay_2941
  · exact WuPaper.ClassicalFourthNat.BPay_2942
  · exact WuPaper.ClassicalFourthNat.BPay_2943
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_045
