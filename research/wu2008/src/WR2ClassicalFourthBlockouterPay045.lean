import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatouterPay045
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem outerPay_block_045 (j : Fin 64) (hj : 64*45+j.val < 10540) :
    OuterPay (64*45+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.outerPay_2880
  · exact WuPaper.ClassicalFourthNat.outerPay_2881
  · exact WuPaper.ClassicalFourthNat.outerPay_2882
  · exact WuPaper.ClassicalFourthNat.outerPay_2883
  · exact WuPaper.ClassicalFourthNat.outerPay_2884
  · exact WuPaper.ClassicalFourthNat.outerPay_2885
  · exact WuPaper.ClassicalFourthNat.outerPay_2886
  · exact WuPaper.ClassicalFourthNat.outerPay_2887
  · exact WuPaper.ClassicalFourthNat.outerPay_2888
  · exact WuPaper.ClassicalFourthNat.outerPay_2889
  · exact WuPaper.ClassicalFourthNat.outerPay_2890
  · exact WuPaper.ClassicalFourthNat.outerPay_2891
  · exact WuPaper.ClassicalFourthNat.outerPay_2892
  · exact WuPaper.ClassicalFourthNat.outerPay_2893
  · exact WuPaper.ClassicalFourthNat.outerPay_2894
  · exact WuPaper.ClassicalFourthNat.outerPay_2895
  · exact WuPaper.ClassicalFourthNat.outerPay_2896
  · exact WuPaper.ClassicalFourthNat.outerPay_2897
  · exact WuPaper.ClassicalFourthNat.outerPay_2898
  · exact WuPaper.ClassicalFourthNat.outerPay_2899
  · exact WuPaper.ClassicalFourthNat.outerPay_2900
  · exact WuPaper.ClassicalFourthNat.outerPay_2901
  · exact WuPaper.ClassicalFourthNat.outerPay_2902
  · exact WuPaper.ClassicalFourthNat.outerPay_2903
  · exact WuPaper.ClassicalFourthNat.outerPay_2904
  · exact WuPaper.ClassicalFourthNat.outerPay_2905
  · exact WuPaper.ClassicalFourthNat.outerPay_2906
  · exact WuPaper.ClassicalFourthNat.outerPay_2907
  · exact WuPaper.ClassicalFourthNat.outerPay_2908
  · exact WuPaper.ClassicalFourthNat.outerPay_2909
  · exact WuPaper.ClassicalFourthNat.outerPay_2910
  · exact WuPaper.ClassicalFourthNat.outerPay_2911
  · exact WuPaper.ClassicalFourthNat.outerPay_2912
  · exact WuPaper.ClassicalFourthNat.outerPay_2913
  · exact WuPaper.ClassicalFourthNat.outerPay_2914
  · exact WuPaper.ClassicalFourthNat.outerPay_2915
  · exact WuPaper.ClassicalFourthNat.outerPay_2916
  · exact WuPaper.ClassicalFourthNat.outerPay_2917
  · exact WuPaper.ClassicalFourthNat.outerPay_2918
  · exact WuPaper.ClassicalFourthNat.outerPay_2919
  · exact WuPaper.ClassicalFourthNat.outerPay_2920
  · exact WuPaper.ClassicalFourthNat.outerPay_2921
  · exact WuPaper.ClassicalFourthNat.outerPay_2922
  · exact WuPaper.ClassicalFourthNat.outerPay_2923
  · exact WuPaper.ClassicalFourthNat.outerPay_2924
  · exact WuPaper.ClassicalFourthNat.outerPay_2925
  · exact WuPaper.ClassicalFourthNat.outerPay_2926
  · exact WuPaper.ClassicalFourthNat.outerPay_2927
  · exact WuPaper.ClassicalFourthNat.outerPay_2928
  · exact WuPaper.ClassicalFourthNat.outerPay_2929
  · exact WuPaper.ClassicalFourthNat.outerPay_2930
  · exact WuPaper.ClassicalFourthNat.outerPay_2931
  · exact WuPaper.ClassicalFourthNat.outerPay_2932
  · exact WuPaper.ClassicalFourthNat.outerPay_2933
  · exact WuPaper.ClassicalFourthNat.outerPay_2934
  · exact WuPaper.ClassicalFourthNat.outerPay_2935
  · exact WuPaper.ClassicalFourthNat.outerPay_2936
  · exact WuPaper.ClassicalFourthNat.outerPay_2937
  · exact WuPaper.ClassicalFourthNat.outerPay_2938
  · exact WuPaper.ClassicalFourthNat.outerPay_2939
  · exact WuPaper.ClassicalFourthNat.outerPay_2940
  · exact WuPaper.ClassicalFourthNat.outerPay_2941
  · exact WuPaper.ClassicalFourthNat.outerPay_2942
  · exact WuPaper.ClassicalFourthNat.outerPay_2943
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.outerPay_block_045
