import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatOuterPoint045
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem OuterPoint_block_045 (j : Fin 64) (hj : 64*45+j.val < 10541) :
    OuterPoint (64*45+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2880
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2881
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2882
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2883
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2884
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2885
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2886
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2887
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2888
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2889
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2890
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2891
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2892
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2893
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2894
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2895
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2896
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2897
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2898
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2899
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2900
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2901
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2902
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2903
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2904
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2905
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2906
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2907
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2908
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2909
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2910
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2911
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2912
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2913
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2914
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2915
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2916
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2917
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2918
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2919
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2920
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2921
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2922
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2923
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2924
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2925
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2926
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2927
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2928
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2929
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2930
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2931
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2932
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2933
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2934
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2935
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2936
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2937
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2938
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2939
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2940
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2941
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2942
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2943
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.OuterPoint_block_045
