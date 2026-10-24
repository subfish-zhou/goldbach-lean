import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay046
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_046 (j : Fin 64) (hj : 64*46+j.val < 10540) :
    BPay (64*46+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_2944
  · exact WuPaper.ClassicalFourthNat.BPay_2945
  · exact WuPaper.ClassicalFourthNat.BPay_2946
  · exact WuPaper.ClassicalFourthNat.BPay_2947
  · exact WuPaper.ClassicalFourthNat.BPay_2948
  · exact WuPaper.ClassicalFourthNat.BPay_2949
  · exact WuPaper.ClassicalFourthNat.BPay_2950
  · exact WuPaper.ClassicalFourthNat.BPay_2951
  · exact WuPaper.ClassicalFourthNat.BPay_2952
  · exact WuPaper.ClassicalFourthNat.BPay_2953
  · exact WuPaper.ClassicalFourthNat.BPay_2954
  · exact WuPaper.ClassicalFourthNat.BPay_2955
  · exact WuPaper.ClassicalFourthNat.BPay_2956
  · exact WuPaper.ClassicalFourthNat.BPay_2957
  · exact WuPaper.ClassicalFourthNat.BPay_2958
  · exact WuPaper.ClassicalFourthNat.BPay_2959
  · exact WuPaper.ClassicalFourthNat.BPay_2960
  · exact WuPaper.ClassicalFourthNat.BPay_2961
  · exact WuPaper.ClassicalFourthNat.BPay_2962
  · exact WuPaper.ClassicalFourthNat.BPay_2963
  · exact WuPaper.ClassicalFourthNat.BPay_2964
  · exact WuPaper.ClassicalFourthNat.BPay_2965
  · exact WuPaper.ClassicalFourthNat.BPay_2966
  · exact WuPaper.ClassicalFourthNat.BPay_2967
  · exact WuPaper.ClassicalFourthNat.BPay_2968
  · exact WuPaper.ClassicalFourthNat.BPay_2969
  · exact WuPaper.ClassicalFourthNat.BPay_2970
  · exact WuPaper.ClassicalFourthNat.BPay_2971
  · exact WuPaper.ClassicalFourthNat.BPay_2972
  · exact WuPaper.ClassicalFourthNat.BPay_2973
  · exact WuPaper.ClassicalFourthNat.BPay_2974
  · exact WuPaper.ClassicalFourthNat.BPay_2975
  · exact WuPaper.ClassicalFourthNat.BPay_2976
  · exact WuPaper.ClassicalFourthNat.BPay_2977
  · exact WuPaper.ClassicalFourthNat.BPay_2978
  · exact WuPaper.ClassicalFourthNat.BPay_2979
  · exact WuPaper.ClassicalFourthNat.BPay_2980
  · exact WuPaper.ClassicalFourthNat.BPay_2981
  · exact WuPaper.ClassicalFourthNat.BPay_2982
  · exact WuPaper.ClassicalFourthNat.BPay_2983
  · exact WuPaper.ClassicalFourthNat.BPay_2984
  · exact WuPaper.ClassicalFourthNat.BPay_2985
  · exact WuPaper.ClassicalFourthNat.BPay_2986
  · exact WuPaper.ClassicalFourthNat.BPay_2987
  · exact WuPaper.ClassicalFourthNat.BPay_2988
  · exact WuPaper.ClassicalFourthNat.BPay_2989
  · exact WuPaper.ClassicalFourthNat.BPay_2990
  · exact WuPaper.ClassicalFourthNat.BPay_2991
  · exact WuPaper.ClassicalFourthNat.BPay_2992
  · exact WuPaper.ClassicalFourthNat.BPay_2993
  · exact WuPaper.ClassicalFourthNat.BPay_2994
  · exact WuPaper.ClassicalFourthNat.BPay_2995
  · exact WuPaper.ClassicalFourthNat.BPay_2996
  · exact WuPaper.ClassicalFourthNat.BPay_2997
  · exact WuPaper.ClassicalFourthNat.BPay_2998
  · exact WuPaper.ClassicalFourthNat.BPay_2999
  · exact WuPaper.ClassicalFourthNat.BPay_3000
  · exact WuPaper.ClassicalFourthNat.BPay_3001
  · exact WuPaper.ClassicalFourthNat.BPay_3002
  · exact WuPaper.ClassicalFourthNat.BPay_3003
  · exact WuPaper.ClassicalFourthNat.BPay_3004
  · exact WuPaper.ClassicalFourthNat.BPay_3005
  · exact WuPaper.ClassicalFourthNat.BPay_3006
  · exact WuPaper.ClassicalFourthNat.BPay_3007
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_046
