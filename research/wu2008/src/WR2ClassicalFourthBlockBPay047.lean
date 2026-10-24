import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay047
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_047 (j : Fin 64) (hj : 64*47+j.val < 10540) :
    BPay (64*47+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_3008
  · exact WuPaper.ClassicalFourthNat.BPay_3009
  · exact WuPaper.ClassicalFourthNat.BPay_3010
  · exact WuPaper.ClassicalFourthNat.BPay_3011
  · exact WuPaper.ClassicalFourthNat.BPay_3012
  · exact WuPaper.ClassicalFourthNat.BPay_3013
  · exact WuPaper.ClassicalFourthNat.BPay_3014
  · exact WuPaper.ClassicalFourthNat.BPay_3015
  · exact WuPaper.ClassicalFourthNat.BPay_3016
  · exact WuPaper.ClassicalFourthNat.BPay_3017
  · exact WuPaper.ClassicalFourthNat.BPay_3018
  · exact WuPaper.ClassicalFourthNat.BPay_3019
  · exact WuPaper.ClassicalFourthNat.BPay_3020
  · exact WuPaper.ClassicalFourthNat.BPay_3021
  · exact WuPaper.ClassicalFourthNat.BPay_3022
  · exact WuPaper.ClassicalFourthNat.BPay_3023
  · exact WuPaper.ClassicalFourthNat.BPay_3024
  · exact WuPaper.ClassicalFourthNat.BPay_3025
  · exact WuPaper.ClassicalFourthNat.BPay_3026
  · exact WuPaper.ClassicalFourthNat.BPay_3027
  · exact WuPaper.ClassicalFourthNat.BPay_3028
  · exact WuPaper.ClassicalFourthNat.BPay_3029
  · exact WuPaper.ClassicalFourthNat.BPay_3030
  · exact WuPaper.ClassicalFourthNat.BPay_3031
  · exact WuPaper.ClassicalFourthNat.BPay_3032
  · exact WuPaper.ClassicalFourthNat.BPay_3033
  · exact WuPaper.ClassicalFourthNat.BPay_3034
  · exact WuPaper.ClassicalFourthNat.BPay_3035
  · exact WuPaper.ClassicalFourthNat.BPay_3036
  · exact WuPaper.ClassicalFourthNat.BPay_3037
  · exact WuPaper.ClassicalFourthNat.BPay_3038
  · exact WuPaper.ClassicalFourthNat.BPay_3039
  · exact WuPaper.ClassicalFourthNat.BPay_3040
  · exact WuPaper.ClassicalFourthNat.BPay_3041
  · exact WuPaper.ClassicalFourthNat.BPay_3042
  · exact WuPaper.ClassicalFourthNat.BPay_3043
  · exact WuPaper.ClassicalFourthNat.BPay_3044
  · exact WuPaper.ClassicalFourthNat.BPay_3045
  · exact WuPaper.ClassicalFourthNat.BPay_3046
  · exact WuPaper.ClassicalFourthNat.BPay_3047
  · exact WuPaper.ClassicalFourthNat.BPay_3048
  · exact WuPaper.ClassicalFourthNat.BPay_3049
  · exact WuPaper.ClassicalFourthNat.BPay_3050
  · exact WuPaper.ClassicalFourthNat.BPay_3051
  · exact WuPaper.ClassicalFourthNat.BPay_3052
  · exact WuPaper.ClassicalFourthNat.BPay_3053
  · exact WuPaper.ClassicalFourthNat.BPay_3054
  · exact WuPaper.ClassicalFourthNat.BPay_3055
  · exact WuPaper.ClassicalFourthNat.BPay_3056
  · exact WuPaper.ClassicalFourthNat.BPay_3057
  · exact WuPaper.ClassicalFourthNat.BPay_3058
  · exact WuPaper.ClassicalFourthNat.BPay_3059
  · exact WuPaper.ClassicalFourthNat.BPay_3060
  · exact WuPaper.ClassicalFourthNat.BPay_3061
  · exact WuPaper.ClassicalFourthNat.BPay_3062
  · exact WuPaper.ClassicalFourthNat.BPay_3063
  · exact WuPaper.ClassicalFourthNat.BPay_3064
  · exact WuPaper.ClassicalFourthNat.BPay_3065
  · exact WuPaper.ClassicalFourthNat.BPay_3066
  · exact WuPaper.ClassicalFourthNat.BPay_3067
  · exact WuPaper.ClassicalFourthNat.BPay_3068
  · exact WuPaper.ClassicalFourthNat.BPay_3069
  · exact WuPaper.ClassicalFourthNat.BPay_3070
  · exact WuPaper.ClassicalFourthNat.BPay_3071
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_047
