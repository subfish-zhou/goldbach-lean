import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatouterPay048
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem outerPay_block_048 (j : Fin 64) (hj : 64*48+j.val < 10540) :
    OuterPay (64*48+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.outerPay_3072
  · exact WuPaper.ClassicalFourthNat.outerPay_3073
  · exact WuPaper.ClassicalFourthNat.outerPay_3074
  · exact WuPaper.ClassicalFourthNat.outerPay_3075
  · exact WuPaper.ClassicalFourthNat.outerPay_3076
  · exact WuPaper.ClassicalFourthNat.outerPay_3077
  · exact WuPaper.ClassicalFourthNat.outerPay_3078
  · exact WuPaper.ClassicalFourthNat.outerPay_3079
  · exact WuPaper.ClassicalFourthNat.outerPay_3080
  · exact WuPaper.ClassicalFourthNat.outerPay_3081
  · exact WuPaper.ClassicalFourthNat.outerPay_3082
  · exact WuPaper.ClassicalFourthNat.outerPay_3083
  · exact WuPaper.ClassicalFourthNat.outerPay_3084
  · exact WuPaper.ClassicalFourthNat.outerPay_3085
  · exact WuPaper.ClassicalFourthNat.outerPay_3086
  · exact WuPaper.ClassicalFourthNat.outerPay_3087
  · exact WuPaper.ClassicalFourthNat.outerPay_3088
  · exact WuPaper.ClassicalFourthNat.outerPay_3089
  · exact WuPaper.ClassicalFourthNat.outerPay_3090
  · exact WuPaper.ClassicalFourthNat.outerPay_3091
  · exact WuPaper.ClassicalFourthNat.outerPay_3092
  · exact WuPaper.ClassicalFourthNat.outerPay_3093
  · exact WuPaper.ClassicalFourthNat.outerPay_3094
  · exact WuPaper.ClassicalFourthNat.outerPay_3095
  · exact WuPaper.ClassicalFourthNat.outerPay_3096
  · exact WuPaper.ClassicalFourthNat.outerPay_3097
  · exact WuPaper.ClassicalFourthNat.outerPay_3098
  · exact WuPaper.ClassicalFourthNat.outerPay_3099
  · exact WuPaper.ClassicalFourthNat.outerPay_3100
  · exact WuPaper.ClassicalFourthNat.outerPay_3101
  · exact WuPaper.ClassicalFourthNat.outerPay_3102
  · exact WuPaper.ClassicalFourthNat.outerPay_3103
  · exact WuPaper.ClassicalFourthNat.outerPay_3104
  · exact WuPaper.ClassicalFourthNat.outerPay_3105
  · exact WuPaper.ClassicalFourthNat.outerPay_3106
  · exact WuPaper.ClassicalFourthNat.outerPay_3107
  · exact WuPaper.ClassicalFourthNat.outerPay_3108
  · exact WuPaper.ClassicalFourthNat.outerPay_3109
  · exact WuPaper.ClassicalFourthNat.outerPay_3110
  · exact WuPaper.ClassicalFourthNat.outerPay_3111
  · exact WuPaper.ClassicalFourthNat.outerPay_3112
  · exact WuPaper.ClassicalFourthNat.outerPay_3113
  · exact WuPaper.ClassicalFourthNat.outerPay_3114
  · exact WuPaper.ClassicalFourthNat.outerPay_3115
  · exact WuPaper.ClassicalFourthNat.outerPay_3116
  · exact WuPaper.ClassicalFourthNat.outerPay_3117
  · exact WuPaper.ClassicalFourthNat.outerPay_3118
  · exact WuPaper.ClassicalFourthNat.outerPay_3119
  · exact WuPaper.ClassicalFourthNat.outerPay_3120
  · exact WuPaper.ClassicalFourthNat.outerPay_3121
  · exact WuPaper.ClassicalFourthNat.outerPay_3122
  · exact WuPaper.ClassicalFourthNat.outerPay_3123
  · exact WuPaper.ClassicalFourthNat.outerPay_3124
  · exact WuPaper.ClassicalFourthNat.outerPay_3125
  · exact WuPaper.ClassicalFourthNat.outerPay_3126
  · exact WuPaper.ClassicalFourthNat.outerPay_3127
  · exact WuPaper.ClassicalFourthNat.outerPay_3128
  · exact WuPaper.ClassicalFourthNat.outerPay_3129
  · exact WuPaper.ClassicalFourthNat.outerPay_3130
  · exact WuPaper.ClassicalFourthNat.outerPay_3131
  · exact WuPaper.ClassicalFourthNat.outerPay_3132
  · exact WuPaper.ClassicalFourthNat.outerPay_3133
  · exact WuPaper.ClassicalFourthNat.outerPay_3134
  · exact WuPaper.ClassicalFourthNat.outerPay_3135
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.outerPay_block_048
