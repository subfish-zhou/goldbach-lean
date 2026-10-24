import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay048
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_048 (j : Fin 64) (hj : 64*48+j.val < 10540) :
    BPay (64*48+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_3072
  · exact WuPaper.ClassicalFourthNat.BPay_3073
  · exact WuPaper.ClassicalFourthNat.BPay_3074
  · exact WuPaper.ClassicalFourthNat.BPay_3075
  · exact WuPaper.ClassicalFourthNat.BPay_3076
  · exact WuPaper.ClassicalFourthNat.BPay_3077
  · exact WuPaper.ClassicalFourthNat.BPay_3078
  · exact WuPaper.ClassicalFourthNat.BPay_3079
  · exact WuPaper.ClassicalFourthNat.BPay_3080
  · exact WuPaper.ClassicalFourthNat.BPay_3081
  · exact WuPaper.ClassicalFourthNat.BPay_3082
  · exact WuPaper.ClassicalFourthNat.BPay_3083
  · exact WuPaper.ClassicalFourthNat.BPay_3084
  · exact WuPaper.ClassicalFourthNat.BPay_3085
  · exact WuPaper.ClassicalFourthNat.BPay_3086
  · exact WuPaper.ClassicalFourthNat.BPay_3087
  · exact WuPaper.ClassicalFourthNat.BPay_3088
  · exact WuPaper.ClassicalFourthNat.BPay_3089
  · exact WuPaper.ClassicalFourthNat.BPay_3090
  · exact WuPaper.ClassicalFourthNat.BPay_3091
  · exact WuPaper.ClassicalFourthNat.BPay_3092
  · exact WuPaper.ClassicalFourthNat.BPay_3093
  · exact WuPaper.ClassicalFourthNat.BPay_3094
  · exact WuPaper.ClassicalFourthNat.BPay_3095
  · exact WuPaper.ClassicalFourthNat.BPay_3096
  · exact WuPaper.ClassicalFourthNat.BPay_3097
  · exact WuPaper.ClassicalFourthNat.BPay_3098
  · exact WuPaper.ClassicalFourthNat.BPay_3099
  · exact WuPaper.ClassicalFourthNat.BPay_3100
  · exact WuPaper.ClassicalFourthNat.BPay_3101
  · exact WuPaper.ClassicalFourthNat.BPay_3102
  · exact WuPaper.ClassicalFourthNat.BPay_3103
  · exact WuPaper.ClassicalFourthNat.BPay_3104
  · exact WuPaper.ClassicalFourthNat.BPay_3105
  · exact WuPaper.ClassicalFourthNat.BPay_3106
  · exact WuPaper.ClassicalFourthNat.BPay_3107
  · exact WuPaper.ClassicalFourthNat.BPay_3108
  · exact WuPaper.ClassicalFourthNat.BPay_3109
  · exact WuPaper.ClassicalFourthNat.BPay_3110
  · exact WuPaper.ClassicalFourthNat.BPay_3111
  · exact WuPaper.ClassicalFourthNat.BPay_3112
  · exact WuPaper.ClassicalFourthNat.BPay_3113
  · exact WuPaper.ClassicalFourthNat.BPay_3114
  · exact WuPaper.ClassicalFourthNat.BPay_3115
  · exact WuPaper.ClassicalFourthNat.BPay_3116
  · exact WuPaper.ClassicalFourthNat.BPay_3117
  · exact WuPaper.ClassicalFourthNat.BPay_3118
  · exact WuPaper.ClassicalFourthNat.BPay_3119
  · exact WuPaper.ClassicalFourthNat.BPay_3120
  · exact WuPaper.ClassicalFourthNat.BPay_3121
  · exact WuPaper.ClassicalFourthNat.BPay_3122
  · exact WuPaper.ClassicalFourthNat.BPay_3123
  · exact WuPaper.ClassicalFourthNat.BPay_3124
  · exact WuPaper.ClassicalFourthNat.BPay_3125
  · exact WuPaper.ClassicalFourthNat.BPay_3126
  · exact WuPaper.ClassicalFourthNat.BPay_3127
  · exact WuPaper.ClassicalFourthNat.BPay_3128
  · exact WuPaper.ClassicalFourthNat.BPay_3129
  · exact WuPaper.ClassicalFourthNat.BPay_3130
  · exact WuPaper.ClassicalFourthNat.BPay_3131
  · exact WuPaper.ClassicalFourthNat.BPay_3132
  · exact WuPaper.ClassicalFourthNat.BPay_3133
  · exact WuPaper.ClassicalFourthNat.BPay_3134
  · exact WuPaper.ClassicalFourthNat.BPay_3135
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_048
