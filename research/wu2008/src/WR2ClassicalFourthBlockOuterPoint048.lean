import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatOuterPoint048
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem OuterPoint_block_048 (j : Fin 64) (hj : 64*48+j.val < 10541) :
    OuterPoint (64*48+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3072
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3073
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3074
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3075
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3076
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3077
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3078
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3079
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3080
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3081
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3082
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3083
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3084
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3085
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3086
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3087
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3088
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3089
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3090
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3091
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3092
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3093
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3094
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3095
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3096
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3097
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3098
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3099
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3100
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3101
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3102
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3103
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3104
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3105
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3106
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3107
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3108
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3109
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3110
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3111
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3112
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3113
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3114
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3115
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3116
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3117
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3118
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3119
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3120
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3121
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3122
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3123
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3124
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3125
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3126
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3127
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3128
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3129
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3130
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3131
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3132
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3133
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3134
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3135
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.OuterPoint_block_048
