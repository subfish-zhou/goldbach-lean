import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatOuterPoint050
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem OuterPoint_block_050 (j : Fin 64) (hj : 64*50+j.val < 10541) :
    OuterPoint (64*50+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3200
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3201
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3202
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3203
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3204
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3205
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3206
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3207
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3208
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3209
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3210
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3211
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3212
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3213
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3214
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3215
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3216
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3217
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3218
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3219
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3220
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3221
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3222
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3223
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3224
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3225
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3226
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3227
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3228
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3229
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3230
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3231
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3232
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3233
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3234
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3235
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3236
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3237
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3238
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3239
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3240
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3241
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3242
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3243
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3244
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3245
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3246
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3247
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3248
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3249
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3250
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3251
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3252
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3253
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3254
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3255
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3256
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3257
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3258
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3259
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3260
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3261
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3262
  · exact WuPaper.ClassicalFourthNat.OuterPoint_3263
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.OuterPoint_block_050
