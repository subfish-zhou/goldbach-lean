import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatOuterPoint144
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem OuterPoint_block_144 (j : Fin 64) (hj : 64*144+j.val < 10541) :
    OuterPoint (64*144+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9216
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9217
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9218
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9219
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9220
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9221
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9222
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9223
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9224
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9225
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9226
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9227
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9228
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9229
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9230
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9231
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9232
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9233
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9234
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9235
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9236
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9237
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9238
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9239
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9240
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9241
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9242
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9243
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9244
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9245
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9246
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9247
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9248
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9249
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9250
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9251
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9252
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9253
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9254
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9255
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9256
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9257
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9258
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9259
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9260
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9261
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9262
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9263
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9264
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9265
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9266
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9267
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9268
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9269
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9270
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9271
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9272
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9273
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9274
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9275
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9276
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9277
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9278
  · exact WuPaper.ClassicalFourthNat.OuterPoint_9279
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.OuterPoint_block_144
