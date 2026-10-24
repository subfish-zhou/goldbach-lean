import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatOuterPoint160
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem OuterPoint_block_160 (j : Fin 64) (hj : 64*160+j.val < 10541) :
    OuterPoint (64*160+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10240
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10241
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10242
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10243
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10244
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10245
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10246
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10247
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10248
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10249
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10250
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10251
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10252
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10253
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10254
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10255
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10256
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10257
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10258
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10259
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10260
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10261
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10262
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10263
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10264
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10265
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10266
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10267
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10268
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10269
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10270
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10271
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10272
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10273
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10274
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10275
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10276
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10277
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10278
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10279
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10280
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10281
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10282
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10283
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10284
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10285
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10286
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10287
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10288
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10289
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10290
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10291
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10292
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10293
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10294
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10295
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10296
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10297
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10298
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10299
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10300
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10301
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10302
  · exact WuPaper.ClassicalFourthNat.OuterPoint_10303
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.OuterPoint_block_160
