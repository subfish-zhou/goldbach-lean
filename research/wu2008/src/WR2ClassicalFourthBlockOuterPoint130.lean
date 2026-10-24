import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatOuterPoint130
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem OuterPoint_block_130 (j : Fin 64) (hj : 64*130+j.val < 10541) :
    OuterPoint (64*130+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8320
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8321
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8322
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8323
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8324
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8325
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8326
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8327
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8328
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8329
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8330
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8331
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8332
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8333
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8334
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8335
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8336
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8337
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8338
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8339
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8340
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8341
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8342
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8343
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8344
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8345
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8346
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8347
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8348
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8349
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8350
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8351
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8352
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8353
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8354
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8355
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8356
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8357
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8358
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8359
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8360
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8361
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8362
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8363
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8364
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8365
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8366
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8367
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8368
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8369
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8370
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8371
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8372
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8373
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8374
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8375
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8376
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8377
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8378
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8379
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8380
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8381
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8382
  · exact WuPaper.ClassicalFourthNat.OuterPoint_8383
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.OuterPoint_block_130
