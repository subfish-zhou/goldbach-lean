import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay098
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_098 (j : Fin 64) (hj : 64*98+j.val < 10540) :
    BPay (64*98+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_6272
  · exact WuPaper.ClassicalFourthNat.BPay_6273
  · exact WuPaper.ClassicalFourthNat.BPay_6274
  · exact WuPaper.ClassicalFourthNat.BPay_6275
  · exact WuPaper.ClassicalFourthNat.BPay_6276
  · exact WuPaper.ClassicalFourthNat.BPay_6277
  · exact WuPaper.ClassicalFourthNat.BPay_6278
  · exact WuPaper.ClassicalFourthNat.BPay_6279
  · exact WuPaper.ClassicalFourthNat.BPay_6280
  · exact WuPaper.ClassicalFourthNat.BPay_6281
  · exact WuPaper.ClassicalFourthNat.BPay_6282
  · exact WuPaper.ClassicalFourthNat.BPay_6283
  · exact WuPaper.ClassicalFourthNat.BPay_6284
  · exact WuPaper.ClassicalFourthNat.BPay_6285
  · exact WuPaper.ClassicalFourthNat.BPay_6286
  · exact WuPaper.ClassicalFourthNat.BPay_6287
  · exact WuPaper.ClassicalFourthNat.BPay_6288
  · exact WuPaper.ClassicalFourthNat.BPay_6289
  · exact WuPaper.ClassicalFourthNat.BPay_6290
  · exact WuPaper.ClassicalFourthNat.BPay_6291
  · exact WuPaper.ClassicalFourthNat.BPay_6292
  · exact WuPaper.ClassicalFourthNat.BPay_6293
  · exact WuPaper.ClassicalFourthNat.BPay_6294
  · exact WuPaper.ClassicalFourthNat.BPay_6295
  · exact WuPaper.ClassicalFourthNat.BPay_6296
  · exact WuPaper.ClassicalFourthNat.BPay_6297
  · exact WuPaper.ClassicalFourthNat.BPay_6298
  · exact WuPaper.ClassicalFourthNat.BPay_6299
  · exact WuPaper.ClassicalFourthNat.BPay_6300
  · exact WuPaper.ClassicalFourthNat.BPay_6301
  · exact WuPaper.ClassicalFourthNat.BPay_6302
  · exact WuPaper.ClassicalFourthNat.BPay_6303
  · exact WuPaper.ClassicalFourthNat.BPay_6304
  · exact WuPaper.ClassicalFourthNat.BPay_6305
  · exact WuPaper.ClassicalFourthNat.BPay_6306
  · exact WuPaper.ClassicalFourthNat.BPay_6307
  · exact WuPaper.ClassicalFourthNat.BPay_6308
  · exact WuPaper.ClassicalFourthNat.BPay_6309
  · exact WuPaper.ClassicalFourthNat.BPay_6310
  · exact WuPaper.ClassicalFourthNat.BPay_6311
  · exact WuPaper.ClassicalFourthNat.BPay_6312
  · exact WuPaper.ClassicalFourthNat.BPay_6313
  · exact WuPaper.ClassicalFourthNat.BPay_6314
  · exact WuPaper.ClassicalFourthNat.BPay_6315
  · exact WuPaper.ClassicalFourthNat.BPay_6316
  · exact WuPaper.ClassicalFourthNat.BPay_6317
  · exact WuPaper.ClassicalFourthNat.BPay_6318
  · exact WuPaper.ClassicalFourthNat.BPay_6319
  · exact WuPaper.ClassicalFourthNat.BPay_6320
  · exact WuPaper.ClassicalFourthNat.BPay_6321
  · exact WuPaper.ClassicalFourthNat.BPay_6322
  · exact WuPaper.ClassicalFourthNat.BPay_6323
  · exact WuPaper.ClassicalFourthNat.BPay_6324
  · exact WuPaper.ClassicalFourthNat.BPay_6325
  · exact WuPaper.ClassicalFourthNat.BPay_6326
  · exact WuPaper.ClassicalFourthNat.BPay_6327
  · exact WuPaper.ClassicalFourthNat.BPay_6328
  · exact WuPaper.ClassicalFourthNat.BPay_6329
  · exact WuPaper.ClassicalFourthNat.BPay_6330
  · exact WuPaper.ClassicalFourthNat.BPay_6331
  · exact WuPaper.ClassicalFourthNat.BPay_6332
  · exact WuPaper.ClassicalFourthNat.BPay_6333
  · exact WuPaper.ClassicalFourthNat.BPay_6334
  · exact WuPaper.ClassicalFourthNat.BPay_6335
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_098
