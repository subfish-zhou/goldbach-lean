import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatCPay036
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem CPay_block_036 (j : Fin 64) (hj : 64*36+j.val < 2540) :
    CPay (64*36+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.CPay_2304
  · exact WuPaper.ClassicalFourthNat.CPay_2305
  · exact WuPaper.ClassicalFourthNat.CPay_2306
  · exact WuPaper.ClassicalFourthNat.CPay_2307
  · exact WuPaper.ClassicalFourthNat.CPay_2308
  · exact WuPaper.ClassicalFourthNat.CPay_2309
  · exact WuPaper.ClassicalFourthNat.CPay_2310
  · exact WuPaper.ClassicalFourthNat.CPay_2311
  · exact WuPaper.ClassicalFourthNat.CPay_2312
  · exact WuPaper.ClassicalFourthNat.CPay_2313
  · exact WuPaper.ClassicalFourthNat.CPay_2314
  · exact WuPaper.ClassicalFourthNat.CPay_2315
  · exact WuPaper.ClassicalFourthNat.CPay_2316
  · exact WuPaper.ClassicalFourthNat.CPay_2317
  · exact WuPaper.ClassicalFourthNat.CPay_2318
  · exact WuPaper.ClassicalFourthNat.CPay_2319
  · exact WuPaper.ClassicalFourthNat.CPay_2320
  · exact WuPaper.ClassicalFourthNat.CPay_2321
  · exact WuPaper.ClassicalFourthNat.CPay_2322
  · exact WuPaper.ClassicalFourthNat.CPay_2323
  · exact WuPaper.ClassicalFourthNat.CPay_2324
  · exact WuPaper.ClassicalFourthNat.CPay_2325
  · exact WuPaper.ClassicalFourthNat.CPay_2326
  · exact WuPaper.ClassicalFourthNat.CPay_2327
  · exact WuPaper.ClassicalFourthNat.CPay_2328
  · exact WuPaper.ClassicalFourthNat.CPay_2329
  · exact WuPaper.ClassicalFourthNat.CPay_2330
  · exact WuPaper.ClassicalFourthNat.CPay_2331
  · exact WuPaper.ClassicalFourthNat.CPay_2332
  · exact WuPaper.ClassicalFourthNat.CPay_2333
  · exact WuPaper.ClassicalFourthNat.CPay_2334
  · exact WuPaper.ClassicalFourthNat.CPay_2335
  · exact WuPaper.ClassicalFourthNat.CPay_2336
  · exact WuPaper.ClassicalFourthNat.CPay_2337
  · exact WuPaper.ClassicalFourthNat.CPay_2338
  · exact WuPaper.ClassicalFourthNat.CPay_2339
  · exact WuPaper.ClassicalFourthNat.CPay_2340
  · exact WuPaper.ClassicalFourthNat.CPay_2341
  · exact WuPaper.ClassicalFourthNat.CPay_2342
  · exact WuPaper.ClassicalFourthNat.CPay_2343
  · exact WuPaper.ClassicalFourthNat.CPay_2344
  · exact WuPaper.ClassicalFourthNat.CPay_2345
  · exact WuPaper.ClassicalFourthNat.CPay_2346
  · exact WuPaper.ClassicalFourthNat.CPay_2347
  · exact WuPaper.ClassicalFourthNat.CPay_2348
  · exact WuPaper.ClassicalFourthNat.CPay_2349
  · exact WuPaper.ClassicalFourthNat.CPay_2350
  · exact WuPaper.ClassicalFourthNat.CPay_2351
  · exact WuPaper.ClassicalFourthNat.CPay_2352
  · exact WuPaper.ClassicalFourthNat.CPay_2353
  · exact WuPaper.ClassicalFourthNat.CPay_2354
  · exact WuPaper.ClassicalFourthNat.CPay_2355
  · exact WuPaper.ClassicalFourthNat.CPay_2356
  · exact WuPaper.ClassicalFourthNat.CPay_2357
  · exact WuPaper.ClassicalFourthNat.CPay_2358
  · exact WuPaper.ClassicalFourthNat.CPay_2359
  · exact WuPaper.ClassicalFourthNat.CPay_2360
  · exact WuPaper.ClassicalFourthNat.CPay_2361
  · exact WuPaper.ClassicalFourthNat.CPay_2362
  · exact WuPaper.ClassicalFourthNat.CPay_2363
  · exact WuPaper.ClassicalFourthNat.CPay_2364
  · exact WuPaper.ClassicalFourthNat.CPay_2365
  · exact WuPaper.ClassicalFourthNat.CPay_2366
  · exact WuPaper.ClassicalFourthNat.CPay_2367
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.CPay_block_036
