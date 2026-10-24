import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay037
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_037 (j : Fin 64) (hj : 64*37+j.val < 10540) :
    BPay (64*37+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_2368
  · exact WuPaper.ClassicalFourthNat.BPay_2369
  · exact WuPaper.ClassicalFourthNat.BPay_2370
  · exact WuPaper.ClassicalFourthNat.BPay_2371
  · exact WuPaper.ClassicalFourthNat.BPay_2372
  · exact WuPaper.ClassicalFourthNat.BPay_2373
  · exact WuPaper.ClassicalFourthNat.BPay_2374
  · exact WuPaper.ClassicalFourthNat.BPay_2375
  · exact WuPaper.ClassicalFourthNat.BPay_2376
  · exact WuPaper.ClassicalFourthNat.BPay_2377
  · exact WuPaper.ClassicalFourthNat.BPay_2378
  · exact WuPaper.ClassicalFourthNat.BPay_2379
  · exact WuPaper.ClassicalFourthNat.BPay_2380
  · exact WuPaper.ClassicalFourthNat.BPay_2381
  · exact WuPaper.ClassicalFourthNat.BPay_2382
  · exact WuPaper.ClassicalFourthNat.BPay_2383
  · exact WuPaper.ClassicalFourthNat.BPay_2384
  · exact WuPaper.ClassicalFourthNat.BPay_2385
  · exact WuPaper.ClassicalFourthNat.BPay_2386
  · exact WuPaper.ClassicalFourthNat.BPay_2387
  · exact WuPaper.ClassicalFourthNat.BPay_2388
  · exact WuPaper.ClassicalFourthNat.BPay_2389
  · exact WuPaper.ClassicalFourthNat.BPay_2390
  · exact WuPaper.ClassicalFourthNat.BPay_2391
  · exact WuPaper.ClassicalFourthNat.BPay_2392
  · exact WuPaper.ClassicalFourthNat.BPay_2393
  · exact WuPaper.ClassicalFourthNat.BPay_2394
  · exact WuPaper.ClassicalFourthNat.BPay_2395
  · exact WuPaper.ClassicalFourthNat.BPay_2396
  · exact WuPaper.ClassicalFourthNat.BPay_2397
  · exact WuPaper.ClassicalFourthNat.BPay_2398
  · exact WuPaper.ClassicalFourthNat.BPay_2399
  · exact WuPaper.ClassicalFourthNat.BPay_2400
  · exact WuPaper.ClassicalFourthNat.BPay_2401
  · exact WuPaper.ClassicalFourthNat.BPay_2402
  · exact WuPaper.ClassicalFourthNat.BPay_2403
  · exact WuPaper.ClassicalFourthNat.BPay_2404
  · exact WuPaper.ClassicalFourthNat.BPay_2405
  · exact WuPaper.ClassicalFourthNat.BPay_2406
  · exact WuPaper.ClassicalFourthNat.BPay_2407
  · exact WuPaper.ClassicalFourthNat.BPay_2408
  · exact WuPaper.ClassicalFourthNat.BPay_2409
  · exact WuPaper.ClassicalFourthNat.BPay_2410
  · exact WuPaper.ClassicalFourthNat.BPay_2411
  · exact WuPaper.ClassicalFourthNat.BPay_2412
  · exact WuPaper.ClassicalFourthNat.BPay_2413
  · exact WuPaper.ClassicalFourthNat.BPay_2414
  · exact WuPaper.ClassicalFourthNat.BPay_2415
  · exact WuPaper.ClassicalFourthNat.BPay_2416
  · exact WuPaper.ClassicalFourthNat.BPay_2417
  · exact WuPaper.ClassicalFourthNat.BPay_2418
  · exact WuPaper.ClassicalFourthNat.BPay_2419
  · exact WuPaper.ClassicalFourthNat.BPay_2420
  · exact WuPaper.ClassicalFourthNat.BPay_2421
  · exact WuPaper.ClassicalFourthNat.BPay_2422
  · exact WuPaper.ClassicalFourthNat.BPay_2423
  · exact WuPaper.ClassicalFourthNat.BPay_2424
  · exact WuPaper.ClassicalFourthNat.BPay_2425
  · exact WuPaper.ClassicalFourthNat.BPay_2426
  · exact WuPaper.ClassicalFourthNat.BPay_2427
  · exact WuPaper.ClassicalFourthNat.BPay_2428
  · exact WuPaper.ClassicalFourthNat.BPay_2429
  · exact WuPaper.ClassicalFourthNat.BPay_2430
  · exact WuPaper.ClassicalFourthNat.BPay_2431
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_037
