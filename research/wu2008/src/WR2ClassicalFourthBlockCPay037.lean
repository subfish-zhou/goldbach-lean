import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatCPay037
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem CPay_block_037 (j : Fin 64) (hj : 64*37+j.val < 2540) :
    CPay (64*37+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.CPay_2368
  · exact WuPaper.ClassicalFourthNat.CPay_2369
  · exact WuPaper.ClassicalFourthNat.CPay_2370
  · exact WuPaper.ClassicalFourthNat.CPay_2371
  · exact WuPaper.ClassicalFourthNat.CPay_2372
  · exact WuPaper.ClassicalFourthNat.CPay_2373
  · exact WuPaper.ClassicalFourthNat.CPay_2374
  · exact WuPaper.ClassicalFourthNat.CPay_2375
  · exact WuPaper.ClassicalFourthNat.CPay_2376
  · exact WuPaper.ClassicalFourthNat.CPay_2377
  · exact WuPaper.ClassicalFourthNat.CPay_2378
  · exact WuPaper.ClassicalFourthNat.CPay_2379
  · exact WuPaper.ClassicalFourthNat.CPay_2380
  · exact WuPaper.ClassicalFourthNat.CPay_2381
  · exact WuPaper.ClassicalFourthNat.CPay_2382
  · exact WuPaper.ClassicalFourthNat.CPay_2383
  · exact WuPaper.ClassicalFourthNat.CPay_2384
  · exact WuPaper.ClassicalFourthNat.CPay_2385
  · exact WuPaper.ClassicalFourthNat.CPay_2386
  · exact WuPaper.ClassicalFourthNat.CPay_2387
  · exact WuPaper.ClassicalFourthNat.CPay_2388
  · exact WuPaper.ClassicalFourthNat.CPay_2389
  · exact WuPaper.ClassicalFourthNat.CPay_2390
  · exact WuPaper.ClassicalFourthNat.CPay_2391
  · exact WuPaper.ClassicalFourthNat.CPay_2392
  · exact WuPaper.ClassicalFourthNat.CPay_2393
  · exact WuPaper.ClassicalFourthNat.CPay_2394
  · exact WuPaper.ClassicalFourthNat.CPay_2395
  · exact WuPaper.ClassicalFourthNat.CPay_2396
  · exact WuPaper.ClassicalFourthNat.CPay_2397
  · exact WuPaper.ClassicalFourthNat.CPay_2398
  · exact WuPaper.ClassicalFourthNat.CPay_2399
  · exact WuPaper.ClassicalFourthNat.CPay_2400
  · exact WuPaper.ClassicalFourthNat.CPay_2401
  · exact WuPaper.ClassicalFourthNat.CPay_2402
  · exact WuPaper.ClassicalFourthNat.CPay_2403
  · exact WuPaper.ClassicalFourthNat.CPay_2404
  · exact WuPaper.ClassicalFourthNat.CPay_2405
  · exact WuPaper.ClassicalFourthNat.CPay_2406
  · exact WuPaper.ClassicalFourthNat.CPay_2407
  · exact WuPaper.ClassicalFourthNat.CPay_2408
  · exact WuPaper.ClassicalFourthNat.CPay_2409
  · exact WuPaper.ClassicalFourthNat.CPay_2410
  · exact WuPaper.ClassicalFourthNat.CPay_2411
  · exact WuPaper.ClassicalFourthNat.CPay_2412
  · exact WuPaper.ClassicalFourthNat.CPay_2413
  · exact WuPaper.ClassicalFourthNat.CPay_2414
  · exact WuPaper.ClassicalFourthNat.CPay_2415
  · exact WuPaper.ClassicalFourthNat.CPay_2416
  · exact WuPaper.ClassicalFourthNat.CPay_2417
  · exact WuPaper.ClassicalFourthNat.CPay_2418
  · exact WuPaper.ClassicalFourthNat.CPay_2419
  · exact WuPaper.ClassicalFourthNat.CPay_2420
  · exact WuPaper.ClassicalFourthNat.CPay_2421
  · exact WuPaper.ClassicalFourthNat.CPay_2422
  · exact WuPaper.ClassicalFourthNat.CPay_2423
  · exact WuPaper.ClassicalFourthNat.CPay_2424
  · exact WuPaper.ClassicalFourthNat.CPay_2425
  · exact WuPaper.ClassicalFourthNat.CPay_2426
  · exact WuPaper.ClassicalFourthNat.CPay_2427
  · exact WuPaper.ClassicalFourthNat.CPay_2428
  · exact WuPaper.ClassicalFourthNat.CPay_2429
  · exact WuPaper.ClassicalFourthNat.CPay_2430
  · exact WuPaper.ClassicalFourthNat.CPay_2431
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.CPay_block_037
