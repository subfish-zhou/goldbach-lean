import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatCPay038
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem CPay_block_038 (j : Fin 64) (hj : 64*38+j.val < 2540) :
    CPay (64*38+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.CPay_2432
  · exact WuPaper.ClassicalFourthNat.CPay_2433
  · exact WuPaper.ClassicalFourthNat.CPay_2434
  · exact WuPaper.ClassicalFourthNat.CPay_2435
  · exact WuPaper.ClassicalFourthNat.CPay_2436
  · exact WuPaper.ClassicalFourthNat.CPay_2437
  · exact WuPaper.ClassicalFourthNat.CPay_2438
  · exact WuPaper.ClassicalFourthNat.CPay_2439
  · exact WuPaper.ClassicalFourthNat.CPay_2440
  · exact WuPaper.ClassicalFourthNat.CPay_2441
  · exact WuPaper.ClassicalFourthNat.CPay_2442
  · exact WuPaper.ClassicalFourthNat.CPay_2443
  · exact WuPaper.ClassicalFourthNat.CPay_2444
  · exact WuPaper.ClassicalFourthNat.CPay_2445
  · exact WuPaper.ClassicalFourthNat.CPay_2446
  · exact WuPaper.ClassicalFourthNat.CPay_2447
  · exact WuPaper.ClassicalFourthNat.CPay_2448
  · exact WuPaper.ClassicalFourthNat.CPay_2449
  · exact WuPaper.ClassicalFourthNat.CPay_2450
  · exact WuPaper.ClassicalFourthNat.CPay_2451
  · exact WuPaper.ClassicalFourthNat.CPay_2452
  · exact WuPaper.ClassicalFourthNat.CPay_2453
  · exact WuPaper.ClassicalFourthNat.CPay_2454
  · exact WuPaper.ClassicalFourthNat.CPay_2455
  · exact WuPaper.ClassicalFourthNat.CPay_2456
  · exact WuPaper.ClassicalFourthNat.CPay_2457
  · exact WuPaper.ClassicalFourthNat.CPay_2458
  · exact WuPaper.ClassicalFourthNat.CPay_2459
  · exact WuPaper.ClassicalFourthNat.CPay_2460
  · exact WuPaper.ClassicalFourthNat.CPay_2461
  · exact WuPaper.ClassicalFourthNat.CPay_2462
  · exact WuPaper.ClassicalFourthNat.CPay_2463
  · exact WuPaper.ClassicalFourthNat.CPay_2464
  · exact WuPaper.ClassicalFourthNat.CPay_2465
  · exact WuPaper.ClassicalFourthNat.CPay_2466
  · exact WuPaper.ClassicalFourthNat.CPay_2467
  · exact WuPaper.ClassicalFourthNat.CPay_2468
  · exact WuPaper.ClassicalFourthNat.CPay_2469
  · exact WuPaper.ClassicalFourthNat.CPay_2470
  · exact WuPaper.ClassicalFourthNat.CPay_2471
  · exact WuPaper.ClassicalFourthNat.CPay_2472
  · exact WuPaper.ClassicalFourthNat.CPay_2473
  · exact WuPaper.ClassicalFourthNat.CPay_2474
  · exact WuPaper.ClassicalFourthNat.CPay_2475
  · exact WuPaper.ClassicalFourthNat.CPay_2476
  · exact WuPaper.ClassicalFourthNat.CPay_2477
  · exact WuPaper.ClassicalFourthNat.CPay_2478
  · exact WuPaper.ClassicalFourthNat.CPay_2479
  · exact WuPaper.ClassicalFourthNat.CPay_2480
  · exact WuPaper.ClassicalFourthNat.CPay_2481
  · exact WuPaper.ClassicalFourthNat.CPay_2482
  · exact WuPaper.ClassicalFourthNat.CPay_2483
  · exact WuPaper.ClassicalFourthNat.CPay_2484
  · exact WuPaper.ClassicalFourthNat.CPay_2485
  · exact WuPaper.ClassicalFourthNat.CPay_2486
  · exact WuPaper.ClassicalFourthNat.CPay_2487
  · exact WuPaper.ClassicalFourthNat.CPay_2488
  · exact WuPaper.ClassicalFourthNat.CPay_2489
  · exact WuPaper.ClassicalFourthNat.CPay_2490
  · exact WuPaper.ClassicalFourthNat.CPay_2491
  · exact WuPaper.ClassicalFourthNat.CPay_2492
  · exact WuPaper.ClassicalFourthNat.CPay_2493
  · exact WuPaper.ClassicalFourthNat.CPay_2494
  · exact WuPaper.ClassicalFourthNat.CPay_2495
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.CPay_block_038
