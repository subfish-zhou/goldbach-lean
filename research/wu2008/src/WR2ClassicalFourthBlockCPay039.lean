import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatCPay039
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem CPay_block_039 (j : Fin 64) (hj : 64*39+j.val < 2540) :
    CPay (64*39+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.CPay_2496
  · exact WuPaper.ClassicalFourthNat.CPay_2497
  · exact WuPaper.ClassicalFourthNat.CPay_2498
  · exact WuPaper.ClassicalFourthNat.CPay_2499
  · exact WuPaper.ClassicalFourthNat.CPay_2500
  · exact WuPaper.ClassicalFourthNat.CPay_2501
  · exact WuPaper.ClassicalFourthNat.CPay_2502
  · exact WuPaper.ClassicalFourthNat.CPay_2503
  · exact WuPaper.ClassicalFourthNat.CPay_2504
  · exact WuPaper.ClassicalFourthNat.CPay_2505
  · exact WuPaper.ClassicalFourthNat.CPay_2506
  · exact WuPaper.ClassicalFourthNat.CPay_2507
  · exact WuPaper.ClassicalFourthNat.CPay_2508
  · exact WuPaper.ClassicalFourthNat.CPay_2509
  · exact WuPaper.ClassicalFourthNat.CPay_2510
  · exact WuPaper.ClassicalFourthNat.CPay_2511
  · exact WuPaper.ClassicalFourthNat.CPay_2512
  · exact WuPaper.ClassicalFourthNat.CPay_2513
  · exact WuPaper.ClassicalFourthNat.CPay_2514
  · exact WuPaper.ClassicalFourthNat.CPay_2515
  · exact WuPaper.ClassicalFourthNat.CPay_2516
  · exact WuPaper.ClassicalFourthNat.CPay_2517
  · exact WuPaper.ClassicalFourthNat.CPay_2518
  · exact WuPaper.ClassicalFourthNat.CPay_2519
  · exact WuPaper.ClassicalFourthNat.CPay_2520
  · exact WuPaper.ClassicalFourthNat.CPay_2521
  · exact WuPaper.ClassicalFourthNat.CPay_2522
  · exact WuPaper.ClassicalFourthNat.CPay_2523
  · exact WuPaper.ClassicalFourthNat.CPay_2524
  · exact WuPaper.ClassicalFourthNat.CPay_2525
  · exact WuPaper.ClassicalFourthNat.CPay_2526
  · exact WuPaper.ClassicalFourthNat.CPay_2527
  · exact WuPaper.ClassicalFourthNat.CPay_2528
  · exact WuPaper.ClassicalFourthNat.CPay_2529
  · exact WuPaper.ClassicalFourthNat.CPay_2530
  · exact WuPaper.ClassicalFourthNat.CPay_2531
  · exact WuPaper.ClassicalFourthNat.CPay_2532
  · exact WuPaper.ClassicalFourthNat.CPay_2533
  · exact WuPaper.ClassicalFourthNat.CPay_2534
  · exact WuPaper.ClassicalFourthNat.CPay_2535
  · exact WuPaper.ClassicalFourthNat.CPay_2536
  · exact WuPaper.ClassicalFourthNat.CPay_2537
  · exact WuPaper.ClassicalFourthNat.CPay_2538
  · exact WuPaper.ClassicalFourthNat.CPay_2539
  · norm_num at hj
  · norm_num at hj
  · norm_num at hj
  · norm_num at hj
  · norm_num at hj
  · norm_num at hj
  · norm_num at hj
  · norm_num at hj
  · norm_num at hj
  · norm_num at hj
  · norm_num at hj
  · norm_num at hj
  · norm_num at hj
  · norm_num at hj
  · norm_num at hj
  · norm_num at hj
  · norm_num at hj
  · norm_num at hj
  · norm_num at hj
  · norm_num at hj
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.CPay_block_039
