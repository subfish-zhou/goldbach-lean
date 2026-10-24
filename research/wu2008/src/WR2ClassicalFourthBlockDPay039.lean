import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatDPay039
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem DPay_block_039 (j : Fin 64) (hj : 64*39+j.val < 2540) :
    DPay (64*39+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.DPay_2496
  · exact WuPaper.ClassicalFourthNat.DPay_2497
  · exact WuPaper.ClassicalFourthNat.DPay_2498
  · exact WuPaper.ClassicalFourthNat.DPay_2499
  · exact WuPaper.ClassicalFourthNat.DPay_2500
  · exact WuPaper.ClassicalFourthNat.DPay_2501
  · exact WuPaper.ClassicalFourthNat.DPay_2502
  · exact WuPaper.ClassicalFourthNat.DPay_2503
  · exact WuPaper.ClassicalFourthNat.DPay_2504
  · exact WuPaper.ClassicalFourthNat.DPay_2505
  · exact WuPaper.ClassicalFourthNat.DPay_2506
  · exact WuPaper.ClassicalFourthNat.DPay_2507
  · exact WuPaper.ClassicalFourthNat.DPay_2508
  · exact WuPaper.ClassicalFourthNat.DPay_2509
  · exact WuPaper.ClassicalFourthNat.DPay_2510
  · exact WuPaper.ClassicalFourthNat.DPay_2511
  · exact WuPaper.ClassicalFourthNat.DPay_2512
  · exact WuPaper.ClassicalFourthNat.DPay_2513
  · exact WuPaper.ClassicalFourthNat.DPay_2514
  · exact WuPaper.ClassicalFourthNat.DPay_2515
  · exact WuPaper.ClassicalFourthNat.DPay_2516
  · exact WuPaper.ClassicalFourthNat.DPay_2517
  · exact WuPaper.ClassicalFourthNat.DPay_2518
  · exact WuPaper.ClassicalFourthNat.DPay_2519
  · exact WuPaper.ClassicalFourthNat.DPay_2520
  · exact WuPaper.ClassicalFourthNat.DPay_2521
  · exact WuPaper.ClassicalFourthNat.DPay_2522
  · exact WuPaper.ClassicalFourthNat.DPay_2523
  · exact WuPaper.ClassicalFourthNat.DPay_2524
  · exact WuPaper.ClassicalFourthNat.DPay_2525
  · exact WuPaper.ClassicalFourthNat.DPay_2526
  · exact WuPaper.ClassicalFourthNat.DPay_2527
  · exact WuPaper.ClassicalFourthNat.DPay_2528
  · exact WuPaper.ClassicalFourthNat.DPay_2529
  · exact WuPaper.ClassicalFourthNat.DPay_2530
  · exact WuPaper.ClassicalFourthNat.DPay_2531
  · exact WuPaper.ClassicalFourthNat.DPay_2532
  · exact WuPaper.ClassicalFourthNat.DPay_2533
  · exact WuPaper.ClassicalFourthNat.DPay_2534
  · exact WuPaper.ClassicalFourthNat.DPay_2535
  · exact WuPaper.ClassicalFourthNat.DPay_2536
  · exact WuPaper.ClassicalFourthNat.DPay_2537
  · exact WuPaper.ClassicalFourthNat.DPay_2538
  · exact WuPaper.ClassicalFourthNat.DPay_2539
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
#print axioms WuPaper.ClassicalFourthConditions.DPay_block_039
