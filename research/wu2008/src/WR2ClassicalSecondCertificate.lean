import WR2ClassicalSecondPoints0
import WR2ClassicalSecondPoints1
import WR2ClassicalSecondPoints2
import WR2ClassicalSecondPoints3
import Wu08TerminalAlignment
noncomputable section
namespace WuPaper.ClassicalSecond
open ClassicalC Finset
def numerator : ℕ → ℕ
  | 0 => 18221162
  | 1 => 53685325
  | 2 => 87852166
  | 3 => 120729913
  | 4 => 152326739
  | 5 => 182650763
  | 6 => 211710053
  | 7 => 239512621
  | 8 => 266066429
  | 9 => 291379385
  | 10 => 315459346
  | 11 => 338314118
  | 12 => 359951457
  | 13 => 380379067
  | 14 => 399604602
  | 15 => 417635667
  | 16 => 434479817
  | 17 => 450144558
  | 18 => 464637348
  | 19 => 477965596
  | 20 => 490136663
  | 21 => 501157863
  | 22 => 511036463
  | 23 => 519779683
  | 24 => 527394695
  | 25 => 533888626
  | 26 => 539268559
  | 27 => 543541528
  | 28 => 546714524
  | 29 => 548794493
  | 30 => 549788335
  | 31 => 549702910
  | 32 => 548545028
  | 33 => 546321461
  | 34 => 543038935
  | 35 => 538704133
  | 36 => 533323697
  | 37 => 526904226
  | 38 => 519452276
  | 39 => 510974363
  | 40 => 501476961
  | 41 => 490966503
  | 42 => 479449381
  | 43 => 466931947
  | 44 => 453420512
  | 45 => 438921349
  | 46 => 423440689
  | 47 => 406984725
  | 48 => 389559612
  | 49 => 371171465
  | 50 => 351826360
  | 51 => 331530337
  | 52 => 310289395
  | 53 => 288109499
  | 54 => 264996573
  | 55 => 240956507
  | 56 => 215995152
  | 57 => 190118324
  | 58 => 163331802
  | 59 => 135641328
  | 60 => 107052611
  | 61 => 77571322
  | 62 => 47203097
  | 63 => 15953538
  | _ => 0
def payment (i : ℕ) : ℝ := (numerator i:ℝ)/1000000000000
theorem numerator_sum : (∑ i ∈ range 64, numerator i) = 23454073582 := by decide +kernel
set_option maxHeartbeats 2000000 in
theorem payments_paid (j : Fin 64) : payment j.val ≤ lowerKernel 1 (103/25)
    ((point (103/25) 64 j.val+point (103/25) 64 (j.val+1))/2) := by
  fin_cases j
  · change payment 0 ≤ lowerKernel 1 (103/25) ((point (103/25) 64 0+point (103/25) 64 1)/2)
    have hp : payment 0 = (18221162:ℝ)/1000000000000 := by rfl
    have hx : (point (103/25) 64 0+point (103/25) 64 1)/2 = (6403:ℝ)/3200 := by norm_num [point,step]
    rw [hp,hx]
    exact point_paid_0
  · change payment 1 ≤ lowerKernel 1 (103/25) ((point (103/25) 64 1+point (103/25) 64 2)/2)
    have hp : payment 1 = (53685325:ℝ)/1000000000000 := by rfl
    have hx : (point (103/25) 64 1+point (103/25) 64 2)/2 = (6409:ℝ)/3200 := by norm_num [point,step]
    rw [hp,hx]
    exact point_paid_1
  · change payment 2 ≤ lowerKernel 1 (103/25) ((point (103/25) 64 2+point (103/25) 64 3)/2)
    have hp : payment 2 = (87852166:ℝ)/1000000000000 := by rfl
    have hx : (point (103/25) 64 2+point (103/25) 64 3)/2 = (1283:ℝ)/640 := by norm_num [point,step]
    rw [hp,hx]
    exact point_paid_2
  · change payment 3 ≤ lowerKernel 1 (103/25) ((point (103/25) 64 3+point (103/25) 64 4)/2)
    have hp : payment 3 = (120729913:ℝ)/1000000000000 := by rfl
    have hx : (point (103/25) 64 3+point (103/25) 64 4)/2 = (6421:ℝ)/3200 := by norm_num [point,step]
    rw [hp,hx]
    exact point_paid_3
  · change payment 4 ≤ lowerKernel 1 (103/25) ((point (103/25) 64 4+point (103/25) 64 5)/2)
    have hp : payment 4 = (152326739:ℝ)/1000000000000 := by rfl
    have hx : (point (103/25) 64 4+point (103/25) 64 5)/2 = (6427:ℝ)/3200 := by norm_num [point,step]
    rw [hp,hx]
    exact point_paid_4
  · change payment 5 ≤ lowerKernel 1 (103/25) ((point (103/25) 64 5+point (103/25) 64 6)/2)
    have hp : payment 5 = (182650763:ℝ)/1000000000000 := by rfl
    have hx : (point (103/25) 64 5+point (103/25) 64 6)/2 = (6433:ℝ)/3200 := by norm_num [point,step]
    rw [hp,hx]
    exact point_paid_5
  · change payment 6 ≤ lowerKernel 1 (103/25) ((point (103/25) 64 6+point (103/25) 64 7)/2)
    have hp : payment 6 = (211710053:ℝ)/1000000000000 := by rfl
    have hx : (point (103/25) 64 6+point (103/25) 64 7)/2 = (6439:ℝ)/3200 := by norm_num [point,step]
    rw [hp,hx]
    exact point_paid_6
  · change payment 7 ≤ lowerKernel 1 (103/25) ((point (103/25) 64 7+point (103/25) 64 8)/2)
    have hp : payment 7 = (239512621:ℝ)/1000000000000 := by rfl
    have hx : (point (103/25) 64 7+point (103/25) 64 8)/2 = (1289:ℝ)/640 := by norm_num [point,step]
    rw [hp,hx]
    exact point_paid_7
  · change payment 8 ≤ lowerKernel 1 (103/25) ((point (103/25) 64 8+point (103/25) 64 9)/2)
    have hp : payment 8 = (266066429:ℝ)/1000000000000 := by rfl
    have hx : (point (103/25) 64 8+point (103/25) 64 9)/2 = (6451:ℝ)/3200 := by norm_num [point,step]
    rw [hp,hx]
    exact point_paid_8
  · change payment 9 ≤ lowerKernel 1 (103/25) ((point (103/25) 64 9+point (103/25) 64 10)/2)
    have hp : payment 9 = (291379385:ℝ)/1000000000000 := by rfl
    have hx : (point (103/25) 64 9+point (103/25) 64 10)/2 = (6457:ℝ)/3200 := by norm_num [point,step]
    rw [hp,hx]
    exact point_paid_9
  · change payment 10 ≤ lowerKernel 1 (103/25) ((point (103/25) 64 10+point (103/25) 64 11)/2)
    have hp : payment 10 = (315459346:ℝ)/1000000000000 := by rfl
    have hx : (point (103/25) 64 10+point (103/25) 64 11)/2 = (6463:ℝ)/3200 := by norm_num [point,step]
    rw [hp,hx]
    exact point_paid_10
  · change payment 11 ≤ lowerKernel 1 (103/25) ((point (103/25) 64 11+point (103/25) 64 12)/2)
    have hp : payment 11 = (338314118:ℝ)/1000000000000 := by rfl
    have hx : (point (103/25) 64 11+point (103/25) 64 12)/2 = (6469:ℝ)/3200 := by norm_num [point,step]
    rw [hp,hx]
    exact point_paid_11
  · change payment 12 ≤ lowerKernel 1 (103/25) ((point (103/25) 64 12+point (103/25) 64 13)/2)
    have hp : payment 12 = (359951457:ℝ)/1000000000000 := by rfl
    have hx : (point (103/25) 64 12+point (103/25) 64 13)/2 = (259:ℝ)/128 := by norm_num [point,step]
    rw [hp,hx]
    exact point_paid_12
  · change payment 13 ≤ lowerKernel 1 (103/25) ((point (103/25) 64 13+point (103/25) 64 14)/2)
    have hp : payment 13 = (380379067:ℝ)/1000000000000 := by rfl
    have hx : (point (103/25) 64 13+point (103/25) 64 14)/2 = (6481:ℝ)/3200 := by norm_num [point,step]
    rw [hp,hx]
    exact point_paid_13
  · change payment 14 ≤ lowerKernel 1 (103/25) ((point (103/25) 64 14+point (103/25) 64 15)/2)
    have hp : payment 14 = (399604602:ℝ)/1000000000000 := by rfl
    have hx : (point (103/25) 64 14+point (103/25) 64 15)/2 = (6487:ℝ)/3200 := by norm_num [point,step]
    rw [hp,hx]
    exact point_paid_14
  · change payment 15 ≤ lowerKernel 1 (103/25) ((point (103/25) 64 15+point (103/25) 64 16)/2)
    have hp : payment 15 = (417635667:ℝ)/1000000000000 := by rfl
    have hx : (point (103/25) 64 15+point (103/25) 64 16)/2 = (6493:ℝ)/3200 := by norm_num [point,step]
    rw [hp,hx]
    exact point_paid_15
  · change payment 16 ≤ lowerKernel 1 (103/25) ((point (103/25) 64 16+point (103/25) 64 17)/2)
    have hp : payment 16 = (434479817:ℝ)/1000000000000 := by rfl
    have hx : (point (103/25) 64 16+point (103/25) 64 17)/2 = (6499:ℝ)/3200 := by norm_num [point,step]
    rw [hp,hx]
    exact point_paid_16
  · change payment 17 ≤ lowerKernel 1 (103/25) ((point (103/25) 64 17+point (103/25) 64 18)/2)
    have hp : payment 17 = (450144558:ℝ)/1000000000000 := by rfl
    have hx : (point (103/25) 64 17+point (103/25) 64 18)/2 = (1301:ℝ)/640 := by norm_num [point,step]
    rw [hp,hx]
    exact point_paid_17
  · change payment 18 ≤ lowerKernel 1 (103/25) ((point (103/25) 64 18+point (103/25) 64 19)/2)
    have hp : payment 18 = (464637348:ℝ)/1000000000000 := by rfl
    have hx : (point (103/25) 64 18+point (103/25) 64 19)/2 = (6511:ℝ)/3200 := by norm_num [point,step]
    rw [hp,hx]
    exact point_paid_18
  · change payment 19 ≤ lowerKernel 1 (103/25) ((point (103/25) 64 19+point (103/25) 64 20)/2)
    have hp : payment 19 = (477965596:ℝ)/1000000000000 := by rfl
    have hx : (point (103/25) 64 19+point (103/25) 64 20)/2 = (6517:ℝ)/3200 := by norm_num [point,step]
    rw [hp,hx]
    exact point_paid_19
  · change payment 20 ≤ lowerKernel 1 (103/25) ((point (103/25) 64 20+point (103/25) 64 21)/2)
    have hp : payment 20 = (490136663:ℝ)/1000000000000 := by rfl
    have hx : (point (103/25) 64 20+point (103/25) 64 21)/2 = (6523:ℝ)/3200 := by norm_num [point,step]
    rw [hp,hx]
    exact point_paid_20
  · change payment 21 ≤ lowerKernel 1 (103/25) ((point (103/25) 64 21+point (103/25) 64 22)/2)
    have hp : payment 21 = (501157863:ℝ)/1000000000000 := by rfl
    have hx : (point (103/25) 64 21+point (103/25) 64 22)/2 = (6529:ℝ)/3200 := by norm_num [point,step]
    rw [hp,hx]
    exact point_paid_21
  · change payment 22 ≤ lowerKernel 1 (103/25) ((point (103/25) 64 22+point (103/25) 64 23)/2)
    have hp : payment 22 = (511036463:ℝ)/1000000000000 := by rfl
    have hx : (point (103/25) 64 22+point (103/25) 64 23)/2 = (1307:ℝ)/640 := by norm_num [point,step]
    rw [hp,hx]
    exact point_paid_22
  · change payment 23 ≤ lowerKernel 1 (103/25) ((point (103/25) 64 23+point (103/25) 64 24)/2)
    have hp : payment 23 = (519779683:ℝ)/1000000000000 := by rfl
    have hx : (point (103/25) 64 23+point (103/25) 64 24)/2 = (6541:ℝ)/3200 := by norm_num [point,step]
    rw [hp,hx]
    exact point_paid_23
  · change payment 24 ≤ lowerKernel 1 (103/25) ((point (103/25) 64 24+point (103/25) 64 25)/2)
    have hp : payment 24 = (527394695:ℝ)/1000000000000 := by rfl
    have hx : (point (103/25) 64 24+point (103/25) 64 25)/2 = (6547:ℝ)/3200 := by norm_num [point,step]
    rw [hp,hx]
    exact point_paid_24
  · change payment 25 ≤ lowerKernel 1 (103/25) ((point (103/25) 64 25+point (103/25) 64 26)/2)
    have hp : payment 25 = (533888626:ℝ)/1000000000000 := by rfl
    have hx : (point (103/25) 64 25+point (103/25) 64 26)/2 = (6553:ℝ)/3200 := by norm_num [point,step]
    rw [hp,hx]
    exact point_paid_25
  · change payment 26 ≤ lowerKernel 1 (103/25) ((point (103/25) 64 26+point (103/25) 64 27)/2)
    have hp : payment 26 = (539268559:ℝ)/1000000000000 := by rfl
    have hx : (point (103/25) 64 26+point (103/25) 64 27)/2 = (6559:ℝ)/3200 := by norm_num [point,step]
    rw [hp,hx]
    exact point_paid_26
  · change payment 27 ≤ lowerKernel 1 (103/25) ((point (103/25) 64 27+point (103/25) 64 28)/2)
    have hp : payment 27 = (543541528:ℝ)/1000000000000 := by rfl
    have hx : (point (103/25) 64 27+point (103/25) 64 28)/2 = (1313:ℝ)/640 := by norm_num [point,step]
    rw [hp,hx]
    exact point_paid_27
  · change payment 28 ≤ lowerKernel 1 (103/25) ((point (103/25) 64 28+point (103/25) 64 29)/2)
    have hp : payment 28 = (546714524:ℝ)/1000000000000 := by rfl
    have hx : (point (103/25) 64 28+point (103/25) 64 29)/2 = (6571:ℝ)/3200 := by norm_num [point,step]
    rw [hp,hx]
    exact point_paid_28
  · change payment 29 ≤ lowerKernel 1 (103/25) ((point (103/25) 64 29+point (103/25) 64 30)/2)
    have hp : payment 29 = (548794493:ℝ)/1000000000000 := by rfl
    have hx : (point (103/25) 64 29+point (103/25) 64 30)/2 = (6577:ℝ)/3200 := by norm_num [point,step]
    rw [hp,hx]
    exact point_paid_29
  · change payment 30 ≤ lowerKernel 1 (103/25) ((point (103/25) 64 30+point (103/25) 64 31)/2)
    have hp : payment 30 = (549788335:ℝ)/1000000000000 := by rfl
    have hx : (point (103/25) 64 30+point (103/25) 64 31)/2 = (6583:ℝ)/3200 := by norm_num [point,step]
    rw [hp,hx]
    exact point_paid_30
  · change payment 31 ≤ lowerKernel 1 (103/25) ((point (103/25) 64 31+point (103/25) 64 32)/2)
    have hp : payment 31 = (549702910:ℝ)/1000000000000 := by rfl
    have hx : (point (103/25) 64 31+point (103/25) 64 32)/2 = (6589:ℝ)/3200 := by norm_num [point,step]
    rw [hp,hx]
    exact point_paid_31
  · change payment 32 ≤ lowerKernel 1 (103/25) ((point (103/25) 64 32+point (103/25) 64 33)/2)
    have hp : payment 32 = (548545028:ℝ)/1000000000000 := by rfl
    have hx : (point (103/25) 64 32+point (103/25) 64 33)/2 = (1319:ℝ)/640 := by norm_num [point,step]
    rw [hp,hx]
    exact point_paid_32
  · change payment 33 ≤ lowerKernel 1 (103/25) ((point (103/25) 64 33+point (103/25) 64 34)/2)
    have hp : payment 33 = (546321461:ℝ)/1000000000000 := by rfl
    have hx : (point (103/25) 64 33+point (103/25) 64 34)/2 = (6601:ℝ)/3200 := by norm_num [point,step]
    rw [hp,hx]
    exact point_paid_33
  · change payment 34 ≤ lowerKernel 1 (103/25) ((point (103/25) 64 34+point (103/25) 64 35)/2)
    have hp : payment 34 = (543038935:ℝ)/1000000000000 := by rfl
    have hx : (point (103/25) 64 34+point (103/25) 64 35)/2 = (6607:ℝ)/3200 := by norm_num [point,step]
    rw [hp,hx]
    exact point_paid_34
  · change payment 35 ≤ lowerKernel 1 (103/25) ((point (103/25) 64 35+point (103/25) 64 36)/2)
    have hp : payment 35 = (538704133:ℝ)/1000000000000 := by rfl
    have hx : (point (103/25) 64 35+point (103/25) 64 36)/2 = (6613:ℝ)/3200 := by norm_num [point,step]
    rw [hp,hx]
    exact point_paid_35
  · change payment 36 ≤ lowerKernel 1 (103/25) ((point (103/25) 64 36+point (103/25) 64 37)/2)
    have hp : payment 36 = (533323697:ℝ)/1000000000000 := by rfl
    have hx : (point (103/25) 64 36+point (103/25) 64 37)/2 = (6619:ℝ)/3200 := by norm_num [point,step]
    rw [hp,hx]
    exact point_paid_36
  · change payment 37 ≤ lowerKernel 1 (103/25) ((point (103/25) 64 37+point (103/25) 64 38)/2)
    have hp : payment 37 = (526904226:ℝ)/1000000000000 := by rfl
    have hx : (point (103/25) 64 37+point (103/25) 64 38)/2 = (265:ℝ)/128 := by norm_num [point,step]
    rw [hp,hx]
    exact point_paid_37
  · change payment 38 ≤ lowerKernel 1 (103/25) ((point (103/25) 64 38+point (103/25) 64 39)/2)
    have hp : payment 38 = (519452276:ℝ)/1000000000000 := by rfl
    have hx : (point (103/25) 64 38+point (103/25) 64 39)/2 = (6631:ℝ)/3200 := by norm_num [point,step]
    rw [hp,hx]
    exact point_paid_38
  · change payment 39 ≤ lowerKernel 1 (103/25) ((point (103/25) 64 39+point (103/25) 64 40)/2)
    have hp : payment 39 = (510974363:ℝ)/1000000000000 := by rfl
    have hx : (point (103/25) 64 39+point (103/25) 64 40)/2 = (6637:ℝ)/3200 := by norm_num [point,step]
    rw [hp,hx]
    exact point_paid_39
  · change payment 40 ≤ lowerKernel 1 (103/25) ((point (103/25) 64 40+point (103/25) 64 41)/2)
    have hp : payment 40 = (501476961:ℝ)/1000000000000 := by rfl
    have hx : (point (103/25) 64 40+point (103/25) 64 41)/2 = (6643:ℝ)/3200 := by norm_num [point,step]
    rw [hp,hx]
    exact point_paid_40
  · change payment 41 ≤ lowerKernel 1 (103/25) ((point (103/25) 64 41+point (103/25) 64 42)/2)
    have hp : payment 41 = (490966503:ℝ)/1000000000000 := by rfl
    have hx : (point (103/25) 64 41+point (103/25) 64 42)/2 = (6649:ℝ)/3200 := by norm_num [point,step]
    rw [hp,hx]
    exact point_paid_41
  · change payment 42 ≤ lowerKernel 1 (103/25) ((point (103/25) 64 42+point (103/25) 64 43)/2)
    have hp : payment 42 = (479449381:ℝ)/1000000000000 := by rfl
    have hx : (point (103/25) 64 42+point (103/25) 64 43)/2 = (1331:ℝ)/640 := by norm_num [point,step]
    rw [hp,hx]
    exact point_paid_42
  · change payment 43 ≤ lowerKernel 1 (103/25) ((point (103/25) 64 43+point (103/25) 64 44)/2)
    have hp : payment 43 = (466931947:ℝ)/1000000000000 := by rfl
    have hx : (point (103/25) 64 43+point (103/25) 64 44)/2 = (6661:ℝ)/3200 := by norm_num [point,step]
    rw [hp,hx]
    exact point_paid_43
  · change payment 44 ≤ lowerKernel 1 (103/25) ((point (103/25) 64 44+point (103/25) 64 45)/2)
    have hp : payment 44 = (453420512:ℝ)/1000000000000 := by rfl
    have hx : (point (103/25) 64 44+point (103/25) 64 45)/2 = (6667:ℝ)/3200 := by norm_num [point,step]
    rw [hp,hx]
    exact point_paid_44
  · change payment 45 ≤ lowerKernel 1 (103/25) ((point (103/25) 64 45+point (103/25) 64 46)/2)
    have hp : payment 45 = (438921349:ℝ)/1000000000000 := by rfl
    have hx : (point (103/25) 64 45+point (103/25) 64 46)/2 = (6673:ℝ)/3200 := by norm_num [point,step]
    rw [hp,hx]
    exact point_paid_45
  · change payment 46 ≤ lowerKernel 1 (103/25) ((point (103/25) 64 46+point (103/25) 64 47)/2)
    have hp : payment 46 = (423440689:ℝ)/1000000000000 := by rfl
    have hx : (point (103/25) 64 46+point (103/25) 64 47)/2 = (6679:ℝ)/3200 := by norm_num [point,step]
    rw [hp,hx]
    exact point_paid_46
  · change payment 47 ≤ lowerKernel 1 (103/25) ((point (103/25) 64 47+point (103/25) 64 48)/2)
    have hp : payment 47 = (406984725:ℝ)/1000000000000 := by rfl
    have hx : (point (103/25) 64 47+point (103/25) 64 48)/2 = (1337:ℝ)/640 := by norm_num [point,step]
    rw [hp,hx]
    exact point_paid_47
  · change payment 48 ≤ lowerKernel 1 (103/25) ((point (103/25) 64 48+point (103/25) 64 49)/2)
    have hp : payment 48 = (389559612:ℝ)/1000000000000 := by rfl
    have hx : (point (103/25) 64 48+point (103/25) 64 49)/2 = (6691:ℝ)/3200 := by norm_num [point,step]
    rw [hp,hx]
    exact point_paid_48
  · change payment 49 ≤ lowerKernel 1 (103/25) ((point (103/25) 64 49+point (103/25) 64 50)/2)
    have hp : payment 49 = (371171465:ℝ)/1000000000000 := by rfl
    have hx : (point (103/25) 64 49+point (103/25) 64 50)/2 = (6697:ℝ)/3200 := by norm_num [point,step]
    rw [hp,hx]
    exact point_paid_49
  · change payment 50 ≤ lowerKernel 1 (103/25) ((point (103/25) 64 50+point (103/25) 64 51)/2)
    have hp : payment 50 = (351826360:ℝ)/1000000000000 := by rfl
    have hx : (point (103/25) 64 50+point (103/25) 64 51)/2 = (6703:ℝ)/3200 := by norm_num [point,step]
    rw [hp,hx]
    exact point_paid_50
  · change payment 51 ≤ lowerKernel 1 (103/25) ((point (103/25) 64 51+point (103/25) 64 52)/2)
    have hp : payment 51 = (331530337:ℝ)/1000000000000 := by rfl
    have hx : (point (103/25) 64 51+point (103/25) 64 52)/2 = (6709:ℝ)/3200 := by norm_num [point,step]
    rw [hp,hx]
    exact point_paid_51
  · change payment 52 ≤ lowerKernel 1 (103/25) ((point (103/25) 64 52+point (103/25) 64 53)/2)
    have hp : payment 52 = (310289395:ℝ)/1000000000000 := by rfl
    have hx : (point (103/25) 64 52+point (103/25) 64 53)/2 = (1343:ℝ)/640 := by norm_num [point,step]
    rw [hp,hx]
    exact point_paid_52
  · change payment 53 ≤ lowerKernel 1 (103/25) ((point (103/25) 64 53+point (103/25) 64 54)/2)
    have hp : payment 53 = (288109499:ℝ)/1000000000000 := by rfl
    have hx : (point (103/25) 64 53+point (103/25) 64 54)/2 = (6721:ℝ)/3200 := by norm_num [point,step]
    rw [hp,hx]
    exact point_paid_53
  · change payment 54 ≤ lowerKernel 1 (103/25) ((point (103/25) 64 54+point (103/25) 64 55)/2)
    have hp : payment 54 = (264996573:ℝ)/1000000000000 := by rfl
    have hx : (point (103/25) 64 54+point (103/25) 64 55)/2 = (6727:ℝ)/3200 := by norm_num [point,step]
    rw [hp,hx]
    exact point_paid_54
  · change payment 55 ≤ lowerKernel 1 (103/25) ((point (103/25) 64 55+point (103/25) 64 56)/2)
    have hp : payment 55 = (240956507:ℝ)/1000000000000 := by rfl
    have hx : (point (103/25) 64 55+point (103/25) 64 56)/2 = (6733:ℝ)/3200 := by norm_num [point,step]
    rw [hp,hx]
    exact point_paid_55
  · change payment 56 ≤ lowerKernel 1 (103/25) ((point (103/25) 64 56+point (103/25) 64 57)/2)
    have hp : payment 56 = (215995152:ℝ)/1000000000000 := by rfl
    have hx : (point (103/25) 64 56+point (103/25) 64 57)/2 = (6739:ℝ)/3200 := by norm_num [point,step]
    rw [hp,hx]
    exact point_paid_56
  · change payment 57 ≤ lowerKernel 1 (103/25) ((point (103/25) 64 57+point (103/25) 64 58)/2)
    have hp : payment 57 = (190118324:ℝ)/1000000000000 := by rfl
    have hx : (point (103/25) 64 57+point (103/25) 64 58)/2 = (1349:ℝ)/640 := by norm_num [point,step]
    rw [hp,hx]
    exact point_paid_57
  · change payment 58 ≤ lowerKernel 1 (103/25) ((point (103/25) 64 58+point (103/25) 64 59)/2)
    have hp : payment 58 = (163331802:ℝ)/1000000000000 := by rfl
    have hx : (point (103/25) 64 58+point (103/25) 64 59)/2 = (6751:ℝ)/3200 := by norm_num [point,step]
    rw [hp,hx]
    exact point_paid_58
  · change payment 59 ≤ lowerKernel 1 (103/25) ((point (103/25) 64 59+point (103/25) 64 60)/2)
    have hp : payment 59 = (135641328:ℝ)/1000000000000 := by rfl
    have hx : (point (103/25) 64 59+point (103/25) 64 60)/2 = (6757:ℝ)/3200 := by norm_num [point,step]
    rw [hp,hx]
    exact point_paid_59
  · change payment 60 ≤ lowerKernel 1 (103/25) ((point (103/25) 64 60+point (103/25) 64 61)/2)
    have hp : payment 60 = (107052611:ℝ)/1000000000000 := by rfl
    have hx : (point (103/25) 64 60+point (103/25) 64 61)/2 = (6763:ℝ)/3200 := by norm_num [point,step]
    rw [hp,hx]
    exact point_paid_60
  · change payment 61 ≤ lowerKernel 1 (103/25) ((point (103/25) 64 61+point (103/25) 64 62)/2)
    have hp : payment 61 = (77571322:ℝ)/1000000000000 := by rfl
    have hx : (point (103/25) 64 61+point (103/25) 64 62)/2 = (6769:ℝ)/3200 := by norm_num [point,step]
    rw [hp,hx]
    exact point_paid_61
  · change payment 62 ≤ lowerKernel 1 (103/25) ((point (103/25) 64 62+point (103/25) 64 63)/2)
    have hp : payment 62 = (47203097:ℝ)/1000000000000 := by rfl
    have hx : (point (103/25) 64 62+point (103/25) 64 63)/2 = (271:ℝ)/128 := by norm_num [point,step]
    rw [hp,hx]
    exact point_paid_62
  · change payment 63 ≤ lowerKernel 1 (103/25) ((point (103/25) 64 63+point (103/25) 64 64)/2)
    have hp : payment 63 = (15953538:ℝ)/1000000000000 := by rfl
    have hx : (point (103/25) 64 63+point (103/25) 64 64)/2 = (6781:ℝ)/3200 := by norm_num [point,step]
    rw [hp,hx]
    exact point_paid_63

theorem C_lower : (438357:ℝ)/10000000000 ≤ Wu08OriginalFirstSteps.C (103/25) := by
  have h := uniform_lower (s := (103:ℝ)/25) (by norm_num) (by norm_num) 1 64 (by norm_num) payment
    (fun i hi => payments_paid ⟨i,hi⟩)
  apply le_trans _ h
  simp only [payment,← sum_div,← Nat.cast_sum,numerator_sum]
  norm_num [step]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem log_lower : (11378330018:ℝ)/10000000000 ≤ Real.log (78/25) := by
  apply le_trans _ (ClassicalLogSplit.bounds 1 (by norm_num : (1:ℝ) ≤ 78/25)).2.1
  norm_num [ClassicalLogSplit.lower,WuSource.SrcFourEnclosure.logLo,Finset.sum_range_succ]

theorem second_main_lower : (9103014:ℝ)/1000000 ≤ Wu08TerminalAlignment.secondMain := by
  rw [Wu08TerminalAlignment.second_exact]
  linarith only [C_lower,log_lower]

end WuPaper.ClassicalSecond
#print axioms WuPaper.ClassicalSecond.second_main_lower
