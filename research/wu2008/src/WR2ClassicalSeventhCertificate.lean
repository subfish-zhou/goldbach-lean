import WR2ClassicalSeventhPoints00
import WR2ClassicalSeventhPoints01
import WR2ClassicalSeventhPoints02
import WR2ClassicalSeventhPoints03
import WR2ClassicalSeventhPoints04
import WR2ClassicalSeventhPoints05
import WR2ClassicalSeventhPoints06
import WR2ClassicalSeventhPoints07
import WR2ClassicalSeventhPoints08
import WR2ClassicalSeventhPoints09
import WR2ClassicalSeventhPoints10
import WR2ClassicalSeventhPoints11
import WR2ClassicalSeventhPoints12
import WR2ClassicalSeventhPoints13
import WR2ClassicalSeventhPoints14
import WR2ClassicalSeventhPoints15
noncomputable section
namespace WuPaper.ClassicalSeventh
open Finset
def numerator : ℕ → ℕ
  | 0 => 2514355064951
  | 1 => 2503616333442
  | 2 => 2492888541568
  | 3 => 2482171637695
  | 4 => 2471465570309
  | 5 => 2460770288025
  | 6 => 2450085739580
  | 7 => 2439411873831
  | 8 => 2428748639763
  | 9 => 2418095986478
  | 10 => 2407453863200
  | 11 => 2396822219272
  | 12 => 2386201004158
  | 13 => 2375590167439
  | 14 => 2364989658812
  | 15 => 2354399428093
  | 16 => 2343819425213
  | 17 => 2333249600219
  | 18 => 2322689903272
  | 19 => 2312140284645
  | 20 => 2301600694726
  | 21 => 2291071084015
  | 22 => 2280551403122
  | 23 => 2270041602770
  | 24 => 2259541633789
  | 25 => 2249051447121
  | 26 => 2238570993814
  | 27 => 2228100225026
  | 28 => 2217639092020
  | 29 => 2207187546166
  | 30 => 2196745538940
  | 31 => 2186313021922
  | 32 => 2175889946797
  | 33 => 2165476265351
  | 34 => 2155071929477
  | 35 => 2144676891164
  | 36 => 2134291102509
  | 37 => 2123914515703
  | 38 => 2113547083040
  | 39 => 2103188756914
  | 40 => 2092839489815
  | 41 => 2082499234332
  | 42 => 2072167943150
  | 43 => 2061845569051
  | 44 => 2051532064913
  | 45 => 2041227383707
  | 46 => 2030931478500
  | 47 => 2020644302451
  | 48 => 2010365808813
  | 49 => 2000095950931
  | 50 => 1989834682240
  | 51 => 1979581956267
  | 52 => 1969337726629
  | 53 => 1959101947031
  | 54 => 1948874571269
  | 55 => 1938655553224
  | 56 => 1928444846868
  | 57 => 1918242406256
  | 58 => 1908048185530
  | 59 => 1897862138920
  | 60 => 1887684220737
  | 61 => 1877514385377
  | 62 => 1867352587321
  | 63 => 1857198781130
  | 64 => 1847052921450
  | 65 => 1836914963005
  | 66 => 1826784860602
  | 67 => 1816662569128
  | 68 => 1806548043547
  | 69 => 1796441238905
  | 70 => 1786342110324
  | 71 => 1776250613004
  | 72 => 1766166702221
  | 73 => 1756090333328
  | 74 => 1746021461753
  | 75 => 1735960042999
  | 76 => 1725906032644
  | 77 => 1715859386338
  | 78 => 1705820059804
  | 79 => 1695788008839
  | 80 => 1685763189310
  | 81 => 1675745557155
  | 82 => 1665735068384
  | 83 => 1655731679075
  | 84 => 1645735345375
  | 85 => 1635746023501
  | 86 => 1625763669738
  | 87 => 1615788240435
  | 88 => 1605819692011
  | 89 => 1595857980949
  | 90 => 1585903063800
  | 91 => 1575954897176
  | 92 => 1566013437755
  | 93 => 1556078642280
  | 94 => 1546150467553
  | 95 => 1536228870443
  | 96 => 1526313807876
  | 97 => 1516405236842
  | 98 => 1506503114391
  | 99 => 1496607397632
  | 100 => 1486718043733
  | 101 => 1476835009922
  | 102 => 1466958253483
  | 103 => 1457087731759
  | 104 => 1447223402150
  | 105 => 1437365222109
  | 106 => 1427513149149
  | 107 => 1417667140834
  | 108 => 1407827154785
  | 109 => 1397993148675
  | 110 => 1388165080231
  | 111 => 1378342907233
  | 112 => 1368526587511
  | 113 => 1358716078948
  | 114 => 1348911339478
  | 115 => 1339112327082
  | 116 => 1329318999795
  | 117 => 1319531315697
  | 118 => 1309749232920
  | 119 => 1299972709639
  | 120 => 1290201704081
  | 121 => 1280436174516
  | 122 => 1270676079261
  | 123 => 1260921376679
  | 124 => 1251172025178
  | 125 => 1241427983208
  | 126 => 1231689209265
  | 127 => 1221955661886
  | 128 => 1212227299651
  | 129 => 1202504081183
  | 130 => 1192785965144
  | 131 => 1183072910239
  | 132 => 1173364875210
  | 133 => 1163661818841
  | 134 => 1153963699955
  | 135 => 1144270477410
  | 136 => 1134582110106
  | 137 => 1124898556975
  | 138 => 1115219776991
  | 139 => 1105545729160
  | 140 => 1095876372523
  | 141 => 1086211666160
  | 142 => 1076551569180
  | 143 => 1066896040728
  | 144 => 1057245039982
  | 145 => 1047598526152
  | 146 => 1037956458479
  | 147 => 1028318796237
  | 148 => 1018685498728
  | 149 => 1009056525287
  | 150 => 999431835276
  | 151 => 989811388087
  | 152 => 980195143140
  | 153 => 970583059882
  | 154 => 960975097787
  | 155 => 951371216357
  | 156 => 941771375120
  | 157 => 932175533626
  | 158 => 922583651453
  | 159 => 912995688202
  | 160 => 903411603497
  | 161 => 893831356987
  | 162 => 884254908341
  | 163 => 874682217250
  | 164 => 865113243428
  | 165 => 855547946608
  | 166 => 845986286543
  | 167 => 836428223007
  | 168 => 826873715790
  | 169 => 817322724703
  | 170 => 807775209573
  | 171 => 798231130245
  | 172 => 788690446580
  | 173 => 779153118455
  | 174 => 769619105762
  | 175 => 760088368407
  | 176 => 750560866313
  | 177 => 741036559413
  | 178 => 731515407655
  | 179 => 721997370998
  | 180 => 712482409414
  | 181 => 702970482885
  | 182 => 693461551405
  | 183 => 683955574976
  | 184 => 674452513610
  | 185 => 664952327329
  | 186 => 655454976162
  | 187 => 645960420146
  | 188 => 636468619323
  | 189 => 626979533745
  | 190 => 617493123466
  | 191 => 608009348547
  | 192 => 598528169055
  | 193 => 589049545057
  | 194 => 579573436627
  | 195 => 570099803839
  | 196 => 560628606772
  | 197 => 551159805504
  | 198 => 541693360114
  | 199 => 532229230682
  | 200 => 522767377289
  | 201 => 513307760013
  | 202 => 503850338931
  | 203 => 494395074118
  | 204 => 484941925645
  | 205 => 475490853583
  | 206 => 466041817994
  | 207 => 456594778940
  | 208 => 447149696476
  | 209 => 437706530649
  | 210 => 428265241502
  | 211 => 418825789072
  | 212 => 409388133384
  | 213 => 399952234458
  | 214 => 390518052304
  | 215 => 381085546922
  | 216 => 371654678303
  | 217 => 362225406425
  | 218 => 352797691257
  | 219 => 343371492753
  | 220 => 333946770857
  | 221 => 324523485497
  | 222 => 315101596588
  | 223 => 305681064032
  | 224 => 296261847712
  | 225 => 286843907498
  | 226 => 277427203242
  | 227 => 268011694778
  | 228 => 258597341925
  | 229 => 249184104480
  | 230 => 239771942221
  | 231 => 230360814910
  | 232 => 220950682283
  | 233 => 211541504058
  | 234 => 202133239931
  | 235 => 192725849574
  | 236 => 183319292637
  | 237 => 173913528745
  | 238 => 164508517501
  | 239 => 155104218478
  | 240 => 145700591229
  | 241 => 136297595275
  | 242 => 126895190113
  | 243 => 117493335211
  | 244 => 108091990009
  | 245 => 98691113916
  | 246 => 89290666314
  | 247 => 79890606551
  | 248 => 70490893946
  | 249 => 61091487785
  | 250 => 51692347321
  | 251 => 42293431774
  | 252 => 32894700329
  | 253 => 23496112138
  | 254 => 14097626316
  | 255 => 4699201942
  | _ => 0
def payment (i : ℕ) : ℝ := (numerator i:ℝ)/1000000000000
set_option maxRecDepth 10000 in
theorem numerator_sum : (∑ i ∈ range 256, numerator i) = 315209245346190 := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem payments_paid (j : Fin 256) : upperValue ((point j.val+point (j.val+1))/2) ≤ payment j.val := by
  fin_cases j
  · change upperValue ((point 0+point 1)/2) ≤ payment 0
    have hp : payment 0 = (2514355064951:ℝ)/1000000000000 := rfl
    have hx : (point 0+point 1)/2 = (1117145:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_0
  · change upperValue ((point 1+point 2)/2) ≤ payment 1
    have hp : payment 1 = (2503616333442:ℝ)/1000000000000 := rfl
    have hx : (point 1+point 2)/2 = (372697:ℝ)/1358848 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_1
  · change upperValue ((point 2+point 3)/2) ≤ payment 2
    have hp : payment 2 = (2492888541568:ℝ)/1000000000000 := rfl
    have hx : (point 2+point 3)/2 = (1119037:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_2
  · change upperValue ((point 3+point 4)/2) ≤ payment 3
    have hp : payment 3 = (2482171637695:ℝ)/1000000000000 := rfl
    have hx : (point 3+point 4)/2 = (1119983:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_3
  · change upperValue ((point 4+point 5)/2) ≤ payment 4
    have hp : payment 4 = (2471465570309:ℝ)/1000000000000 := rfl
    have hx : (point 4+point 5)/2 = (373643:ℝ)/1358848 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_4
  · change upperValue ((point 5+point 6)/2) ≤ payment 5
    have hp : payment 5 = (2460770288025:ℝ)/1000000000000 := rfl
    have hx : (point 5+point 6)/2 = (1121875:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_5
  · change upperValue ((point 6+point 7)/2) ≤ payment 6
    have hp : payment 6 = (2450085739580:ℝ)/1000000000000 := rfl
    have hx : (point 6+point 7)/2 = (1122821:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_6
  · change upperValue ((point 7+point 8)/2) ≤ payment 7
    have hp : payment 7 = (2439411873831:ℝ)/1000000000000 := rfl
    have hx : (point 7+point 8)/2 = (374589:ℝ)/1358848 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_7
  · change upperValue ((point 8+point 9)/2) ≤ payment 8
    have hp : payment 8 = (2428748639763:ℝ)/1000000000000 := rfl
    have hx : (point 8+point 9)/2 = (1124713:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_8
  · change upperValue ((point 9+point 10)/2) ≤ payment 9
    have hp : payment 9 = (2418095986478:ℝ)/1000000000000 := rfl
    have hx : (point 9+point 10)/2 = (1125659:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_9
  · change upperValue ((point 10+point 11)/2) ≤ payment 10
    have hp : payment 10 = (2407453863200:ℝ)/1000000000000 := rfl
    have hx : (point 10+point 11)/2 = (375535:ℝ)/1358848 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_10
  · change upperValue ((point 11+point 12)/2) ≤ payment 11
    have hp : payment 11 = (2396822219272:ℝ)/1000000000000 := rfl
    have hx : (point 11+point 12)/2 = (1127551:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_11
  · change upperValue ((point 12+point 13)/2) ≤ payment 12
    have hp : payment 12 = (2386201004158:ℝ)/1000000000000 := rfl
    have hx : (point 12+point 13)/2 = (1128497:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_12
  · change upperValue ((point 13+point 14)/2) ≤ payment 13
    have hp : payment 13 = (2375590167439:ℝ)/1000000000000 := rfl
    have hx : (point 13+point 14)/2 = (376481:ℝ)/1358848 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_13
  · change upperValue ((point 14+point 15)/2) ≤ payment 14
    have hp : payment 14 = (2364989658812:ℝ)/1000000000000 := rfl
    have hx : (point 14+point 15)/2 = (1130389:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_14
  · change upperValue ((point 15+point 16)/2) ≤ payment 15
    have hp : payment 15 = (2354399428093:ℝ)/1000000000000 := rfl
    have hx : (point 15+point 16)/2 = (1131335:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_15
  · change upperValue ((point 16+point 17)/2) ≤ payment 16
    have hp : payment 16 = (2343819425213:ℝ)/1000000000000 := rfl
    have hx : (point 16+point 17)/2 = (377427:ℝ)/1358848 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_16
  · change upperValue ((point 17+point 18)/2) ≤ payment 17
    have hp : payment 17 = (2333249600219:ℝ)/1000000000000 := rfl
    have hx : (point 17+point 18)/2 = (1133227:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_17
  · change upperValue ((point 18+point 19)/2) ≤ payment 18
    have hp : payment 18 = (2322689903272:ℝ)/1000000000000 := rfl
    have hx : (point 18+point 19)/2 = (1134173:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_18
  · change upperValue ((point 19+point 20)/2) ≤ payment 19
    have hp : payment 19 = (2312140284645:ℝ)/1000000000000 := rfl
    have hx : (point 19+point 20)/2 = (378373:ℝ)/1358848 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_19
  · change upperValue ((point 20+point 21)/2) ≤ payment 20
    have hp : payment 20 = (2301600694726:ℝ)/1000000000000 := rfl
    have hx : (point 20+point 21)/2 = (1136065:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_20
  · change upperValue ((point 21+point 22)/2) ≤ payment 21
    have hp : payment 21 = (2291071084015:ℝ)/1000000000000 := rfl
    have hx : (point 21+point 22)/2 = (1137011:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_21
  · change upperValue ((point 22+point 23)/2) ≤ payment 22
    have hp : payment 22 = (2280551403122:ℝ)/1000000000000 := rfl
    have hx : (point 22+point 23)/2 = (379319:ℝ)/1358848 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_22
  · change upperValue ((point 23+point 24)/2) ≤ payment 23
    have hp : payment 23 = (2270041602770:ℝ)/1000000000000 := rfl
    have hx : (point 23+point 24)/2 = (1138903:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_23
  · change upperValue ((point 24+point 25)/2) ≤ payment 24
    have hp : payment 24 = (2259541633789:ℝ)/1000000000000 := rfl
    have hx : (point 24+point 25)/2 = (1139849:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_24
  · change upperValue ((point 25+point 26)/2) ≤ payment 25
    have hp : payment 25 = (2249051447121:ℝ)/1000000000000 := rfl
    have hx : (point 25+point 26)/2 = (380265:ℝ)/1358848 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_25
  · change upperValue ((point 26+point 27)/2) ≤ payment 26
    have hp : payment 26 = (2238570993814:ℝ)/1000000000000 := rfl
    have hx : (point 26+point 27)/2 = (1141741:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_26
  · change upperValue ((point 27+point 28)/2) ≤ payment 27
    have hp : payment 27 = (2228100225026:ℝ)/1000000000000 := rfl
    have hx : (point 27+point 28)/2 = (1142687:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_27
  · change upperValue ((point 28+point 29)/2) ≤ payment 28
    have hp : payment 28 = (2217639092020:ℝ)/1000000000000 := rfl
    have hx : (point 28+point 29)/2 = (381211:ℝ)/1358848 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_28
  · change upperValue ((point 29+point 30)/2) ≤ payment 29
    have hp : payment 29 = (2207187546166:ℝ)/1000000000000 := rfl
    have hx : (point 29+point 30)/2 = (1144579:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_29
  · change upperValue ((point 30+point 31)/2) ≤ payment 30
    have hp : payment 30 = (2196745538940:ℝ)/1000000000000 := rfl
    have hx : (point 30+point 31)/2 = (1145525:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_30
  · change upperValue ((point 31+point 32)/2) ≤ payment 31
    have hp : payment 31 = (2186313021922:ℝ)/1000000000000 := rfl
    have hx : (point 31+point 32)/2 = (382157:ℝ)/1358848 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_31
  · change upperValue ((point 32+point 33)/2) ≤ payment 32
    have hp : payment 32 = (2175889946797:ℝ)/1000000000000 := rfl
    have hx : (point 32+point 33)/2 = (1147417:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_32
  · change upperValue ((point 33+point 34)/2) ≤ payment 33
    have hp : payment 33 = (2165476265351:ℝ)/1000000000000 := rfl
    have hx : (point 33+point 34)/2 = (1148363:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_33
  · change upperValue ((point 34+point 35)/2) ≤ payment 34
    have hp : payment 34 = (2155071929477:ℝ)/1000000000000 := rfl
    have hx : (point 34+point 35)/2 = (383103:ℝ)/1358848 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_34
  · change upperValue ((point 35+point 36)/2) ≤ payment 35
    have hp : payment 35 = (2144676891164:ℝ)/1000000000000 := rfl
    have hx : (point 35+point 36)/2 = (1150255:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_35
  · change upperValue ((point 36+point 37)/2) ≤ payment 36
    have hp : payment 36 = (2134291102509:ℝ)/1000000000000 := rfl
    have hx : (point 36+point 37)/2 = (1151201:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_36
  · change upperValue ((point 37+point 38)/2) ≤ payment 37
    have hp : payment 37 = (2123914515703:ℝ)/1000000000000 := rfl
    have hx : (point 37+point 38)/2 = (384049:ℝ)/1358848 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_37
  · change upperValue ((point 38+point 39)/2) ≤ payment 38
    have hp : payment 38 = (2113547083040:ℝ)/1000000000000 := rfl
    have hx : (point 38+point 39)/2 = (1153093:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_38
  · change upperValue ((point 39+point 40)/2) ≤ payment 39
    have hp : payment 39 = (2103188756914:ℝ)/1000000000000 := rfl
    have hx : (point 39+point 40)/2 = (1154039:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_39
  · change upperValue ((point 40+point 41)/2) ≤ payment 40
    have hp : payment 40 = (2092839489815:ℝ)/1000000000000 := rfl
    have hx : (point 40+point 41)/2 = (384995:ℝ)/1358848 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_40
  · change upperValue ((point 41+point 42)/2) ≤ payment 41
    have hp : payment 41 = (2082499234332:ℝ)/1000000000000 := rfl
    have hx : (point 41+point 42)/2 = (1155931:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_41
  · change upperValue ((point 42+point 43)/2) ≤ payment 42
    have hp : payment 42 = (2072167943150:ℝ)/1000000000000 := rfl
    have hx : (point 42+point 43)/2 = (1156877:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_42
  · change upperValue ((point 43+point 44)/2) ≤ payment 43
    have hp : payment 43 = (2061845569051:ℝ)/1000000000000 := rfl
    have hx : (point 43+point 44)/2 = (385941:ℝ)/1358848 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_43
  · change upperValue ((point 44+point 45)/2) ≤ payment 44
    have hp : payment 44 = (2051532064913:ℝ)/1000000000000 := rfl
    have hx : (point 44+point 45)/2 = (1158769:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_44
  · change upperValue ((point 45+point 46)/2) ≤ payment 45
    have hp : payment 45 = (2041227383707:ℝ)/1000000000000 := rfl
    have hx : (point 45+point 46)/2 = (1159715:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_45
  · change upperValue ((point 46+point 47)/2) ≤ payment 46
    have hp : payment 46 = (2030931478500:ℝ)/1000000000000 := rfl
    have hx : (point 46+point 47)/2 = (386887:ℝ)/1358848 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_46
  · change upperValue ((point 47+point 48)/2) ≤ payment 47
    have hp : payment 47 = (2020644302451:ℝ)/1000000000000 := rfl
    have hx : (point 47+point 48)/2 = (1161607:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_47
  · change upperValue ((point 48+point 49)/2) ≤ payment 48
    have hp : payment 48 = (2010365808813:ℝ)/1000000000000 := rfl
    have hx : (point 48+point 49)/2 = (1162553:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_48
  · change upperValue ((point 49+point 50)/2) ≤ payment 49
    have hp : payment 49 = (2000095950931:ℝ)/1000000000000 := rfl
    have hx : (point 49+point 50)/2 = (387833:ℝ)/1358848 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_49
  · change upperValue ((point 50+point 51)/2) ≤ payment 50
    have hp : payment 50 = (1989834682240:ℝ)/1000000000000 := rfl
    have hx : (point 50+point 51)/2 = (1164445:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_50
  · change upperValue ((point 51+point 52)/2) ≤ payment 51
    have hp : payment 51 = (1979581956267:ℝ)/1000000000000 := rfl
    have hx : (point 51+point 52)/2 = (1165391:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_51
  · change upperValue ((point 52+point 53)/2) ≤ payment 52
    have hp : payment 52 = (1969337726629:ℝ)/1000000000000 := rfl
    have hx : (point 52+point 53)/2 = (388779:ℝ)/1358848 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_52
  · change upperValue ((point 53+point 54)/2) ≤ payment 53
    have hp : payment 53 = (1959101947031:ℝ)/1000000000000 := rfl
    have hx : (point 53+point 54)/2 = (1167283:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_53
  · change upperValue ((point 54+point 55)/2) ≤ payment 54
    have hp : payment 54 = (1948874571269:ℝ)/1000000000000 := rfl
    have hx : (point 54+point 55)/2 = (1168229:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_54
  · change upperValue ((point 55+point 56)/2) ≤ payment 55
    have hp : payment 55 = (1938655553224:ℝ)/1000000000000 := rfl
    have hx : (point 55+point 56)/2 = (389725:ℝ)/1358848 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_55
  · change upperValue ((point 56+point 57)/2) ≤ payment 56
    have hp : payment 56 = (1928444846868:ℝ)/1000000000000 := rfl
    have hx : (point 56+point 57)/2 = (1170121:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_56
  · change upperValue ((point 57+point 58)/2) ≤ payment 57
    have hp : payment 57 = (1918242406256:ℝ)/1000000000000 := rfl
    have hx : (point 57+point 58)/2 = (1171067:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_57
  · change upperValue ((point 58+point 59)/2) ≤ payment 58
    have hp : payment 58 = (1908048185530:ℝ)/1000000000000 := rfl
    have hx : (point 58+point 59)/2 = (390671:ℝ)/1358848 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_58
  · change upperValue ((point 59+point 60)/2) ≤ payment 59
    have hp : payment 59 = (1897862138920:ℝ)/1000000000000 := rfl
    have hx : (point 59+point 60)/2 = (1172959:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_59
  · change upperValue ((point 60+point 61)/2) ≤ payment 60
    have hp : payment 60 = (1887684220737:ℝ)/1000000000000 := rfl
    have hx : (point 60+point 61)/2 = (1173905:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_60
  · change upperValue ((point 61+point 62)/2) ≤ payment 61
    have hp : payment 61 = (1877514385377:ℝ)/1000000000000 := rfl
    have hx : (point 61+point 62)/2 = (391617:ℝ)/1358848 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_61
  · change upperValue ((point 62+point 63)/2) ≤ payment 62
    have hp : payment 62 = (1867352587321:ℝ)/1000000000000 := rfl
    have hx : (point 62+point 63)/2 = (1175797:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_62
  · change upperValue ((point 63+point 64)/2) ≤ payment 63
    have hp : payment 63 = (1857198781130:ℝ)/1000000000000 := rfl
    have hx : (point 63+point 64)/2 = (1176743:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_63
  · change upperValue ((point 64+point 65)/2) ≤ payment 64
    have hp : payment 64 = (1847052921450:ℝ)/1000000000000 := rfl
    have hx : (point 64+point 65)/2 = (392563:ℝ)/1358848 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_64
  · change upperValue ((point 65+point 66)/2) ≤ payment 65
    have hp : payment 65 = (1836914963005:ℝ)/1000000000000 := rfl
    have hx : (point 65+point 66)/2 = (1178635:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_65
  · change upperValue ((point 66+point 67)/2) ≤ payment 66
    have hp : payment 66 = (1826784860602:ℝ)/1000000000000 := rfl
    have hx : (point 66+point 67)/2 = (1179581:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_66
  · change upperValue ((point 67+point 68)/2) ≤ payment 67
    have hp : payment 67 = (1816662569128:ℝ)/1000000000000 := rfl
    have hx : (point 67+point 68)/2 = (393509:ℝ)/1358848 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_67
  · change upperValue ((point 68+point 69)/2) ≤ payment 68
    have hp : payment 68 = (1806548043547:ℝ)/1000000000000 := rfl
    have hx : (point 68+point 69)/2 = (1181473:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_68
  · change upperValue ((point 69+point 70)/2) ≤ payment 69
    have hp : payment 69 = (1796441238905:ℝ)/1000000000000 := rfl
    have hx : (point 69+point 70)/2 = (1182419:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_69
  · change upperValue ((point 70+point 71)/2) ≤ payment 70
    have hp : payment 70 = (1786342110324:ℝ)/1000000000000 := rfl
    have hx : (point 70+point 71)/2 = (394455:ℝ)/1358848 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_70
  · change upperValue ((point 71+point 72)/2) ≤ payment 71
    have hp : payment 71 = (1776250613004:ℝ)/1000000000000 := rfl
    have hx : (point 71+point 72)/2 = (1184311:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_71
  · change upperValue ((point 72+point 73)/2) ≤ payment 72
    have hp : payment 72 = (1766166702221:ℝ)/1000000000000 := rfl
    have hx : (point 72+point 73)/2 = (1185257:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_72
  · change upperValue ((point 73+point 74)/2) ≤ payment 73
    have hp : payment 73 = (1756090333328:ℝ)/1000000000000 := rfl
    have hx : (point 73+point 74)/2 = (395401:ℝ)/1358848 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_73
  · change upperValue ((point 74+point 75)/2) ≤ payment 74
    have hp : payment 74 = (1746021461753:ℝ)/1000000000000 := rfl
    have hx : (point 74+point 75)/2 = (1187149:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_74
  · change upperValue ((point 75+point 76)/2) ≤ payment 75
    have hp : payment 75 = (1735960042999:ℝ)/1000000000000 := rfl
    have hx : (point 75+point 76)/2 = (1188095:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_75
  · change upperValue ((point 76+point 77)/2) ≤ payment 76
    have hp : payment 76 = (1725906032644:ℝ)/1000000000000 := rfl
    have hx : (point 76+point 77)/2 = (396347:ℝ)/1358848 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_76
  · change upperValue ((point 77+point 78)/2) ≤ payment 77
    have hp : payment 77 = (1715859386338:ℝ)/1000000000000 := rfl
    have hx : (point 77+point 78)/2 = (1189987:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_77
  · change upperValue ((point 78+point 79)/2) ≤ payment 78
    have hp : payment 78 = (1705820059804:ℝ)/1000000000000 := rfl
    have hx : (point 78+point 79)/2 = (1190933:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_78
  · change upperValue ((point 79+point 80)/2) ≤ payment 79
    have hp : payment 79 = (1695788008839:ℝ)/1000000000000 := rfl
    have hx : (point 79+point 80)/2 = (397293:ℝ)/1358848 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_79
  · change upperValue ((point 80+point 81)/2) ≤ payment 80
    have hp : payment 80 = (1685763189310:ℝ)/1000000000000 := rfl
    have hx : (point 80+point 81)/2 = (1192825:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_80
  · change upperValue ((point 81+point 82)/2) ≤ payment 81
    have hp : payment 81 = (1675745557155:ℝ)/1000000000000 := rfl
    have hx : (point 81+point 82)/2 = (1193771:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_81
  · change upperValue ((point 82+point 83)/2) ≤ payment 82
    have hp : payment 82 = (1665735068384:ℝ)/1000000000000 := rfl
    have hx : (point 82+point 83)/2 = (398239:ℝ)/1358848 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_82
  · change upperValue ((point 83+point 84)/2) ≤ payment 83
    have hp : payment 83 = (1655731679075:ℝ)/1000000000000 := rfl
    have hx : (point 83+point 84)/2 = (1195663:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_83
  · change upperValue ((point 84+point 85)/2) ≤ payment 84
    have hp : payment 84 = (1645735345375:ℝ)/1000000000000 := rfl
    have hx : (point 84+point 85)/2 = (1196609:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_84
  · change upperValue ((point 85+point 86)/2) ≤ payment 85
    have hp : payment 85 = (1635746023501:ℝ)/1000000000000 := rfl
    have hx : (point 85+point 86)/2 = (399185:ℝ)/1358848 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_85
  · change upperValue ((point 86+point 87)/2) ≤ payment 86
    have hp : payment 86 = (1625763669738:ℝ)/1000000000000 := rfl
    have hx : (point 86+point 87)/2 = (1198501:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_86
  · change upperValue ((point 87+point 88)/2) ≤ payment 87
    have hp : payment 87 = (1615788240435:ℝ)/1000000000000 := rfl
    have hx : (point 87+point 88)/2 = (1199447:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_87
  · change upperValue ((point 88+point 89)/2) ≤ payment 88
    have hp : payment 88 = (1605819692011:ℝ)/1000000000000 := rfl
    have hx : (point 88+point 89)/2 = (400131:ℝ)/1358848 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_88
  · change upperValue ((point 89+point 90)/2) ≤ payment 89
    have hp : payment 89 = (1595857980949:ℝ)/1000000000000 := rfl
    have hx : (point 89+point 90)/2 = (1201339:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_89
  · change upperValue ((point 90+point 91)/2) ≤ payment 90
    have hp : payment 90 = (1585903063800:ℝ)/1000000000000 := rfl
    have hx : (point 90+point 91)/2 = (1202285:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_90
  · change upperValue ((point 91+point 92)/2) ≤ payment 91
    have hp : payment 91 = (1575954897176:ℝ)/1000000000000 := rfl
    have hx : (point 91+point 92)/2 = (401077:ℝ)/1358848 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_91
  · change upperValue ((point 92+point 93)/2) ≤ payment 92
    have hp : payment 92 = (1566013437755:ℝ)/1000000000000 := rfl
    have hx : (point 92+point 93)/2 = (1204177:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_92
  · change upperValue ((point 93+point 94)/2) ≤ payment 93
    have hp : payment 93 = (1556078642280:ℝ)/1000000000000 := rfl
    have hx : (point 93+point 94)/2 = (1205123:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_93
  · change upperValue ((point 94+point 95)/2) ≤ payment 94
    have hp : payment 94 = (1546150467553:ℝ)/1000000000000 := rfl
    have hx : (point 94+point 95)/2 = (402023:ℝ)/1358848 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_94
  · change upperValue ((point 95+point 96)/2) ≤ payment 95
    have hp : payment 95 = (1536228870443:ℝ)/1000000000000 := rfl
    have hx : (point 95+point 96)/2 = (1207015:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_95
  · change upperValue ((point 96+point 97)/2) ≤ payment 96
    have hp : payment 96 = (1526313807876:ℝ)/1000000000000 := rfl
    have hx : (point 96+point 97)/2 = (1207961:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_96
  · change upperValue ((point 97+point 98)/2) ≤ payment 97
    have hp : payment 97 = (1516405236842:ℝ)/1000000000000 := rfl
    have hx : (point 97+point 98)/2 = (402969:ℝ)/1358848 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_97
  · change upperValue ((point 98+point 99)/2) ≤ payment 98
    have hp : payment 98 = (1506503114391:ℝ)/1000000000000 := rfl
    have hx : (point 98+point 99)/2 = (1209853:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_98
  · change upperValue ((point 99+point 100)/2) ≤ payment 99
    have hp : payment 99 = (1496607397632:ℝ)/1000000000000 := rfl
    have hx : (point 99+point 100)/2 = (1210799:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_99
  · change upperValue ((point 100+point 101)/2) ≤ payment 100
    have hp : payment 100 = (1486718043733:ℝ)/1000000000000 := rfl
    have hx : (point 100+point 101)/2 = (403915:ℝ)/1358848 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_100
  · change upperValue ((point 101+point 102)/2) ≤ payment 101
    have hp : payment 101 = (1476835009922:ℝ)/1000000000000 := rfl
    have hx : (point 101+point 102)/2 = (1212691:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_101
  · change upperValue ((point 102+point 103)/2) ≤ payment 102
    have hp : payment 102 = (1466958253483:ℝ)/1000000000000 := rfl
    have hx : (point 102+point 103)/2 = (1213637:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_102
  · change upperValue ((point 103+point 104)/2) ≤ payment 103
    have hp : payment 103 = (1457087731759:ℝ)/1000000000000 := rfl
    have hx : (point 103+point 104)/2 = (404861:ℝ)/1358848 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_103
  · change upperValue ((point 104+point 105)/2) ≤ payment 104
    have hp : payment 104 = (1447223402150:ℝ)/1000000000000 := rfl
    have hx : (point 104+point 105)/2 = (1215529:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_104
  · change upperValue ((point 105+point 106)/2) ≤ payment 105
    have hp : payment 105 = (1437365222109:ℝ)/1000000000000 := rfl
    have hx : (point 105+point 106)/2 = (1216475:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_105
  · change upperValue ((point 106+point 107)/2) ≤ payment 106
    have hp : payment 106 = (1427513149149:ℝ)/1000000000000 := rfl
    have hx : (point 106+point 107)/2 = (405807:ℝ)/1358848 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_106
  · change upperValue ((point 107+point 108)/2) ≤ payment 107
    have hp : payment 107 = (1417667140834:ℝ)/1000000000000 := rfl
    have hx : (point 107+point 108)/2 = (1218367:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_107
  · change upperValue ((point 108+point 109)/2) ≤ payment 108
    have hp : payment 108 = (1407827154785:ℝ)/1000000000000 := rfl
    have hx : (point 108+point 109)/2 = (1219313:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_108
  · change upperValue ((point 109+point 110)/2) ≤ payment 109
    have hp : payment 109 = (1397993148675:ℝ)/1000000000000 := rfl
    have hx : (point 109+point 110)/2 = (406753:ℝ)/1358848 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_109
  · change upperValue ((point 110+point 111)/2) ≤ payment 110
    have hp : payment 110 = (1388165080231:ℝ)/1000000000000 := rfl
    have hx : (point 110+point 111)/2 = (1221205:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_110
  · change upperValue ((point 111+point 112)/2) ≤ payment 111
    have hp : payment 111 = (1378342907233:ℝ)/1000000000000 := rfl
    have hx : (point 111+point 112)/2 = (1222151:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_111
  · change upperValue ((point 112+point 113)/2) ≤ payment 112
    have hp : payment 112 = (1368526587511:ℝ)/1000000000000 := rfl
    have hx : (point 112+point 113)/2 = (407699:ℝ)/1358848 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_112
  · change upperValue ((point 113+point 114)/2) ≤ payment 113
    have hp : payment 113 = (1358716078948:ℝ)/1000000000000 := rfl
    have hx : (point 113+point 114)/2 = (1224043:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_113
  · change upperValue ((point 114+point 115)/2) ≤ payment 114
    have hp : payment 114 = (1348911339478:ℝ)/1000000000000 := rfl
    have hx : (point 114+point 115)/2 = (1224989:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_114
  · change upperValue ((point 115+point 116)/2) ≤ payment 115
    have hp : payment 115 = (1339112327082:ℝ)/1000000000000 := rfl
    have hx : (point 115+point 116)/2 = (408645:ℝ)/1358848 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_115
  · change upperValue ((point 116+point 117)/2) ≤ payment 116
    have hp : payment 116 = (1329318999795:ℝ)/1000000000000 := rfl
    have hx : (point 116+point 117)/2 = (1226881:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_116
  · change upperValue ((point 117+point 118)/2) ≤ payment 117
    have hp : payment 117 = (1319531315697:ℝ)/1000000000000 := rfl
    have hx : (point 117+point 118)/2 = (1227827:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_117
  · change upperValue ((point 118+point 119)/2) ≤ payment 118
    have hp : payment 118 = (1309749232920:ℝ)/1000000000000 := rfl
    have hx : (point 118+point 119)/2 = (409591:ℝ)/1358848 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_118
  · change upperValue ((point 119+point 120)/2) ≤ payment 119
    have hp : payment 119 = (1299972709639:ℝ)/1000000000000 := rfl
    have hx : (point 119+point 120)/2 = (1229719:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_119
  · change upperValue ((point 120+point 121)/2) ≤ payment 120
    have hp : payment 120 = (1290201704081:ℝ)/1000000000000 := rfl
    have hx : (point 120+point 121)/2 = (1230665:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_120
  · change upperValue ((point 121+point 122)/2) ≤ payment 121
    have hp : payment 121 = (1280436174516:ℝ)/1000000000000 := rfl
    have hx : (point 121+point 122)/2 = (410537:ℝ)/1358848 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_121
  · change upperValue ((point 122+point 123)/2) ≤ payment 122
    have hp : payment 122 = (1270676079261:ℝ)/1000000000000 := rfl
    have hx : (point 122+point 123)/2 = (1232557:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_122
  · change upperValue ((point 123+point 124)/2) ≤ payment 123
    have hp : payment 123 = (1260921376679:ℝ)/1000000000000 := rfl
    have hx : (point 123+point 124)/2 = (1233503:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_123
  · change upperValue ((point 124+point 125)/2) ≤ payment 124
    have hp : payment 124 = (1251172025178:ℝ)/1000000000000 := rfl
    have hx : (point 124+point 125)/2 = (411483:ℝ)/1358848 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_124
  · change upperValue ((point 125+point 126)/2) ≤ payment 125
    have hp : payment 125 = (1241427983208:ℝ)/1000000000000 := rfl
    have hx : (point 125+point 126)/2 = (1235395:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_125
  · change upperValue ((point 126+point 127)/2) ≤ payment 126
    have hp : payment 126 = (1231689209265:ℝ)/1000000000000 := rfl
    have hx : (point 126+point 127)/2 = (1236341:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_126
  · change upperValue ((point 127+point 128)/2) ≤ payment 127
    have hp : payment 127 = (1221955661886:ℝ)/1000000000000 := rfl
    have hx : (point 127+point 128)/2 = (412429:ℝ)/1358848 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_127
  · change upperValue ((point 128+point 129)/2) ≤ payment 128
    have hp : payment 128 = (1212227299651:ℝ)/1000000000000 := rfl
    have hx : (point 128+point 129)/2 = (1238233:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_128
  · change upperValue ((point 129+point 130)/2) ≤ payment 129
    have hp : payment 129 = (1202504081183:ℝ)/1000000000000 := rfl
    have hx : (point 129+point 130)/2 = (1239179:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_129
  · change upperValue ((point 130+point 131)/2) ≤ payment 130
    have hp : payment 130 = (1192785965144:ℝ)/1000000000000 := rfl
    have hx : (point 130+point 131)/2 = (413375:ℝ)/1358848 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_130
  · change upperValue ((point 131+point 132)/2) ≤ payment 131
    have hp : payment 131 = (1183072910239:ℝ)/1000000000000 := rfl
    have hx : (point 131+point 132)/2 = (1241071:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_131
  · change upperValue ((point 132+point 133)/2) ≤ payment 132
    have hp : payment 132 = (1173364875210:ℝ)/1000000000000 := rfl
    have hx : (point 132+point 133)/2 = (1242017:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_132
  · change upperValue ((point 133+point 134)/2) ≤ payment 133
    have hp : payment 133 = (1163661818841:ℝ)/1000000000000 := rfl
    have hx : (point 133+point 134)/2 = (414321:ℝ)/1358848 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_133
  · change upperValue ((point 134+point 135)/2) ≤ payment 134
    have hp : payment 134 = (1153963699955:ℝ)/1000000000000 := rfl
    have hx : (point 134+point 135)/2 = (1243909:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_134
  · change upperValue ((point 135+point 136)/2) ≤ payment 135
    have hp : payment 135 = (1144270477410:ℝ)/1000000000000 := rfl
    have hx : (point 135+point 136)/2 = (1244855:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_135
  · change upperValue ((point 136+point 137)/2) ≤ payment 136
    have hp : payment 136 = (1134582110106:ℝ)/1000000000000 := rfl
    have hx : (point 136+point 137)/2 = (415267:ℝ)/1358848 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_136
  · change upperValue ((point 137+point 138)/2) ≤ payment 137
    have hp : payment 137 = (1124898556975:ℝ)/1000000000000 := rfl
    have hx : (point 137+point 138)/2 = (1246747:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_137
  · change upperValue ((point 138+point 139)/2) ≤ payment 138
    have hp : payment 138 = (1115219776991:ℝ)/1000000000000 := rfl
    have hx : (point 138+point 139)/2 = (1247693:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_138
  · change upperValue ((point 139+point 140)/2) ≤ payment 139
    have hp : payment 139 = (1105545729160:ℝ)/1000000000000 := rfl
    have hx : (point 139+point 140)/2 = (416213:ℝ)/1358848 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_139
  · change upperValue ((point 140+point 141)/2) ≤ payment 140
    have hp : payment 140 = (1095876372523:ℝ)/1000000000000 := rfl
    have hx : (point 140+point 141)/2 = (1249585:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_140
  · change upperValue ((point 141+point 142)/2) ≤ payment 141
    have hp : payment 141 = (1086211666160:ℝ)/1000000000000 := rfl
    have hx : (point 141+point 142)/2 = (1250531:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_141
  · change upperValue ((point 142+point 143)/2) ≤ payment 142
    have hp : payment 142 = (1076551569180:ℝ)/1000000000000 := rfl
    have hx : (point 142+point 143)/2 = (417159:ℝ)/1358848 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_142
  · change upperValue ((point 143+point 144)/2) ≤ payment 143
    have hp : payment 143 = (1066896040728:ℝ)/1000000000000 := rfl
    have hx : (point 143+point 144)/2 = (1252423:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_143
  · change upperValue ((point 144+point 145)/2) ≤ payment 144
    have hp : payment 144 = (1057245039982:ℝ)/1000000000000 := rfl
    have hx : (point 144+point 145)/2 = (1253369:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_144
  · change upperValue ((point 145+point 146)/2) ≤ payment 145
    have hp : payment 145 = (1047598526152:ℝ)/1000000000000 := rfl
    have hx : (point 145+point 146)/2 = (418105:ℝ)/1358848 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_145
  · change upperValue ((point 146+point 147)/2) ≤ payment 146
    have hp : payment 146 = (1037956458479:ℝ)/1000000000000 := rfl
    have hx : (point 146+point 147)/2 = (1255261:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_146
  · change upperValue ((point 147+point 148)/2) ≤ payment 147
    have hp : payment 147 = (1028318796237:ℝ)/1000000000000 := rfl
    have hx : (point 147+point 148)/2 = (1256207:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_147
  · change upperValue ((point 148+point 149)/2) ≤ payment 148
    have hp : payment 148 = (1018685498728:ℝ)/1000000000000 := rfl
    have hx : (point 148+point 149)/2 = (419051:ℝ)/1358848 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_148
  · change upperValue ((point 149+point 150)/2) ≤ payment 149
    have hp : payment 149 = (1009056525287:ℝ)/1000000000000 := rfl
    have hx : (point 149+point 150)/2 = (1258099:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_149
  · change upperValue ((point 150+point 151)/2) ≤ payment 150
    have hp : payment 150 = (999431835276:ℝ)/1000000000000 := rfl
    have hx : (point 150+point 151)/2 = (1259045:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_150
  · change upperValue ((point 151+point 152)/2) ≤ payment 151
    have hp : payment 151 = (989811388087:ℝ)/1000000000000 := rfl
    have hx : (point 151+point 152)/2 = (419997:ℝ)/1358848 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_151
  · change upperValue ((point 152+point 153)/2) ≤ payment 152
    have hp : payment 152 = (980195143140:ℝ)/1000000000000 := rfl
    have hx : (point 152+point 153)/2 = (1260937:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_152
  · change upperValue ((point 153+point 154)/2) ≤ payment 153
    have hp : payment 153 = (970583059882:ℝ)/1000000000000 := rfl
    have hx : (point 153+point 154)/2 = (1261883:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_153
  · change upperValue ((point 154+point 155)/2) ≤ payment 154
    have hp : payment 154 = (960975097787:ℝ)/1000000000000 := rfl
    have hx : (point 154+point 155)/2 = (420943:ℝ)/1358848 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_154
  · change upperValue ((point 155+point 156)/2) ≤ payment 155
    have hp : payment 155 = (951371216357:ℝ)/1000000000000 := rfl
    have hx : (point 155+point 156)/2 = (1263775:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_155
  · change upperValue ((point 156+point 157)/2) ≤ payment 156
    have hp : payment 156 = (941771375120:ℝ)/1000000000000 := rfl
    have hx : (point 156+point 157)/2 = (1264721:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_156
  · change upperValue ((point 157+point 158)/2) ≤ payment 157
    have hp : payment 157 = (932175533626:ℝ)/1000000000000 := rfl
    have hx : (point 157+point 158)/2 = (421889:ℝ)/1358848 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_157
  · change upperValue ((point 158+point 159)/2) ≤ payment 158
    have hp : payment 158 = (922583651453:ℝ)/1000000000000 := rfl
    have hx : (point 158+point 159)/2 = (1266613:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_158
  · change upperValue ((point 159+point 160)/2) ≤ payment 159
    have hp : payment 159 = (912995688202:ℝ)/1000000000000 := rfl
    have hx : (point 159+point 160)/2 = (1267559:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_159
  · change upperValue ((point 160+point 161)/2) ≤ payment 160
    have hp : payment 160 = (903411603497:ℝ)/1000000000000 := rfl
    have hx : (point 160+point 161)/2 = (422835:ℝ)/1358848 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_160
  · change upperValue ((point 161+point 162)/2) ≤ payment 161
    have hp : payment 161 = (893831356987:ℝ)/1000000000000 := rfl
    have hx : (point 161+point 162)/2 = (1269451:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_161
  · change upperValue ((point 162+point 163)/2) ≤ payment 162
    have hp : payment 162 = (884254908341:ℝ)/1000000000000 := rfl
    have hx : (point 162+point 163)/2 = (1270397:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_162
  · change upperValue ((point 163+point 164)/2) ≤ payment 163
    have hp : payment 163 = (874682217250:ℝ)/1000000000000 := rfl
    have hx : (point 163+point 164)/2 = (423781:ℝ)/1358848 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_163
  · change upperValue ((point 164+point 165)/2) ≤ payment 164
    have hp : payment 164 = (865113243428:ℝ)/1000000000000 := rfl
    have hx : (point 164+point 165)/2 = (1272289:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_164
  · change upperValue ((point 165+point 166)/2) ≤ payment 165
    have hp : payment 165 = (855547946608:ℝ)/1000000000000 := rfl
    have hx : (point 165+point 166)/2 = (1273235:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_165
  · change upperValue ((point 166+point 167)/2) ≤ payment 166
    have hp : payment 166 = (845986286543:ℝ)/1000000000000 := rfl
    have hx : (point 166+point 167)/2 = (424727:ℝ)/1358848 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_166
  · change upperValue ((point 167+point 168)/2) ≤ payment 167
    have hp : payment 167 = (836428223007:ℝ)/1000000000000 := rfl
    have hx : (point 167+point 168)/2 = (1275127:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_167
  · change upperValue ((point 168+point 169)/2) ≤ payment 168
    have hp : payment 168 = (826873715790:ℝ)/1000000000000 := rfl
    have hx : (point 168+point 169)/2 = (1276073:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_168
  · change upperValue ((point 169+point 170)/2) ≤ payment 169
    have hp : payment 169 = (817322724703:ℝ)/1000000000000 := rfl
    have hx : (point 169+point 170)/2 = (425673:ℝ)/1358848 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_169
  · change upperValue ((point 170+point 171)/2) ≤ payment 170
    have hp : payment 170 = (807775209573:ℝ)/1000000000000 := rfl
    have hx : (point 170+point 171)/2 = (1277965:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_170
  · change upperValue ((point 171+point 172)/2) ≤ payment 171
    have hp : payment 171 = (798231130245:ℝ)/1000000000000 := rfl
    have hx : (point 171+point 172)/2 = (1278911:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_171
  · change upperValue ((point 172+point 173)/2) ≤ payment 172
    have hp : payment 172 = (788690446580:ℝ)/1000000000000 := rfl
    have hx : (point 172+point 173)/2 = (426619:ℝ)/1358848 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_172
  · change upperValue ((point 173+point 174)/2) ≤ payment 173
    have hp : payment 173 = (779153118455:ℝ)/1000000000000 := rfl
    have hx : (point 173+point 174)/2 = (1280803:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_173
  · change upperValue ((point 174+point 175)/2) ≤ payment 174
    have hp : payment 174 = (769619105762:ℝ)/1000000000000 := rfl
    have hx : (point 174+point 175)/2 = (1281749:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_174
  · change upperValue ((point 175+point 176)/2) ≤ payment 175
    have hp : payment 175 = (760088368407:ℝ)/1000000000000 := rfl
    have hx : (point 175+point 176)/2 = (427565:ℝ)/1358848 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_175
  · change upperValue ((point 176+point 177)/2) ≤ payment 176
    have hp : payment 176 = (750560866313:ℝ)/1000000000000 := rfl
    have hx : (point 176+point 177)/2 = (1283641:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_176
  · change upperValue ((point 177+point 178)/2) ≤ payment 177
    have hp : payment 177 = (741036559413:ℝ)/1000000000000 := rfl
    have hx : (point 177+point 178)/2 = (1284587:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_177
  · change upperValue ((point 178+point 179)/2) ≤ payment 178
    have hp : payment 178 = (731515407655:ℝ)/1000000000000 := rfl
    have hx : (point 178+point 179)/2 = (428511:ℝ)/1358848 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_178
  · change upperValue ((point 179+point 180)/2) ≤ payment 179
    have hp : payment 179 = (721997370998:ℝ)/1000000000000 := rfl
    have hx : (point 179+point 180)/2 = (1286479:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_179
  · change upperValue ((point 180+point 181)/2) ≤ payment 180
    have hp : payment 180 = (712482409414:ℝ)/1000000000000 := rfl
    have hx : (point 180+point 181)/2 = (1287425:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_180
  · change upperValue ((point 181+point 182)/2) ≤ payment 181
    have hp : payment 181 = (702970482885:ℝ)/1000000000000 := rfl
    have hx : (point 181+point 182)/2 = (429457:ℝ)/1358848 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_181
  · change upperValue ((point 182+point 183)/2) ≤ payment 182
    have hp : payment 182 = (693461551405:ℝ)/1000000000000 := rfl
    have hx : (point 182+point 183)/2 = (1289317:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_182
  · change upperValue ((point 183+point 184)/2) ≤ payment 183
    have hp : payment 183 = (683955574976:ℝ)/1000000000000 := rfl
    have hx : (point 183+point 184)/2 = (1290263:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_183
  · change upperValue ((point 184+point 185)/2) ≤ payment 184
    have hp : payment 184 = (674452513610:ℝ)/1000000000000 := rfl
    have hx : (point 184+point 185)/2 = (430403:ℝ)/1358848 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_184
  · change upperValue ((point 185+point 186)/2) ≤ payment 185
    have hp : payment 185 = (664952327329:ℝ)/1000000000000 := rfl
    have hx : (point 185+point 186)/2 = (1292155:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_185
  · change upperValue ((point 186+point 187)/2) ≤ payment 186
    have hp : payment 186 = (655454976162:ℝ)/1000000000000 := rfl
    have hx : (point 186+point 187)/2 = (1293101:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_186
  · change upperValue ((point 187+point 188)/2) ≤ payment 187
    have hp : payment 187 = (645960420146:ℝ)/1000000000000 := rfl
    have hx : (point 187+point 188)/2 = (431349:ℝ)/1358848 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_187
  · change upperValue ((point 188+point 189)/2) ≤ payment 188
    have hp : payment 188 = (636468619323:ℝ)/1000000000000 := rfl
    have hx : (point 188+point 189)/2 = (1294993:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_188
  · change upperValue ((point 189+point 190)/2) ≤ payment 189
    have hp : payment 189 = (626979533745:ℝ)/1000000000000 := rfl
    have hx : (point 189+point 190)/2 = (1295939:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_189
  · change upperValue ((point 190+point 191)/2) ≤ payment 190
    have hp : payment 190 = (617493123466:ℝ)/1000000000000 := rfl
    have hx : (point 190+point 191)/2 = (432295:ℝ)/1358848 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_190
  · change upperValue ((point 191+point 192)/2) ≤ payment 191
    have hp : payment 191 = (608009348547:ℝ)/1000000000000 := rfl
    have hx : (point 191+point 192)/2 = (1297831:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_191
  · change upperValue ((point 192+point 193)/2) ≤ payment 192
    have hp : payment 192 = (598528169055:ℝ)/1000000000000 := rfl
    have hx : (point 192+point 193)/2 = (1298777:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_192
  · change upperValue ((point 193+point 194)/2) ≤ payment 193
    have hp : payment 193 = (589049545057:ℝ)/1000000000000 := rfl
    have hx : (point 193+point 194)/2 = (433241:ℝ)/1358848 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_193
  · change upperValue ((point 194+point 195)/2) ≤ payment 194
    have hp : payment 194 = (579573436627:ℝ)/1000000000000 := rfl
    have hx : (point 194+point 195)/2 = (1300669:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_194
  · change upperValue ((point 195+point 196)/2) ≤ payment 195
    have hp : payment 195 = (570099803839:ℝ)/1000000000000 := rfl
    have hx : (point 195+point 196)/2 = (1301615:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_195
  · change upperValue ((point 196+point 197)/2) ≤ payment 196
    have hp : payment 196 = (560628606772:ℝ)/1000000000000 := rfl
    have hx : (point 196+point 197)/2 = (434187:ℝ)/1358848 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_196
  · change upperValue ((point 197+point 198)/2) ≤ payment 197
    have hp : payment 197 = (551159805504:ℝ)/1000000000000 := rfl
    have hx : (point 197+point 198)/2 = (1303507:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_197
  · change upperValue ((point 198+point 199)/2) ≤ payment 198
    have hp : payment 198 = (541693360114:ℝ)/1000000000000 := rfl
    have hx : (point 198+point 199)/2 = (1304453:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_198
  · change upperValue ((point 199+point 200)/2) ≤ payment 199
    have hp : payment 199 = (532229230682:ℝ)/1000000000000 := rfl
    have hx : (point 199+point 200)/2 = (435133:ℝ)/1358848 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_199
  · change upperValue ((point 200+point 201)/2) ≤ payment 200
    have hp : payment 200 = (522767377289:ℝ)/1000000000000 := rfl
    have hx : (point 200+point 201)/2 = (1306345:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_200
  · change upperValue ((point 201+point 202)/2) ≤ payment 201
    have hp : payment 201 = (513307760013:ℝ)/1000000000000 := rfl
    have hx : (point 201+point 202)/2 = (1307291:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_201
  · change upperValue ((point 202+point 203)/2) ≤ payment 202
    have hp : payment 202 = (503850338931:ℝ)/1000000000000 := rfl
    have hx : (point 202+point 203)/2 = (436079:ℝ)/1358848 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_202
  · change upperValue ((point 203+point 204)/2) ≤ payment 203
    have hp : payment 203 = (494395074118:ℝ)/1000000000000 := rfl
    have hx : (point 203+point 204)/2 = (1309183:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_203
  · change upperValue ((point 204+point 205)/2) ≤ payment 204
    have hp : payment 204 = (484941925645:ℝ)/1000000000000 := rfl
    have hx : (point 204+point 205)/2 = (1310129:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_204
  · change upperValue ((point 205+point 206)/2) ≤ payment 205
    have hp : payment 205 = (475490853583:ℝ)/1000000000000 := rfl
    have hx : (point 205+point 206)/2 = (437025:ℝ)/1358848 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_205
  · change upperValue ((point 206+point 207)/2) ≤ payment 206
    have hp : payment 206 = (466041817994:ℝ)/1000000000000 := rfl
    have hx : (point 206+point 207)/2 = (1312021:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_206
  · change upperValue ((point 207+point 208)/2) ≤ payment 207
    have hp : payment 207 = (456594778940:ℝ)/1000000000000 := rfl
    have hx : (point 207+point 208)/2 = (1312967:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_207
  · change upperValue ((point 208+point 209)/2) ≤ payment 208
    have hp : payment 208 = (447149696476:ℝ)/1000000000000 := rfl
    have hx : (point 208+point 209)/2 = (437971:ℝ)/1358848 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_208
  · change upperValue ((point 209+point 210)/2) ≤ payment 209
    have hp : payment 209 = (437706530649:ℝ)/1000000000000 := rfl
    have hx : (point 209+point 210)/2 = (1314859:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_209
  · change upperValue ((point 210+point 211)/2) ≤ payment 210
    have hp : payment 210 = (428265241502:ℝ)/1000000000000 := rfl
    have hx : (point 210+point 211)/2 = (1315805:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_210
  · change upperValue ((point 211+point 212)/2) ≤ payment 211
    have hp : payment 211 = (418825789072:ℝ)/1000000000000 := rfl
    have hx : (point 211+point 212)/2 = (438917:ℝ)/1358848 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_211
  · change upperValue ((point 212+point 213)/2) ≤ payment 212
    have hp : payment 212 = (409388133384:ℝ)/1000000000000 := rfl
    have hx : (point 212+point 213)/2 = (1317697:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_212
  · change upperValue ((point 213+point 214)/2) ≤ payment 213
    have hp : payment 213 = (399952234458:ℝ)/1000000000000 := rfl
    have hx : (point 213+point 214)/2 = (1318643:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_213
  · change upperValue ((point 214+point 215)/2) ≤ payment 214
    have hp : payment 214 = (390518052304:ℝ)/1000000000000 := rfl
    have hx : (point 214+point 215)/2 = (439863:ℝ)/1358848 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_214
  · change upperValue ((point 215+point 216)/2) ≤ payment 215
    have hp : payment 215 = (381085546922:ℝ)/1000000000000 := rfl
    have hx : (point 215+point 216)/2 = (1320535:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_215
  · change upperValue ((point 216+point 217)/2) ≤ payment 216
    have hp : payment 216 = (371654678303:ℝ)/1000000000000 := rfl
    have hx : (point 216+point 217)/2 = (1321481:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_216
  · change upperValue ((point 217+point 218)/2) ≤ payment 217
    have hp : payment 217 = (362225406425:ℝ)/1000000000000 := rfl
    have hx : (point 217+point 218)/2 = (440809:ℝ)/1358848 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_217
  · change upperValue ((point 218+point 219)/2) ≤ payment 218
    have hp : payment 218 = (352797691257:ℝ)/1000000000000 := rfl
    have hx : (point 218+point 219)/2 = (1323373:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_218
  · change upperValue ((point 219+point 220)/2) ≤ payment 219
    have hp : payment 219 = (343371492753:ℝ)/1000000000000 := rfl
    have hx : (point 219+point 220)/2 = (1324319:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_219
  · change upperValue ((point 220+point 221)/2) ≤ payment 220
    have hp : payment 220 = (333946770857:ℝ)/1000000000000 := rfl
    have hx : (point 220+point 221)/2 = (441755:ℝ)/1358848 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_220
  · change upperValue ((point 221+point 222)/2) ≤ payment 221
    have hp : payment 221 = (324523485497:ℝ)/1000000000000 := rfl
    have hx : (point 221+point 222)/2 = (1326211:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_221
  · change upperValue ((point 222+point 223)/2) ≤ payment 222
    have hp : payment 222 = (315101596588:ℝ)/1000000000000 := rfl
    have hx : (point 222+point 223)/2 = (1327157:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_222
  · change upperValue ((point 223+point 224)/2) ≤ payment 223
    have hp : payment 223 = (305681064032:ℝ)/1000000000000 := rfl
    have hx : (point 223+point 224)/2 = (442701:ℝ)/1358848 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_223
  · change upperValue ((point 224+point 225)/2) ≤ payment 224
    have hp : payment 224 = (296261847712:ℝ)/1000000000000 := rfl
    have hx : (point 224+point 225)/2 = (1329049:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_224
  · change upperValue ((point 225+point 226)/2) ≤ payment 225
    have hp : payment 225 = (286843907498:ℝ)/1000000000000 := rfl
    have hx : (point 225+point 226)/2 = (1329995:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_225
  · change upperValue ((point 226+point 227)/2) ≤ payment 226
    have hp : payment 226 = (277427203242:ℝ)/1000000000000 := rfl
    have hx : (point 226+point 227)/2 = (443647:ℝ)/1358848 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_226
  · change upperValue ((point 227+point 228)/2) ≤ payment 227
    have hp : payment 227 = (268011694778:ℝ)/1000000000000 := rfl
    have hx : (point 227+point 228)/2 = (1331887:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_227
  · change upperValue ((point 228+point 229)/2) ≤ payment 228
    have hp : payment 228 = (258597341925:ℝ)/1000000000000 := rfl
    have hx : (point 228+point 229)/2 = (1332833:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_228
  · change upperValue ((point 229+point 230)/2) ≤ payment 229
    have hp : payment 229 = (249184104480:ℝ)/1000000000000 := rfl
    have hx : (point 229+point 230)/2 = (444593:ℝ)/1358848 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_229
  · change upperValue ((point 230+point 231)/2) ≤ payment 230
    have hp : payment 230 = (239771942221:ℝ)/1000000000000 := rfl
    have hx : (point 230+point 231)/2 = (1334725:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_230
  · change upperValue ((point 231+point 232)/2) ≤ payment 231
    have hp : payment 231 = (230360814910:ℝ)/1000000000000 := rfl
    have hx : (point 231+point 232)/2 = (1335671:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_231
  · change upperValue ((point 232+point 233)/2) ≤ payment 232
    have hp : payment 232 = (220950682283:ℝ)/1000000000000 := rfl
    have hx : (point 232+point 233)/2 = (445539:ℝ)/1358848 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_232
  · change upperValue ((point 233+point 234)/2) ≤ payment 233
    have hp : payment 233 = (211541504058:ℝ)/1000000000000 := rfl
    have hx : (point 233+point 234)/2 = (1337563:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_233
  · change upperValue ((point 234+point 235)/2) ≤ payment 234
    have hp : payment 234 = (202133239931:ℝ)/1000000000000 := rfl
    have hx : (point 234+point 235)/2 = (1338509:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_234
  · change upperValue ((point 235+point 236)/2) ≤ payment 235
    have hp : payment 235 = (192725849574:ℝ)/1000000000000 := rfl
    have hx : (point 235+point 236)/2 = (446485:ℝ)/1358848 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_235
  · change upperValue ((point 236+point 237)/2) ≤ payment 236
    have hp : payment 236 = (183319292637:ℝ)/1000000000000 := rfl
    have hx : (point 236+point 237)/2 = (1340401:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_236
  · change upperValue ((point 237+point 238)/2) ≤ payment 237
    have hp : payment 237 = (173913528745:ℝ)/1000000000000 := rfl
    have hx : (point 237+point 238)/2 = (1341347:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_237
  · change upperValue ((point 238+point 239)/2) ≤ payment 238
    have hp : payment 238 = (164508517501:ℝ)/1000000000000 := rfl
    have hx : (point 238+point 239)/2 = (447431:ℝ)/1358848 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_238
  · change upperValue ((point 239+point 240)/2) ≤ payment 239
    have hp : payment 239 = (155104218478:ℝ)/1000000000000 := rfl
    have hx : (point 239+point 240)/2 = (1343239:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_239
  · change upperValue ((point 240+point 241)/2) ≤ payment 240
    have hp : payment 240 = (145700591229:ℝ)/1000000000000 := rfl
    have hx : (point 240+point 241)/2 = (1344185:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_240
  · change upperValue ((point 241+point 242)/2) ≤ payment 241
    have hp : payment 241 = (136297595275:ℝ)/1000000000000 := rfl
    have hx : (point 241+point 242)/2 = (448377:ℝ)/1358848 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_241
  · change upperValue ((point 242+point 243)/2) ≤ payment 242
    have hp : payment 242 = (126895190113:ℝ)/1000000000000 := rfl
    have hx : (point 242+point 243)/2 = (1346077:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_242
  · change upperValue ((point 243+point 244)/2) ≤ payment 243
    have hp : payment 243 = (117493335211:ℝ)/1000000000000 := rfl
    have hx : (point 243+point 244)/2 = (1347023:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_243
  · change upperValue ((point 244+point 245)/2) ≤ payment 244
    have hp : payment 244 = (108091990009:ℝ)/1000000000000 := rfl
    have hx : (point 244+point 245)/2 = (449323:ℝ)/1358848 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_244
  · change upperValue ((point 245+point 246)/2) ≤ payment 245
    have hp : payment 245 = (98691113916:ℝ)/1000000000000 := rfl
    have hx : (point 245+point 246)/2 = (1348915:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_245
  · change upperValue ((point 246+point 247)/2) ≤ payment 246
    have hp : payment 246 = (89290666314:ℝ)/1000000000000 := rfl
    have hx : (point 246+point 247)/2 = (1349861:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_246
  · change upperValue ((point 247+point 248)/2) ≤ payment 247
    have hp : payment 247 = (79890606551:ℝ)/1000000000000 := rfl
    have hx : (point 247+point 248)/2 = (450269:ℝ)/1358848 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_247
  · change upperValue ((point 248+point 249)/2) ≤ payment 248
    have hp : payment 248 = (70490893946:ℝ)/1000000000000 := rfl
    have hx : (point 248+point 249)/2 = (1351753:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_248
  · change upperValue ((point 249+point 250)/2) ≤ payment 249
    have hp : payment 249 = (61091487785:ℝ)/1000000000000 := rfl
    have hx : (point 249+point 250)/2 = (1352699:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_249
  · change upperValue ((point 250+point 251)/2) ≤ payment 250
    have hp : payment 250 = (51692347321:ℝ)/1000000000000 := rfl
    have hx : (point 250+point 251)/2 = (451215:ℝ)/1358848 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_250
  · change upperValue ((point 251+point 252)/2) ≤ payment 251
    have hp : payment 251 = (42293431774:ℝ)/1000000000000 := rfl
    have hx : (point 251+point 252)/2 = (1354591:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_251
  · change upperValue ((point 252+point 253)/2) ≤ payment 252
    have hp : payment 252 = (32894700329:ℝ)/1000000000000 := rfl
    have hx : (point 252+point 253)/2 = (1355537:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_252
  · change upperValue ((point 253+point 254)/2) ≤ payment 253
    have hp : payment 253 = (23496112138:ℝ)/1000000000000 := rfl
    have hx : (point 253+point 254)/2 = (452161:ℝ)/1358848 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_253
  · change upperValue ((point 254+point 255)/2) ≤ payment 254
    have hp : payment 254 = (14097626316:ℝ)/1000000000000 := rfl
    have hx : (point 254+point 255)/2 = (1357429:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_254
  · change upperValue ((point 255+point 256)/2) ≤ payment 255
    have hp : payment 255 = (4699201942:ℝ)/1000000000000 := rfl
    have hx : (point 255+point 256)/2 = (1358375:ℝ)/4076544 := by
      norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_upper_255

theorem seventh_main_upper : Wu08TerminalAlignment.seventhMain ≤ (29259:ℝ)/50000 := by
  have h := uniform_upper payment (fun i hi => payments_paid ⟨i,hi⟩)
  apply h.trans
  simp only [payment,← sum_div,← Nat.cast_sum,numerator_sum]
  norm_num [step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]

end WuPaper.ClassicalSeventh
#print axioms WuPaper.ClassicalSeventh.seventh_main_upper
