import WR2ClassicalNinthPoints00
import WR2ClassicalNinthPoints01
import WR2ClassicalNinthPoints02
import WR2ClassicalNinthPoints03
import WR2ClassicalNinthPoints04
import WR2ClassicalNinthPoints05
import WR2ClassicalNinthPoints06
import WR2ClassicalNinthPoints07
import WR2ClassicalNinthPoints08
import WR2ClassicalNinthPoints09
import WR2ClassicalNinthPoints10
import WR2ClassicalNinthPoints11
import WR2ClassicalNinthPoints12
import WR2ClassicalNinthPoints13
import WR2ClassicalNinthPoints14
import WR2ClassicalNinthPoints15
import WR2ClassicalNinthPoints16
import WR2ClassicalNinthPoints17
import WR2ClassicalNinthPoints18
import WR2ClassicalNinthPoints19
import WR2ClassicalNinthPoints20
import WR2ClassicalNinthPoints21
import WR2ClassicalNinthPoints22
import WR2ClassicalNinthPoints23
import WR2ClassicalNinthPoints24
import WR2ClassicalNinthPoints25
import WR2ClassicalNinthPoints26
import WR2ClassicalNinthPoints27
import WR2ClassicalNinthPoints28
import WR2ClassicalNinthPoints29
import WR2ClassicalNinthPoints30
import WR2ClassicalNinthPoints31
noncomputable section
namespace WuPaper.ClassicalNinth
open Finset
def numerator : ℕ → ℕ
  | 0 => 7416360053360
  | 1 => 7396118378787
  | 2 => 7375971809833
  | 3 => 7355919645923
  | 4 => 7335961193279
  | 5 => 7316095764831
  | 6 => 7296322680142
  | 7 => 7276641265325
  | 8 => 7257050852965
  | 9 => 7237550782041
  | 10 => 7218140397850
  | 11 => 7198819051932
  | 12 => 7179586101992
  | 13 => 7160440911831
  | 14 => 7141382851275
  | 15 => 7122411296096
  | 16 => 7103525627950
  | 17 => 7084725234304
  | 18 => 7066009508367
  | 19 => 7047377849025
  | 20 => 7028829660774
  | 21 => 7010364353652
  | 22 => 6991981343179
  | 23 => 6973680050290
  | 24 => 6955459901271
  | 25 => 6937320327703
  | 26 => 6919260766396
  | 27 => 6901280659328
  | 28 => 6883379453590
  | 29 => 6865556601326
  | 30 => 6847811559671
  | 31 => 6830143790701
  | 32 => 6812552761373
  | 33 => 6795037943467
  | 34 => 6777598813538
  | 35 => 6760234852857
  | 36 => 6742945547358
  | 37 => 6725730387589
  | 38 => 6708588868657
  | 39 => 6691520490178
  | 40 => 6674524756226
  | 41 => 6657601175285
  | 42 => 6640749260199
  | 43 => 6623968528122
  | 44 => 6607258500474
  | 45 => 6590618702888
  | 46 => 6574048665172
  | 47 => 6557547921254
  | 48 => 6541116009143
  | 49 => 6524752470883
  | 50 => 6508456852506
  | 51 => 6492228703993
  | 52 => 6476067579227
  | 53 => 6459973035954
  | 54 => 6443944635738
  | 55 => 6427981943922
  | 56 => 6412084529586
  | 57 => 6396251965508
  | 58 => 6380483828124
  | 59 => 6364779697486
  | 60 => 6349139157228
  | 61 => 6333561794525
  | 62 => 6318047200055
  | 63 => 6302594967962
  | 64 => 6287204695822
  | 65 => 6271875984601
  | 66 => 6256608438625
  | 67 => 6241401665542
  | 68 => 6226255276287
  | 69 => 6211168885047
  | 70 => 6196142109228
  | 71 => 6181174569422
  | 72 => 6166265889371
  | 73 => 6151415695938
  | 74 => 6136623619071
  | 75 => 6121889291774
  | 76 => 6107212350072
  | 77 => 6092592432984
  | 78 => 6078029182489
  | 79 => 6063522243496
  | 80 => 6049071263816
  | 81 => 6034675894128
  | 82 => 6020335787956
  | 83 => 6006050601635
  | 84 => 5991819994282
  | 85 => 5977643627772
  | 86 => 5963521166706
  | 87 => 5949452278388
  | 88 => 5935436632790
  | 89 => 5921473902534
  | 90 => 5907563762859
  | 91 => 5893705891598
  | 92 => 5879899969151
  | 93 => 5866145678458
  | 94 => 5852442704978
  | 95 => 5838790736657
  | 96 => 5825189463911
  | 97 => 5811638579594
  | 98 => 5798137778981
  | 99 => 5784686759739
  | 100 => 5771285221904
  | 101 => 5757932867862
  | 102 => 5744629402320
  | 103 => 5731374532287
  | 104 => 5718167967049
  | 105 => 5705009418151
  | 106 => 5691898599370
  | 107 => 5678835226696
  | 108 => 5665819018310
  | 109 => 5652849694564
  | 110 => 5639926977957
  | 111 => 5627050593117
  | 112 => 5614220266779
  | 113 => 5601435727766
  | 114 => 5588696706968
  | 115 => 5576002937323
  | 116 => 5563354153796
  | 117 => 5550750093360
  | 118 => 5538190494980
  | 119 => 5525675099589
  | 120 => 5513203650073
  | 121 => 5500775891251
  | 122 => 5488391569857
  | 123 => 5476050434522
  | 124 => 5463752235756
  | 125 => 5451496725932
  | 126 => 5439283659264
  | 127 => 5427112791796
  | 128 => 5414983881379
  | 129 => 5402896687658
  | 130 => 5390850972055
  | 131 => 5378846497750
  | 132 => 5366883029666
  | 133 => 5354960334454
  | 134 => 5343078180477
  | 135 => 5331236337791
  | 136 => 5319434578135
  | 137 => 5307672674908
  | 138 => 5295950403162
  | 139 => 5284267539581
  | 140 => 5272623862467
  | 141 => 5261019151729
  | 142 => 5249453188862
  | 143 => 5237925756939
  | 144 => 5226436640593
  | 145 => 5214985626003
  | 146 => 5203572500882
  | 147 => 5192197054459
  | 148 => 5180859077471
  | 149 => 5169558362146
  | 150 => 5158294702189
  | 151 => 5147067892771
  | 152 => 5135877730515
  | 153 => 5124724013481
  | 154 => 5113606541158
  | 155 => 5102525114445
  | 156 => 5091479535644
  | 157 => 5080469608444
  | 158 => 5069495137912
  | 159 => 5058555930476
  | 160 => 5047651793918
  | 161 => 5036782537360
  | 162 => 5025947971249
  | 163 => 5015147907353
  | 164 => 5004382158742
  | 165 => 4993650539779
  | 166 => 4982952866111
  | 167 => 4972288954656
  | 168 => 4961658623590
  | 169 => 4951061692340
  | 170 => 4940497981569
  | 171 => 4929967313171
  | 172 => 4919469510252
  | 173 => 4909004397129
  | 174 => 4898571799311
  | 175 => 4888171543495
  | 176 => 4877803457553
  | 177 => 4867467370522
  | 178 => 4857163112594
  | 179 => 4846890515107
  | 180 => 4836649410535
  | 181 => 4826439632478
  | 182 => 4816261015651
  | 183 => 4806113395878
  | 184 => 4795996610080
  | 185 => 4785910496266
  | 186 => 4775854893524
  | 187 => 4765829642012
  | 188 => 4755834582949
  | 189 => 4745869558607
  | 190 => 4735934412301
  | 191 => 4726028988379
  | 192 => 4716153132217
  | 193 => 4706306690206
  | 194 => 4696489509749
  | 195 => 4686701439246
  | 196 => 4676942328091
  | 197 => 4667212026662
  | 198 => 4657510386312
  | 199 => 4647837259362
  | 200 => 4638192499093
  | 201 => 4628575959736
  | 202 => 4618987496468
  | 203 => 4609426965401
  | 204 => 4599894223577
  | 205 => 4590389128957
  | 206 => 4580911540415
  | 207 => 4571461317734
  | 208 => 4562038321592
  | 209 => 4552642413559
  | 210 => 4543273456092
  | 211 => 4533931312520
  | 212 => 4524615847045
  | 213 => 4515326924730
  | 214 => 4506064411496
  | 215 => 4496828174108
  | 216 => 4487618080178
  | 217 => 4478433998151
  | 218 => 4469275797300
  | 219 => 4460143347721
  | 220 => 4451036520323
  | 221 => 4441955186827
  | 222 => 4432899219754
  | 223 => 4423868492420
  | 224 => 4414862878934
  | 225 => 4405882254186
  | 226 => 4396926493842
  | 227 => 4387995474341
  | 228 => 4379089072886
  | 229 => 4370207167439
  | 230 => 4361349636715
  | 231 => 4352516360174
  | 232 => 4343707218019
  | 233 => 4334922091189
  | 234 => 4326160861350
  | 235 => 4317423410893
  | 236 => 4308709622928
  | 237 => 4300019381274
  | 238 => 4291352570462
  | 239 => 4282709075720
  | 240 => 4274088782974
  | 241 => 4265491578841
  | 242 => 4256917350623
  | 243 => 4248365986301
  | 244 => 4239837374530
  | 245 => 4231331404638
  | 246 => 4222847966614
  | 247 => 4214386951107
  | 248 => 4205948249421
  | 249 => 4197531753508
  | 250 => 4189137355967
  | 251 => 4180764950031
  | 252 => 4172414429574
  | 253 => 4164085689093
  | 254 => 4155778623716
  | 255 => 4147493129185
  | 256 => 4139229101863
  | 257 => 4130986438719
  | 258 => 4122765037331
  | 259 => 4114564795877
  | 260 => 4106385613133
  | 261 => 4098227388467
  | 262 => 4090090021835
  | 263 => 4081973413776
  | 264 => 4073877465409
  | 265 => 4065802078427
  | 266 => 4057747155094
  | 267 => 4049712598242
  | 268 => 4041698311262
  | 269 => 4033704198104
  | 270 => 4025730163274
  | 271 => 4017776111824
  | 272 => 4009841949354
  | 273 => 4001927582005
  | 274 => 3994032916455
  | 275 => 3986157859916
  | 276 => 3978302320129
  | 277 => 3970466205362
  | 278 => 3962649424404
  | 279 => 3954851886561
  | 280 => 3947073501655
  | 281 => 3939314180017
  | 282 => 3931573832487
  | 283 => 3923852370404
  | 284 => 3916149705611
  | 285 => 3908465750443
  | 286 => 3900800417729
  | 287 => 3893153620785
  | 288 => 3885525273415
  | 289 => 3877915289900
  | 290 => 3870323585004
  | 291 => 3862750073961
  | 292 => 3855194672478
  | 293 => 3847657296731
  | 294 => 3840137863358
  | 295 => 3832636289459
  | 296 => 3825152492592
  | 297 => 3817686390769
  | 298 => 3810237902454
  | 299 => 3802806946557
  | 300 => 3795393442434
  | 301 => 3787997309883
  | 302 => 3780618469140
  | 303 => 3773256840876
  | 304 => 3765912346194
  | 305 => 3758584906626
  | 306 => 3751274444131
  | 307 => 3743980881091
  | 308 => 3736704140307
  | 309 => 3729444144998
  | 310 => 3722200818797
  | 311 => 3714974085748
  | 312 => 3707763870304
  | 313 => 3700570097322
  | 314 => 3693392692064
  | 315 => 3686231580190
  | 316 => 3679086687758
  | 317 => 3671957941218
  | 318 => 3664845267416
  | 319 => 3657748593582
  | 320 => 3650667847334
  | 321 => 3643602956676
  | 322 => 3636553849987
  | 323 => 3629520456030
  | 324 => 3622502703939
  | 325 => 3615500523224
  | 326 => 3608513843763
  | 327 => 3601542595802
  | 328 => 3594586709955
  | 329 => 3587646117194
  | 330 => 3580720748856
  | 331 => 3573810536632
  | 332 => 3566915412570
  | 333 => 3560035309070
  | 334 => 3553170158883
  | 335 => 3546319895109
  | 336 => 3539484451192
  | 337 => 3532663760919
  | 338 => 3525857758419
  | 339 => 3519066378159
  | 340 => 3512289554944
  | 341 => 3505527223911
  | 342 => 3498779320529
  | 343 => 3492045780598
  | 344 => 3485326540242
  | 345 => 3478621535915
  | 346 => 3471930704390
  | 347 => 3465253982762
  | 348 => 3458591308444
  | 349 => 3451942619167
  | 350 => 3445307852974
  | 351 => 3438686948222
  | 352 => 3432079843577
  | 353 => 3425486478014
  | 354 => 3418906790813
  | 355 => 3412340721558
  | 356 => 3405788210136
  | 357 => 3399249196732
  | 358 => 3392723621830
  | 359 => 3386211426210
  | 360 => 3379712550945
  | 361 => 3373226937402
  | 362 => 3366754527235
  | 363 => 3360295262389
  | 364 => 3353849085094
  | 365 => 3347415937863
  | 366 => 3340995763494
  | 367 => 3334588505064
  | 368 => 3328194105928
  | 369 => 3321812509720
  | 370 => 3315443660348
  | 371 => 3309087501992
  | 372 => 3302743979107
  | 373 => 3296413036413
  | 374 => 3290094618902
  | 375 => 3283788671830
  | 376 => 3277495140718
  | 377 => 3271213971350
  | 378 => 3264945109770
  | 379 => 3258688502283
  | 380 => 3252444095450
  | 381 => 3246211836089
  | 382 => 3239991671272
  | 383 => 3233783548323
  | 384 => 3227587414819
  | 385 => 3221403218583
  | 386 => 3215230907688
  | 387 => 3209070430455
  | 388 => 3202921735445
  | 389 => 3196784771466
  | 390 => 3190659487566
  | 391 => 3184545833032
  | 392 => 3178443757390
  | 393 => 3172353210404
  | 394 => 3166274142073
  | 395 => 3160206502627
  | 396 => 3154150242532
  | 397 => 3148105312482
  | 398 => 3142071663404
  | 399 => 3136049246448
  | 400 => 3130038012994
  | 401 => 3124037914645
  | 402 => 3118048903230
  | 403 => 3112070930798
  | 404 => 3106103949619
  | 405 => 3100147912183
  | 406 => 3094202771198
  | 407 => 3088268479587
  | 408 => 3082344990490
  | 409 => 3076432257260
  | 410 => 3070530233464
  | 411 => 3064638872877
  | 412 => 3058758129486
  | 413 => 3052887957486
  | 414 => 3047028311281
  | 415 => 3041179145477
  | 416 => 3035340414887
  | 417 => 3029512074528
  | 418 => 3023694079618
  | 419 => 3017886385576
  | 420 => 3012088948019
  | 421 => 3006301722764
  | 422 => 3000524665826
  | 423 => 2994757733413
  | 424 => 2989000881929
  | 425 => 2983254067972
  | 426 => 2977517248331
  | 427 => 2971790379986
  | 428 => 2966073420109
  | 429 => 2960366326056
  | 430 => 2954669055376
  | 431 => 2948981565800
  | 432 => 2943303815246
  | 433 => 2937635761815
  | 434 => 2931977363792
  | 435 => 2926328579643
  | 436 => 2920689368014
  | 437 => 2915059687733
  | 438 => 2909439497802
  | 439 => 2903828757404
  | 440 => 2898227425897
  | 441 => 2892635462814
  | 442 => 2887052827862
  | 443 => 2881479480920
  | 444 => 2875915382042
  | 445 => 2870360491448
  | 446 => 2864814769532
  | 447 => 2859278176855
  | 448 => 2853750674146
  | 449 => 2848232222300
  | 450 => 2842722782379
  | 451 => 2837222315608
  | 452 => 2831730783377
  | 453 => 2826248147239
  | 454 => 2820774368906
  | 455 => 2815309410255
  | 456 => 2809853233318
  | 457 => 2804405800290
  | 458 => 2798967073520
  | 459 => 2793537015517
  | 460 => 2788115588943
  | 461 => 2782702756618
  | 462 => 2777298481514
  | 463 => 2771902726755
  | 464 => 2766515455620
  | 465 => 2761136631538
  | 466 => 2755766218087
  | 467 => 2750404178995
  | 468 => 2745050478141
  | 469 => 2739705079547
  | 470 => 2734367947386
  | 471 => 2729039045975
  | 472 => 2723718339775
  | 473 => 2718405793393
  | 474 => 2713101371578
  | 475 => 2707805039221
  | 476 => 2702516761356
  | 477 => 2697236503155
  | 478 => 2691964229934
  | 479 => 2686699907144
  | 480 => 2681443500377
  | 481 => 2676194975359
  | 482 => 2670954297955
  | 483 => 2665721434166
  | 484 => 2660496350127
  | 485 => 2655279012105
  | 486 => 2650069386505
  | 487 => 2644867439860
  | 488 => 2639673138838
  | 489 => 2634486450234
  | 490 => 2629307340977
  | 491 => 2624135778123
  | 492 => 2618971728858
  | 493 => 2613815160495
  | 494 => 2608666040474
  | 495 => 2603524336361
  | 496 => 2598390015848
  | 497 => 2593263046752
  | 498 => 2588143397014
  | 499 => 2583031034698
  | 500 => 2577925927991
  | 501 => 2572828045201
  | 502 => 2567737354758
  | 503 => 2562653825213
  | 504 => 2557577425234
  | 505 => 2552508123611
  | 506 => 2547445889251
  | 507 => 2542390691178
  | 508 => 2537342498535
  | 509 => 2532301280579
  | 510 => 2527267006684
  | 511 => 2522239646337
  | _ => 0
def payment (i : ℕ) : ℝ := (numerator i:ℝ)/1000000000000
set_option maxRecDepth 10000 in
theorem numerator_sum : (∑ i ∈ range 512, numerator i) = 2253660978484446 := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem payments_paid (j : Fin 512) : upperValue ((point j.val+point (j.val+1))/2) ≤ payment j.val := by
  fin_cases j
  · change upperValue ((point 0+point 1)/2) ≤ payment 0
    have hp : payment 0 = (7416360053360:ℝ)/1000000000000 := rfl
    have hx : (point 0+point 1)/2 = (17006453:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_0
  · change upperValue ((point 1+point 2)/2) ≤ payment 1
    have hp : payment 1 = (7396118378787:ℝ)/1000000000000 := rfl
    have hx : (point 1+point 2)/2 = (17048159:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_1
  · change upperValue ((point 2+point 3)/2) ≤ payment 2
    have hp : payment 2 = (7375971809833:ℝ)/1000000000000 := rfl
    have hx : (point 2+point 3)/2 = (17089865:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_2
  · change upperValue ((point 3+point 4)/2) ≤ payment 3
    have hp : payment 3 = (7355919645923:ℝ)/1000000000000 := rfl
    have hx : (point 3+point 4)/2 = (17131571:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_3
  · change upperValue ((point 4+point 5)/2) ≤ payment 4
    have hp : payment 4 = (7335961193279:ℝ)/1000000000000 := rfl
    have hx : (point 4+point 5)/2 = (17173277:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_4
  · change upperValue ((point 5+point 6)/2) ≤ payment 5
    have hp : payment 5 = (7316095764831:ℝ)/1000000000000 := rfl
    have hx : (point 5+point 6)/2 = (17214983:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_5
  · change upperValue ((point 6+point 7)/2) ≤ payment 6
    have hp : payment 6 = (7296322680142:ℝ)/1000000000000 := rfl
    have hx : (point 6+point 7)/2 = (17256689:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_6
  · change upperValue ((point 7+point 8)/2) ≤ payment 7
    have hp : payment 7 = (7276641265325:ℝ)/1000000000000 := rfl
    have hx : (point 7+point 8)/2 = (17298395:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_7
  · change upperValue ((point 8+point 9)/2) ≤ payment 8
    have hp : payment 8 = (7257050852965:ℝ)/1000000000000 := rfl
    have hx : (point 8+point 9)/2 = (17340101:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_8
  · change upperValue ((point 9+point 10)/2) ≤ payment 9
    have hp : payment 9 = (7237550782041:ℝ)/1000000000000 := rfl
    have hx : (point 9+point 10)/2 = (17381807:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_9
  · change upperValue ((point 10+point 11)/2) ≤ payment 10
    have hp : payment 10 = (7218140397850:ℝ)/1000000000000 := rfl
    have hx : (point 10+point 11)/2 = (17423513:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_10
  · change upperValue ((point 11+point 12)/2) ≤ payment 11
    have hp : payment 11 = (7198819051932:ℝ)/1000000000000 := rfl
    have hx : (point 11+point 12)/2 = (17465219:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_11
  · change upperValue ((point 12+point 13)/2) ≤ payment 12
    have hp : payment 12 = (7179586101992:ℝ)/1000000000000 := rfl
    have hx : (point 12+point 13)/2 = (17506925:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_12
  · change upperValue ((point 13+point 14)/2) ≤ payment 13
    have hp : payment 13 = (7160440911831:ℝ)/1000000000000 := rfl
    have hx : (point 13+point 14)/2 = (17548631:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_13
  · change upperValue ((point 14+point 15)/2) ≤ payment 14
    have hp : payment 14 = (7141382851275:ℝ)/1000000000000 := rfl
    have hx : (point 14+point 15)/2 = (17590337:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_14
  · change upperValue ((point 15+point 16)/2) ≤ payment 15
    have hp : payment 15 = (7122411296096:ℝ)/1000000000000 := rfl
    have hx : (point 15+point 16)/2 = (17632043:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_15
  · change upperValue ((point 16+point 17)/2) ≤ payment 16
    have hp : payment 16 = (7103525627950:ℝ)/1000000000000 := rfl
    have hx : (point 16+point 17)/2 = (17673749:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_16
  · change upperValue ((point 17+point 18)/2) ≤ payment 17
    have hp : payment 17 = (7084725234304:ℝ)/1000000000000 := rfl
    have hx : (point 17+point 18)/2 = (17715455:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_17
  · change upperValue ((point 18+point 19)/2) ≤ payment 18
    have hp : payment 18 = (7066009508367:ℝ)/1000000000000 := rfl
    have hx : (point 18+point 19)/2 = (17757161:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_18
  · change upperValue ((point 19+point 20)/2) ≤ payment 19
    have hp : payment 19 = (7047377849025:ℝ)/1000000000000 := rfl
    have hx : (point 19+point 20)/2 = (17798867:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_19
  · change upperValue ((point 20+point 21)/2) ≤ payment 20
    have hp : payment 20 = (7028829660774:ℝ)/1000000000000 := rfl
    have hx : (point 20+point 21)/2 = (17840573:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_20
  · change upperValue ((point 21+point 22)/2) ≤ payment 21
    have hp : payment 21 = (7010364353652:ℝ)/1000000000000 := rfl
    have hx : (point 21+point 22)/2 = (17882279:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_21
  · change upperValue ((point 22+point 23)/2) ≤ payment 22
    have hp : payment 22 = (6991981343179:ℝ)/1000000000000 := rfl
    have hx : (point 22+point 23)/2 = (17923985:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_22
  · change upperValue ((point 23+point 24)/2) ≤ payment 23
    have hp : payment 23 = (6973680050290:ℝ)/1000000000000 := rfl
    have hx : (point 23+point 24)/2 = (17965691:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_23
  · change upperValue ((point 24+point 25)/2) ≤ payment 24
    have hp : payment 24 = (6955459901271:ℝ)/1000000000000 := rfl
    have hx : (point 24+point 25)/2 = (18007397:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_24
  · change upperValue ((point 25+point 26)/2) ≤ payment 25
    have hp : payment 25 = (6937320327703:ℝ)/1000000000000 := rfl
    have hx : (point 25+point 26)/2 = (18049103:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_25
  · change upperValue ((point 26+point 27)/2) ≤ payment 26
    have hp : payment 26 = (6919260766396:ℝ)/1000000000000 := rfl
    have hx : (point 26+point 27)/2 = (18090809:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_26
  · change upperValue ((point 27+point 28)/2) ≤ payment 27
    have hp : payment 27 = (6901280659328:ℝ)/1000000000000 := rfl
    have hx : (point 27+point 28)/2 = (18132515:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_27
  · change upperValue ((point 28+point 29)/2) ≤ payment 28
    have hp : payment 28 = (6883379453590:ℝ)/1000000000000 := rfl
    have hx : (point 28+point 29)/2 = (18174221:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_28
  · change upperValue ((point 29+point 30)/2) ≤ payment 29
    have hp : payment 29 = (6865556601326:ℝ)/1000000000000 := rfl
    have hx : (point 29+point 30)/2 = (18215927:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_29
  · change upperValue ((point 30+point 31)/2) ≤ payment 30
    have hp : payment 30 = (6847811559671:ℝ)/1000000000000 := rfl
    have hx : (point 30+point 31)/2 = (18257633:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_30
  · change upperValue ((point 31+point 32)/2) ≤ payment 31
    have hp : payment 31 = (6830143790701:ℝ)/1000000000000 := rfl
    have hx : (point 31+point 32)/2 = (18299339:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_31
  · change upperValue ((point 32+point 33)/2) ≤ payment 32
    have hp : payment 32 = (6812552761373:ℝ)/1000000000000 := rfl
    have hx : (point 32+point 33)/2 = (18341045:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_32
  · change upperValue ((point 33+point 34)/2) ≤ payment 33
    have hp : payment 33 = (6795037943467:ℝ)/1000000000000 := rfl
    have hx : (point 33+point 34)/2 = (18382751:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_33
  · change upperValue ((point 34+point 35)/2) ≤ payment 34
    have hp : payment 34 = (6777598813538:ℝ)/1000000000000 := rfl
    have hx : (point 34+point 35)/2 = (18424457:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_34
  · change upperValue ((point 35+point 36)/2) ≤ payment 35
    have hp : payment 35 = (6760234852857:ℝ)/1000000000000 := rfl
    have hx : (point 35+point 36)/2 = (18466163:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_35
  · change upperValue ((point 36+point 37)/2) ≤ payment 36
    have hp : payment 36 = (6742945547358:ℝ)/1000000000000 := rfl
    have hx : (point 36+point 37)/2 = (18507869:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_36
  · change upperValue ((point 37+point 38)/2) ≤ payment 37
    have hp : payment 37 = (6725730387589:ℝ)/1000000000000 := rfl
    have hx : (point 37+point 38)/2 = (18549575:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_37
  · change upperValue ((point 38+point 39)/2) ≤ payment 38
    have hp : payment 38 = (6708588868657:ℝ)/1000000000000 := rfl
    have hx : (point 38+point 39)/2 = (18591281:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_38
  · change upperValue ((point 39+point 40)/2) ≤ payment 39
    have hp : payment 39 = (6691520490178:ℝ)/1000000000000 := rfl
    have hx : (point 39+point 40)/2 = (18632987:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_39
  · change upperValue ((point 40+point 41)/2) ≤ payment 40
    have hp : payment 40 = (6674524756226:ℝ)/1000000000000 := rfl
    have hx : (point 40+point 41)/2 = (18674693:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_40
  · change upperValue ((point 41+point 42)/2) ≤ payment 41
    have hp : payment 41 = (6657601175285:ℝ)/1000000000000 := rfl
    have hx : (point 41+point 42)/2 = (18716399:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_41
  · change upperValue ((point 42+point 43)/2) ≤ payment 42
    have hp : payment 42 = (6640749260199:ℝ)/1000000000000 := rfl
    have hx : (point 42+point 43)/2 = (18758105:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_42
  · change upperValue ((point 43+point 44)/2) ≤ payment 43
    have hp : payment 43 = (6623968528122:ℝ)/1000000000000 := rfl
    have hx : (point 43+point 44)/2 = (18799811:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_43
  · change upperValue ((point 44+point 45)/2) ≤ payment 44
    have hp : payment 44 = (6607258500474:ℝ)/1000000000000 := rfl
    have hx : (point 44+point 45)/2 = (18841517:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_44
  · change upperValue ((point 45+point 46)/2) ≤ payment 45
    have hp : payment 45 = (6590618702888:ℝ)/1000000000000 := rfl
    have hx : (point 45+point 46)/2 = (18883223:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_45
  · change upperValue ((point 46+point 47)/2) ≤ payment 46
    have hp : payment 46 = (6574048665172:ℝ)/1000000000000 := rfl
    have hx : (point 46+point 47)/2 = (18924929:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_46
  · change upperValue ((point 47+point 48)/2) ≤ payment 47
    have hp : payment 47 = (6557547921254:ℝ)/1000000000000 := rfl
    have hx : (point 47+point 48)/2 = (18966635:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_47
  · change upperValue ((point 48+point 49)/2) ≤ payment 48
    have hp : payment 48 = (6541116009143:ℝ)/1000000000000 := rfl
    have hx : (point 48+point 49)/2 = (184547:ℝ)/1358848 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_48
  · change upperValue ((point 49+point 50)/2) ≤ payment 49
    have hp : payment 49 = (6524752470883:ℝ)/1000000000000 := rfl
    have hx : (point 49+point 50)/2 = (19050047:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_49
  · change upperValue ((point 50+point 51)/2) ≤ payment 50
    have hp : payment 50 = (6508456852506:ℝ)/1000000000000 := rfl
    have hx : (point 50+point 51)/2 = (19091753:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_50
  · change upperValue ((point 51+point 52)/2) ≤ payment 51
    have hp : payment 51 = (6492228703993:ℝ)/1000000000000 := rfl
    have hx : (point 51+point 52)/2 = (19133459:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_51
  · change upperValue ((point 52+point 53)/2) ≤ payment 52
    have hp : payment 52 = (6476067579227:ℝ)/1000000000000 := rfl
    have hx : (point 52+point 53)/2 = (19175165:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_52
  · change upperValue ((point 53+point 54)/2) ≤ payment 53
    have hp : payment 53 = (6459973035954:ℝ)/1000000000000 := rfl
    have hx : (point 53+point 54)/2 = (19216871:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_53
  · change upperValue ((point 54+point 55)/2) ≤ payment 54
    have hp : payment 54 = (6443944635738:ℝ)/1000000000000 := rfl
    have hx : (point 54+point 55)/2 = (19258577:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_54
  · change upperValue ((point 55+point 56)/2) ≤ payment 55
    have hp : payment 55 = (6427981943922:ℝ)/1000000000000 := rfl
    have hx : (point 55+point 56)/2 = (19300283:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_55
  · change upperValue ((point 56+point 57)/2) ≤ payment 56
    have hp : payment 56 = (6412084529586:ℝ)/1000000000000 := rfl
    have hx : (point 56+point 57)/2 = (19341989:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_56
  · change upperValue ((point 57+point 58)/2) ≤ payment 57
    have hp : payment 57 = (6396251965508:ℝ)/1000000000000 := rfl
    have hx : (point 57+point 58)/2 = (19383695:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_57
  · change upperValue ((point 58+point 59)/2) ≤ payment 58
    have hp : payment 58 = (6380483828124:ℝ)/1000000000000 := rfl
    have hx : (point 58+point 59)/2 = (19425401:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_58
  · change upperValue ((point 59+point 60)/2) ≤ payment 59
    have hp : payment 59 = (6364779697486:ℝ)/1000000000000 := rfl
    have hx : (point 59+point 60)/2 = (19467107:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_59
  · change upperValue ((point 60+point 61)/2) ≤ payment 60
    have hp : payment 60 = (6349139157228:ℝ)/1000000000000 := rfl
    have hx : (point 60+point 61)/2 = (19508813:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_60
  · change upperValue ((point 61+point 62)/2) ≤ payment 61
    have hp : payment 61 = (6333561794525:ℝ)/1000000000000 := rfl
    have hx : (point 61+point 62)/2 = (19550519:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_61
  · change upperValue ((point 62+point 63)/2) ≤ payment 62
    have hp : payment 62 = (6318047200055:ℝ)/1000000000000 := rfl
    have hx : (point 62+point 63)/2 = (19592225:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_62
  · change upperValue ((point 63+point 64)/2) ≤ payment 63
    have hp : payment 63 = (6302594967962:ℝ)/1000000000000 := rfl
    have hx : (point 63+point 64)/2 = (19633931:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_63
  · change upperValue ((point 64+point 65)/2) ≤ payment 64
    have hp : payment 64 = (6287204695822:ℝ)/1000000000000 := rfl
    have hx : (point 64+point 65)/2 = (19675637:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_64
  · change upperValue ((point 65+point 66)/2) ≤ payment 65
    have hp : payment 65 = (6271875984601:ℝ)/1000000000000 := rfl
    have hx : (point 65+point 66)/2 = (19717343:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_65
  · change upperValue ((point 66+point 67)/2) ≤ payment 66
    have hp : payment 66 = (6256608438625:ℝ)/1000000000000 := rfl
    have hx : (point 66+point 67)/2 = (19759049:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_66
  · change upperValue ((point 67+point 68)/2) ≤ payment 67
    have hp : payment 67 = (6241401665542:ℝ)/1000000000000 := rfl
    have hx : (point 67+point 68)/2 = (19800755:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_67
  · change upperValue ((point 68+point 69)/2) ≤ payment 68
    have hp : payment 68 = (6226255276287:ℝ)/1000000000000 := rfl
    have hx : (point 68+point 69)/2 = (19842461:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_68
  · change upperValue ((point 69+point 70)/2) ≤ payment 69
    have hp : payment 69 = (6211168885047:ℝ)/1000000000000 := rfl
    have hx : (point 69+point 70)/2 = (19884167:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_69
  · change upperValue ((point 70+point 71)/2) ≤ payment 70
    have hp : payment 70 = (6196142109228:ℝ)/1000000000000 := rfl
    have hx : (point 70+point 71)/2 = (19925873:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_70
  · change upperValue ((point 71+point 72)/2) ≤ payment 71
    have hp : payment 71 = (6181174569422:ℝ)/1000000000000 := rfl
    have hx : (point 71+point 72)/2 = (19967579:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_71
  · change upperValue ((point 72+point 73)/2) ≤ payment 72
    have hp : payment 72 = (6166265889371:ℝ)/1000000000000 := rfl
    have hx : (point 72+point 73)/2 = (20009285:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_72
  · change upperValue ((point 73+point 74)/2) ≤ payment 73
    have hp : payment 73 = (6151415695938:ℝ)/1000000000000 := rfl
    have hx : (point 73+point 74)/2 = (20050991:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_73
  · change upperValue ((point 74+point 75)/2) ≤ payment 74
    have hp : payment 74 = (6136623619071:ℝ)/1000000000000 := rfl
    have hx : (point 74+point 75)/2 = (20092697:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_74
  · change upperValue ((point 75+point 76)/2) ≤ payment 75
    have hp : payment 75 = (6121889291774:ℝ)/1000000000000 := rfl
    have hx : (point 75+point 76)/2 = (20134403:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_75
  · change upperValue ((point 76+point 77)/2) ≤ payment 76
    have hp : payment 76 = (6107212350072:ℝ)/1000000000000 := rfl
    have hx : (point 76+point 77)/2 = (20176109:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_76
  · change upperValue ((point 77+point 78)/2) ≤ payment 77
    have hp : payment 77 = (6092592432984:ℝ)/1000000000000 := rfl
    have hx : (point 77+point 78)/2 = (20217815:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_77
  · change upperValue ((point 78+point 79)/2) ≤ payment 78
    have hp : payment 78 = (6078029182489:ℝ)/1000000000000 := rfl
    have hx : (point 78+point 79)/2 = (20259521:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_78
  · change upperValue ((point 79+point 80)/2) ≤ payment 79
    have hp : payment 79 = (6063522243496:ℝ)/1000000000000 := rfl
    have hx : (point 79+point 80)/2 = (20301227:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_79
  · change upperValue ((point 80+point 81)/2) ≤ payment 80
    have hp : payment 80 = (6049071263816:ℝ)/1000000000000 := rfl
    have hx : (point 80+point 81)/2 = (20342933:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_80
  · change upperValue ((point 81+point 82)/2) ≤ payment 81
    have hp : payment 81 = (6034675894128:ℝ)/1000000000000 := rfl
    have hx : (point 81+point 82)/2 = (20384639:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_81
  · change upperValue ((point 82+point 83)/2) ≤ payment 82
    have hp : payment 82 = (6020335787956:ℝ)/1000000000000 := rfl
    have hx : (point 82+point 83)/2 = (20426345:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_82
  · change upperValue ((point 83+point 84)/2) ≤ payment 83
    have hp : payment 83 = (6006050601635:ℝ)/1000000000000 := rfl
    have hx : (point 83+point 84)/2 = (20468051:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_83
  · change upperValue ((point 84+point 85)/2) ≤ payment 84
    have hp : payment 84 = (5991819994282:ℝ)/1000000000000 := rfl
    have hx : (point 84+point 85)/2 = (20509757:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_84
  · change upperValue ((point 85+point 86)/2) ≤ payment 85
    have hp : payment 85 = (5977643627772:ℝ)/1000000000000 := rfl
    have hx : (point 85+point 86)/2 = (20551463:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_85
  · change upperValue ((point 86+point 87)/2) ≤ payment 86
    have hp : payment 86 = (5963521166706:ℝ)/1000000000000 := rfl
    have hx : (point 86+point 87)/2 = (20593169:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_86
  · change upperValue ((point 87+point 88)/2) ≤ payment 87
    have hp : payment 87 = (5949452278388:ℝ)/1000000000000 := rfl
    have hx : (point 87+point 88)/2 = (20634875:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_87
  · change upperValue ((point 88+point 89)/2) ≤ payment 88
    have hp : payment 88 = (5935436632790:ℝ)/1000000000000 := rfl
    have hx : (point 88+point 89)/2 = (20676581:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_88
  · change upperValue ((point 89+point 90)/2) ≤ payment 89
    have hp : payment 89 = (5921473902534:ℝ)/1000000000000 := rfl
    have hx : (point 89+point 90)/2 = (20718287:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_89
  · change upperValue ((point 90+point 91)/2) ≤ payment 90
    have hp : payment 90 = (5907563762859:ℝ)/1000000000000 := rfl
    have hx : (point 90+point 91)/2 = (20759993:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_90
  · change upperValue ((point 91+point 92)/2) ≤ payment 91
    have hp : payment 91 = (5893705891598:ℝ)/1000000000000 := rfl
    have hx : (point 91+point 92)/2 = (20801699:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_91
  · change upperValue ((point 92+point 93)/2) ≤ payment 92
    have hp : payment 92 = (5879899969151:ℝ)/1000000000000 := rfl
    have hx : (point 92+point 93)/2 = (20843405:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_92
  · change upperValue ((point 93+point 94)/2) ≤ payment 93
    have hp : payment 93 = (5866145678458:ℝ)/1000000000000 := rfl
    have hx : (point 93+point 94)/2 = (20885111:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_93
  · change upperValue ((point 94+point 95)/2) ≤ payment 94
    have hp : payment 94 = (5852442704978:ℝ)/1000000000000 := rfl
    have hx : (point 94+point 95)/2 = (20926817:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_94
  · change upperValue ((point 95+point 96)/2) ≤ payment 95
    have hp : payment 95 = (5838790736657:ℝ)/1000000000000 := rfl
    have hx : (point 95+point 96)/2 = (20968523:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_95
  · change upperValue ((point 96+point 97)/2) ≤ payment 96
    have hp : payment 96 = (5825189463911:ℝ)/1000000000000 := rfl
    have hx : (point 96+point 97)/2 = (21010229:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_96
  · change upperValue ((point 97+point 98)/2) ≤ payment 97
    have hp : payment 97 = (5811638579594:ℝ)/1000000000000 := rfl
    have hx : (point 97+point 98)/2 = (21051935:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_97
  · change upperValue ((point 98+point 99)/2) ≤ payment 98
    have hp : payment 98 = (5798137778981:ℝ)/1000000000000 := rfl
    have hx : (point 98+point 99)/2 = (21093641:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_98
  · change upperValue ((point 99+point 100)/2) ≤ payment 99
    have hp : payment 99 = (5784686759739:ℝ)/1000000000000 := rfl
    have hx : (point 99+point 100)/2 = (21135347:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_99
  · change upperValue ((point 100+point 101)/2) ≤ payment 100
    have hp : payment 100 = (5771285221904:ℝ)/1000000000000 := rfl
    have hx : (point 100+point 101)/2 = (21177053:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_100
  · change upperValue ((point 101+point 102)/2) ≤ payment 101
    have hp : payment 101 = (5757932867862:ℝ)/1000000000000 := rfl
    have hx : (point 101+point 102)/2 = (21218759:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_101
  · change upperValue ((point 102+point 103)/2) ≤ payment 102
    have hp : payment 102 = (5744629402320:ℝ)/1000000000000 := rfl
    have hx : (point 102+point 103)/2 = (21260465:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_102
  · change upperValue ((point 103+point 104)/2) ≤ payment 103
    have hp : payment 103 = (5731374532287:ℝ)/1000000000000 := rfl
    have hx : (point 103+point 104)/2 = (21302171:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_103
  · change upperValue ((point 104+point 105)/2) ≤ payment 104
    have hp : payment 104 = (5718167967049:ℝ)/1000000000000 := rfl
    have hx : (point 104+point 105)/2 = (21343877:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_104
  · change upperValue ((point 105+point 106)/2) ≤ payment 105
    have hp : payment 105 = (5705009418151:ℝ)/1000000000000 := rfl
    have hx : (point 105+point 106)/2 = (21385583:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_105
  · change upperValue ((point 106+point 107)/2) ≤ payment 106
    have hp : payment 106 = (5691898599370:ℝ)/1000000000000 := rfl
    have hx : (point 106+point 107)/2 = (21427289:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_106
  · change upperValue ((point 107+point 108)/2) ≤ payment 107
    have hp : payment 107 = (5678835226696:ℝ)/1000000000000 := rfl
    have hx : (point 107+point 108)/2 = (21468995:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_107
  · change upperValue ((point 108+point 109)/2) ≤ payment 108
    have hp : payment 108 = (5665819018310:ℝ)/1000000000000 := rfl
    have hx : (point 108+point 109)/2 = (21510701:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_108
  · change upperValue ((point 109+point 110)/2) ≤ payment 109
    have hp : payment 109 = (5652849694564:ℝ)/1000000000000 := rfl
    have hx : (point 109+point 110)/2 = (21552407:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_109
  · change upperValue ((point 110+point 111)/2) ≤ payment 110
    have hp : payment 110 = (5639926977957:ℝ)/1000000000000 := rfl
    have hx : (point 110+point 111)/2 = (21594113:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_110
  · change upperValue ((point 111+point 112)/2) ≤ payment 111
    have hp : payment 111 = (5627050593117:ℝ)/1000000000000 := rfl
    have hx : (point 111+point 112)/2 = (21635819:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_111
  · change upperValue ((point 112+point 113)/2) ≤ payment 112
    have hp : payment 112 = (5614220266779:ℝ)/1000000000000 := rfl
    have hx : (point 112+point 113)/2 = (21677525:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_112
  · change upperValue ((point 113+point 114)/2) ≤ payment 113
    have hp : payment 113 = (5601435727766:ℝ)/1000000000000 := rfl
    have hx : (point 113+point 114)/2 = (21719231:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_113
  · change upperValue ((point 114+point 115)/2) ≤ payment 114
    have hp : payment 114 = (5588696706968:ℝ)/1000000000000 := rfl
    have hx : (point 114+point 115)/2 = (21760937:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_114
  · change upperValue ((point 115+point 116)/2) ≤ payment 115
    have hp : payment 115 = (5576002937323:ℝ)/1000000000000 := rfl
    have hx : (point 115+point 116)/2 = (21802643:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_115
  · change upperValue ((point 116+point 117)/2) ≤ payment 116
    have hp : payment 116 = (5563354153796:ℝ)/1000000000000 := rfl
    have hx : (point 116+point 117)/2 = (21844349:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_116
  · change upperValue ((point 117+point 118)/2) ≤ payment 117
    have hp : payment 117 = (5550750093360:ℝ)/1000000000000 := rfl
    have hx : (point 117+point 118)/2 = (21886055:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_117
  · change upperValue ((point 118+point 119)/2) ≤ payment 118
    have hp : payment 118 = (5538190494980:ℝ)/1000000000000 := rfl
    have hx : (point 118+point 119)/2 = (21927761:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_118
  · change upperValue ((point 119+point 120)/2) ≤ payment 119
    have hp : payment 119 = (5525675099589:ℝ)/1000000000000 := rfl
    have hx : (point 119+point 120)/2 = (21969467:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_119
  · change upperValue ((point 120+point 121)/2) ≤ payment 120
    have hp : payment 120 = (5513203650073:ℝ)/1000000000000 := rfl
    have hx : (point 120+point 121)/2 = (22011173:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_120
  · change upperValue ((point 121+point 122)/2) ≤ payment 121
    have hp : payment 121 = (5500775891251:ℝ)/1000000000000 := rfl
    have hx : (point 121+point 122)/2 = (22052879:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_121
  · change upperValue ((point 122+point 123)/2) ≤ payment 122
    have hp : payment 122 = (5488391569857:ℝ)/1000000000000 := rfl
    have hx : (point 122+point 123)/2 = (22094585:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_122
  · change upperValue ((point 123+point 124)/2) ≤ payment 123
    have hp : payment 123 = (5476050434522:ℝ)/1000000000000 := rfl
    have hx : (point 123+point 124)/2 = (22136291:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_123
  · change upperValue ((point 124+point 125)/2) ≤ payment 124
    have hp : payment 124 = (5463752235756:ℝ)/1000000000000 := rfl
    have hx : (point 124+point 125)/2 = (22177997:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_124
  · change upperValue ((point 125+point 126)/2) ≤ payment 125
    have hp : payment 125 = (5451496725932:ℝ)/1000000000000 := rfl
    have hx : (point 125+point 126)/2 = (22219703:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_125
  · change upperValue ((point 126+point 127)/2) ≤ payment 126
    have hp : payment 126 = (5439283659264:ℝ)/1000000000000 := rfl
    have hx : (point 126+point 127)/2 = (22261409:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_126
  · change upperValue ((point 127+point 128)/2) ≤ payment 127
    have hp : payment 127 = (5427112791796:ℝ)/1000000000000 := rfl
    have hx : (point 127+point 128)/2 = (22303115:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_127
  · change upperValue ((point 128+point 129)/2) ≤ payment 128
    have hp : payment 128 = (5414983881379:ℝ)/1000000000000 := rfl
    have hx : (point 128+point 129)/2 = (22344821:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_128
  · change upperValue ((point 129+point 130)/2) ≤ payment 129
    have hp : payment 129 = (5402896687658:ℝ)/1000000000000 := rfl
    have hx : (point 129+point 130)/2 = (22386527:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_129
  · change upperValue ((point 130+point 131)/2) ≤ payment 130
    have hp : payment 130 = (5390850972055:ℝ)/1000000000000 := rfl
    have hx : (point 130+point 131)/2 = (22428233:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_130
  · change upperValue ((point 131+point 132)/2) ≤ payment 131
    have hp : payment 131 = (5378846497750:ℝ)/1000000000000 := rfl
    have hx : (point 131+point 132)/2 = (22469939:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_131
  · change upperValue ((point 132+point 133)/2) ≤ payment 132
    have hp : payment 132 = (5366883029666:ℝ)/1000000000000 := rfl
    have hx : (point 132+point 133)/2 = (22511645:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_132
  · change upperValue ((point 133+point 134)/2) ≤ payment 133
    have hp : payment 133 = (5354960334454:ℝ)/1000000000000 := rfl
    have hx : (point 133+point 134)/2 = (22553351:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_133
  · change upperValue ((point 134+point 135)/2) ≤ payment 134
    have hp : payment 134 = (5343078180477:ℝ)/1000000000000 := rfl
    have hx : (point 134+point 135)/2 = (22595057:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_134
  · change upperValue ((point 135+point 136)/2) ≤ payment 135
    have hp : payment 135 = (5331236337791:ℝ)/1000000000000 := rfl
    have hx : (point 135+point 136)/2 = (22636763:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_135
  · change upperValue ((point 136+point 137)/2) ≤ payment 136
    have hp : payment 136 = (5319434578135:ℝ)/1000000000000 := rfl
    have hx : (point 136+point 137)/2 = (22678469:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_136
  · change upperValue ((point 137+point 138)/2) ≤ payment 137
    have hp : payment 137 = (5307672674908:ℝ)/1000000000000 := rfl
    have hx : (point 137+point 138)/2 = (22720175:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_137
  · change upperValue ((point 138+point 139)/2) ≤ payment 138
    have hp : payment 138 = (5295950403162:ℝ)/1000000000000 := rfl
    have hx : (point 138+point 139)/2 = (22761881:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_138
  · change upperValue ((point 139+point 140)/2) ≤ payment 139
    have hp : payment 139 = (5284267539581:ℝ)/1000000000000 := rfl
    have hx : (point 139+point 140)/2 = (22803587:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_139
  · change upperValue ((point 140+point 141)/2) ≤ payment 140
    have hp : payment 140 = (5272623862467:ℝ)/1000000000000 := rfl
    have hx : (point 140+point 141)/2 = (22845293:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_140
  · change upperValue ((point 141+point 142)/2) ≤ payment 141
    have hp : payment 141 = (5261019151729:ℝ)/1000000000000 := rfl
    have hx : (point 141+point 142)/2 = (22886999:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_141
  · change upperValue ((point 142+point 143)/2) ≤ payment 142
    have hp : payment 142 = (5249453188862:ℝ)/1000000000000 := rfl
    have hx : (point 142+point 143)/2 = (22928705:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_142
  · change upperValue ((point 143+point 144)/2) ≤ payment 143
    have hp : payment 143 = (5237925756939:ℝ)/1000000000000 := rfl
    have hx : (point 143+point 144)/2 = (22970411:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_143
  · change upperValue ((point 144+point 145)/2) ≤ payment 144
    have hp : payment 144 = (5226436640593:ℝ)/1000000000000 := rfl
    have hx : (point 144+point 145)/2 = (23012117:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_144
  · change upperValue ((point 145+point 146)/2) ≤ payment 145
    have hp : payment 145 = (5214985626003:ℝ)/1000000000000 := rfl
    have hx : (point 145+point 146)/2 = (23053823:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_145
  · change upperValue ((point 146+point 147)/2) ≤ payment 146
    have hp : payment 146 = (5203572500882:ℝ)/1000000000000 := rfl
    have hx : (point 146+point 147)/2 = (23095529:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_146
  · change upperValue ((point 147+point 148)/2) ≤ payment 147
    have hp : payment 147 = (5192197054459:ℝ)/1000000000000 := rfl
    have hx : (point 147+point 148)/2 = (23137235:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_147
  · change upperValue ((point 148+point 149)/2) ≤ payment 148
    have hp : payment 148 = (5180859077471:ℝ)/1000000000000 := rfl
    have hx : (point 148+point 149)/2 = (23178941:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_148
  · change upperValue ((point 149+point 150)/2) ≤ payment 149
    have hp : payment 149 = (5169558362146:ℝ)/1000000000000 := rfl
    have hx : (point 149+point 150)/2 = (23220647:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_149
  · change upperValue ((point 150+point 151)/2) ≤ payment 150
    have hp : payment 150 = (5158294702189:ℝ)/1000000000000 := rfl
    have hx : (point 150+point 151)/2 = (23262353:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_150
  · change upperValue ((point 151+point 152)/2) ≤ payment 151
    have hp : payment 151 = (5147067892771:ℝ)/1000000000000 := rfl
    have hx : (point 151+point 152)/2 = (226253:ℝ)/1358848 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_151
  · change upperValue ((point 152+point 153)/2) ≤ payment 152
    have hp : payment 152 = (5135877730515:ℝ)/1000000000000 := rfl
    have hx : (point 152+point 153)/2 = (23345765:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_152
  · change upperValue ((point 153+point 154)/2) ≤ payment 153
    have hp : payment 153 = (5124724013481:ℝ)/1000000000000 := rfl
    have hx : (point 153+point 154)/2 = (23387471:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_153
  · change upperValue ((point 154+point 155)/2) ≤ payment 154
    have hp : payment 154 = (5113606541158:ℝ)/1000000000000 := rfl
    have hx : (point 154+point 155)/2 = (23429177:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_154
  · change upperValue ((point 155+point 156)/2) ≤ payment 155
    have hp : payment 155 = (5102525114445:ℝ)/1000000000000 := rfl
    have hx : (point 155+point 156)/2 = (23470883:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_155
  · change upperValue ((point 156+point 157)/2) ≤ payment 156
    have hp : payment 156 = (5091479535644:ℝ)/1000000000000 := rfl
    have hx : (point 156+point 157)/2 = (23512589:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_156
  · change upperValue ((point 157+point 158)/2) ≤ payment 157
    have hp : payment 157 = (5080469608444:ℝ)/1000000000000 := rfl
    have hx : (point 157+point 158)/2 = (23554295:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_157
  · change upperValue ((point 158+point 159)/2) ≤ payment 158
    have hp : payment 158 = (5069495137912:ℝ)/1000000000000 := rfl
    have hx : (point 158+point 159)/2 = (23596001:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_158
  · change upperValue ((point 159+point 160)/2) ≤ payment 159
    have hp : payment 159 = (5058555930476:ℝ)/1000000000000 := rfl
    have hx : (point 159+point 160)/2 = (23637707:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_159
  · change upperValue ((point 160+point 161)/2) ≤ payment 160
    have hp : payment 160 = (5047651793918:ℝ)/1000000000000 := rfl
    have hx : (point 160+point 161)/2 = (23679413:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_160
  · change upperValue ((point 161+point 162)/2) ≤ payment 161
    have hp : payment 161 = (5036782537360:ℝ)/1000000000000 := rfl
    have hx : (point 161+point 162)/2 = (23721119:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_161
  · change upperValue ((point 162+point 163)/2) ≤ payment 162
    have hp : payment 162 = (5025947971249:ℝ)/1000000000000 := rfl
    have hx : (point 162+point 163)/2 = (23762825:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_162
  · change upperValue ((point 163+point 164)/2) ≤ payment 163
    have hp : payment 163 = (5015147907353:ℝ)/1000000000000 := rfl
    have hx : (point 163+point 164)/2 = (23804531:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_163
  · change upperValue ((point 164+point 165)/2) ≤ payment 164
    have hp : payment 164 = (5004382158742:ℝ)/1000000000000 := rfl
    have hx : (point 164+point 165)/2 = (23846237:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_164
  · change upperValue ((point 165+point 166)/2) ≤ payment 165
    have hp : payment 165 = (4993650539779:ℝ)/1000000000000 := rfl
    have hx : (point 165+point 166)/2 = (23887943:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_165
  · change upperValue ((point 166+point 167)/2) ≤ payment 166
    have hp : payment 166 = (4982952866111:ℝ)/1000000000000 := rfl
    have hx : (point 166+point 167)/2 = (23929649:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_166
  · change upperValue ((point 167+point 168)/2) ≤ payment 167
    have hp : payment 167 = (4972288954656:ℝ)/1000000000000 := rfl
    have hx : (point 167+point 168)/2 = (23971355:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_167
  · change upperValue ((point 168+point 169)/2) ≤ payment 168
    have hp : payment 168 = (4961658623590:ℝ)/1000000000000 := rfl
    have hx : (point 168+point 169)/2 = (24013061:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_168
  · change upperValue ((point 169+point 170)/2) ≤ payment 169
    have hp : payment 169 = (4951061692340:ℝ)/1000000000000 := rfl
    have hx : (point 169+point 170)/2 = (24054767:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_169
  · change upperValue ((point 170+point 171)/2) ≤ payment 170
    have hp : payment 170 = (4940497981569:ℝ)/1000000000000 := rfl
    have hx : (point 170+point 171)/2 = (24096473:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_170
  · change upperValue ((point 171+point 172)/2) ≤ payment 171
    have hp : payment 171 = (4929967313171:ℝ)/1000000000000 := rfl
    have hx : (point 171+point 172)/2 = (24138179:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_171
  · change upperValue ((point 172+point 173)/2) ≤ payment 172
    have hp : payment 172 = (4919469510252:ℝ)/1000000000000 := rfl
    have hx : (point 172+point 173)/2 = (24179885:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_172
  · change upperValue ((point 173+point 174)/2) ≤ payment 173
    have hp : payment 173 = (4909004397129:ℝ)/1000000000000 := rfl
    have hx : (point 173+point 174)/2 = (24221591:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_173
  · change upperValue ((point 174+point 175)/2) ≤ payment 174
    have hp : payment 174 = (4898571799311:ℝ)/1000000000000 := rfl
    have hx : (point 174+point 175)/2 = (24263297:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_174
  · change upperValue ((point 175+point 176)/2) ≤ payment 175
    have hp : payment 175 = (4888171543495:ℝ)/1000000000000 := rfl
    have hx : (point 175+point 176)/2 = (24305003:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_175
  · change upperValue ((point 176+point 177)/2) ≤ payment 176
    have hp : payment 176 = (4877803457553:ℝ)/1000000000000 := rfl
    have hx : (point 176+point 177)/2 = (24346709:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_176
  · change upperValue ((point 177+point 178)/2) ≤ payment 177
    have hp : payment 177 = (4867467370522:ℝ)/1000000000000 := rfl
    have hx : (point 177+point 178)/2 = (24388415:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_177
  · change upperValue ((point 178+point 179)/2) ≤ payment 178
    have hp : payment 178 = (4857163112594:ℝ)/1000000000000 := rfl
    have hx : (point 178+point 179)/2 = (24430121:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_178
  · change upperValue ((point 179+point 180)/2) ≤ payment 179
    have hp : payment 179 = (4846890515107:ℝ)/1000000000000 := rfl
    have hx : (point 179+point 180)/2 = (24471827:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_179
  · change upperValue ((point 180+point 181)/2) ≤ payment 180
    have hp : payment 180 = (4836649410535:ℝ)/1000000000000 := rfl
    have hx : (point 180+point 181)/2 = (24513533:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_180
  · change upperValue ((point 181+point 182)/2) ≤ payment 181
    have hp : payment 181 = (4826439632478:ℝ)/1000000000000 := rfl
    have hx : (point 181+point 182)/2 = (24555239:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_181
  · change upperValue ((point 182+point 183)/2) ≤ payment 182
    have hp : payment 182 = (4816261015651:ℝ)/1000000000000 := rfl
    have hx : (point 182+point 183)/2 = (24596945:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_182
  · change upperValue ((point 183+point 184)/2) ≤ payment 183
    have hp : payment 183 = (4806113395878:ℝ)/1000000000000 := rfl
    have hx : (point 183+point 184)/2 = (24638651:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_183
  · change upperValue ((point 184+point 185)/2) ≤ payment 184
    have hp : payment 184 = (4795996610080:ℝ)/1000000000000 := rfl
    have hx : (point 184+point 185)/2 = (24680357:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_184
  · change upperValue ((point 185+point 186)/2) ≤ payment 185
    have hp : payment 185 = (4785910496266:ℝ)/1000000000000 := rfl
    have hx : (point 185+point 186)/2 = (24722063:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_185
  · change upperValue ((point 186+point 187)/2) ≤ payment 186
    have hp : payment 186 = (4775854893524:ℝ)/1000000000000 := rfl
    have hx : (point 186+point 187)/2 = (24763769:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_186
  · change upperValue ((point 187+point 188)/2) ≤ payment 187
    have hp : payment 187 = (4765829642012:ℝ)/1000000000000 := rfl
    have hx : (point 187+point 188)/2 = (24805475:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_187
  · change upperValue ((point 188+point 189)/2) ≤ payment 188
    have hp : payment 188 = (4755834582949:ℝ)/1000000000000 := rfl
    have hx : (point 188+point 189)/2 = (24847181:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_188
  · change upperValue ((point 189+point 190)/2) ≤ payment 189
    have hp : payment 189 = (4745869558607:ℝ)/1000000000000 := rfl
    have hx : (point 189+point 190)/2 = (24888887:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_189
  · change upperValue ((point 190+point 191)/2) ≤ payment 190
    have hp : payment 190 = (4735934412301:ℝ)/1000000000000 := rfl
    have hx : (point 190+point 191)/2 = (24930593:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_190
  · change upperValue ((point 191+point 192)/2) ≤ payment 191
    have hp : payment 191 = (4726028988379:ℝ)/1000000000000 := rfl
    have hx : (point 191+point 192)/2 = (24972299:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_191
  · change upperValue ((point 192+point 193)/2) ≤ payment 192
    have hp : payment 192 = (4716153132217:ℝ)/1000000000000 := rfl
    have hx : (point 192+point 193)/2 = (25014005:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_192
  · change upperValue ((point 193+point 194)/2) ≤ payment 193
    have hp : payment 193 = (4706306690206:ℝ)/1000000000000 := rfl
    have hx : (point 193+point 194)/2 = (25055711:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_193
  · change upperValue ((point 194+point 195)/2) ≤ payment 194
    have hp : payment 194 = (4696489509749:ℝ)/1000000000000 := rfl
    have hx : (point 194+point 195)/2 = (25097417:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_194
  · change upperValue ((point 195+point 196)/2) ≤ payment 195
    have hp : payment 195 = (4686701439246:ℝ)/1000000000000 := rfl
    have hx : (point 195+point 196)/2 = (25139123:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_195
  · change upperValue ((point 196+point 197)/2) ≤ payment 196
    have hp : payment 196 = (4676942328091:ℝ)/1000000000000 := rfl
    have hx : (point 196+point 197)/2 = (25180829:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_196
  · change upperValue ((point 197+point 198)/2) ≤ payment 197
    have hp : payment 197 = (4667212026662:ℝ)/1000000000000 := rfl
    have hx : (point 197+point 198)/2 = (25222535:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_197
  · change upperValue ((point 198+point 199)/2) ≤ payment 198
    have hp : payment 198 = (4657510386312:ℝ)/1000000000000 := rfl
    have hx : (point 198+point 199)/2 = (25264241:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_198
  · change upperValue ((point 199+point 200)/2) ≤ payment 199
    have hp : payment 199 = (4647837259362:ℝ)/1000000000000 := rfl
    have hx : (point 199+point 200)/2 = (25305947:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_199
  · change upperValue ((point 200+point 201)/2) ≤ payment 200
    have hp : payment 200 = (4638192499093:ℝ)/1000000000000 := rfl
    have hx : (point 200+point 201)/2 = (25347653:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_200
  · change upperValue ((point 201+point 202)/2) ≤ payment 201
    have hp : payment 201 = (4628575959736:ℝ)/1000000000000 := rfl
    have hx : (point 201+point 202)/2 = (25389359:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_201
  · change upperValue ((point 202+point 203)/2) ≤ payment 202
    have hp : payment 202 = (4618987496468:ℝ)/1000000000000 := rfl
    have hx : (point 202+point 203)/2 = (25431065:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_202
  · change upperValue ((point 203+point 204)/2) ≤ payment 203
    have hp : payment 203 = (4609426965401:ℝ)/1000000000000 := rfl
    have hx : (point 203+point 204)/2 = (25472771:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_203
  · change upperValue ((point 204+point 205)/2) ≤ payment 204
    have hp : payment 204 = (4599894223577:ℝ)/1000000000000 := rfl
    have hx : (point 204+point 205)/2 = (25514477:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_204
  · change upperValue ((point 205+point 206)/2) ≤ payment 205
    have hp : payment 205 = (4590389128957:ℝ)/1000000000000 := rfl
    have hx : (point 205+point 206)/2 = (25556183:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_205
  · change upperValue ((point 206+point 207)/2) ≤ payment 206
    have hp : payment 206 = (4580911540415:ℝ)/1000000000000 := rfl
    have hx : (point 206+point 207)/2 = (25597889:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_206
  · change upperValue ((point 207+point 208)/2) ≤ payment 207
    have hp : payment 207 = (4571461317734:ℝ)/1000000000000 := rfl
    have hx : (point 207+point 208)/2 = (25639595:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_207
  · change upperValue ((point 208+point 209)/2) ≤ payment 208
    have hp : payment 208 = (4562038321592:ℝ)/1000000000000 := rfl
    have hx : (point 208+point 209)/2 = (25681301:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_208
  · change upperValue ((point 209+point 210)/2) ≤ payment 209
    have hp : payment 209 = (4552642413559:ℝ)/1000000000000 := rfl
    have hx : (point 209+point 210)/2 = (25723007:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_209
  · change upperValue ((point 210+point 211)/2) ≤ payment 210
    have hp : payment 210 = (4543273456092:ℝ)/1000000000000 := rfl
    have hx : (point 210+point 211)/2 = (25764713:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_210
  · change upperValue ((point 211+point 212)/2) ≤ payment 211
    have hp : payment 211 = (4533931312520:ℝ)/1000000000000 := rfl
    have hx : (point 211+point 212)/2 = (25806419:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_211
  · change upperValue ((point 212+point 213)/2) ≤ payment 212
    have hp : payment 212 = (4524615847045:ℝ)/1000000000000 := rfl
    have hx : (point 212+point 213)/2 = (25848125:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_212
  · change upperValue ((point 213+point 214)/2) ≤ payment 213
    have hp : payment 213 = (4515326924730:ℝ)/1000000000000 := rfl
    have hx : (point 213+point 214)/2 = (25889831:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_213
  · change upperValue ((point 214+point 215)/2) ≤ payment 214
    have hp : payment 214 = (4506064411496:ℝ)/1000000000000 := rfl
    have hx : (point 214+point 215)/2 = (25931537:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_214
  · change upperValue ((point 215+point 216)/2) ≤ payment 215
    have hp : payment 215 = (4496828174108:ℝ)/1000000000000 := rfl
    have hx : (point 215+point 216)/2 = (25973243:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_215
  · change upperValue ((point 216+point 217)/2) ≤ payment 216
    have hp : payment 216 = (4487618080178:ℝ)/1000000000000 := rfl
    have hx : (point 216+point 217)/2 = (26014949:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_216
  · change upperValue ((point 217+point 218)/2) ≤ payment 217
    have hp : payment 217 = (4478433998151:ℝ)/1000000000000 := rfl
    have hx : (point 217+point 218)/2 = (26056655:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_217
  · change upperValue ((point 218+point 219)/2) ≤ payment 218
    have hp : payment 218 = (4469275797300:ℝ)/1000000000000 := rfl
    have hx : (point 218+point 219)/2 = (26098361:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_218
  · change upperValue ((point 219+point 220)/2) ≤ payment 219
    have hp : payment 219 = (4460143347721:ℝ)/1000000000000 := rfl
    have hx : (point 219+point 220)/2 = (26140067:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_219
  · change upperValue ((point 220+point 221)/2) ≤ payment 220
    have hp : payment 220 = (4451036520323:ℝ)/1000000000000 := rfl
    have hx : (point 220+point 221)/2 = (26181773:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_220
  · change upperValue ((point 221+point 222)/2) ≤ payment 221
    have hp : payment 221 = (4441955186827:ℝ)/1000000000000 := rfl
    have hx : (point 221+point 222)/2 = (26223479:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_221
  · change upperValue ((point 222+point 223)/2) ≤ payment 222
    have hp : payment 222 = (4432899219754:ℝ)/1000000000000 := rfl
    have hx : (point 222+point 223)/2 = (26265185:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_222
  · change upperValue ((point 223+point 224)/2) ≤ payment 223
    have hp : payment 223 = (4423868492420:ℝ)/1000000000000 := rfl
    have hx : (point 223+point 224)/2 = (26306891:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_223
  · change upperValue ((point 224+point 225)/2) ≤ payment 224
    have hp : payment 224 = (4414862878934:ℝ)/1000000000000 := rfl
    have hx : (point 224+point 225)/2 = (26348597:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_224
  · change upperValue ((point 225+point 226)/2) ≤ payment 225
    have hp : payment 225 = (4405882254186:ℝ)/1000000000000 := rfl
    have hx : (point 225+point 226)/2 = (26390303:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_225
  · change upperValue ((point 226+point 227)/2) ≤ payment 226
    have hp : payment 226 = (4396926493842:ℝ)/1000000000000 := rfl
    have hx : (point 226+point 227)/2 = (26432009:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_226
  · change upperValue ((point 227+point 228)/2) ≤ payment 227
    have hp : payment 227 = (4387995474341:ℝ)/1000000000000 := rfl
    have hx : (point 227+point 228)/2 = (26473715:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_227
  · change upperValue ((point 228+point 229)/2) ≤ payment 228
    have hp : payment 228 = (4379089072886:ℝ)/1000000000000 := rfl
    have hx : (point 228+point 229)/2 = (26515421:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_228
  · change upperValue ((point 229+point 230)/2) ≤ payment 229
    have hp : payment 229 = (4370207167439:ℝ)/1000000000000 := rfl
    have hx : (point 229+point 230)/2 = (26557127:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_229
  · change upperValue ((point 230+point 231)/2) ≤ payment 230
    have hp : payment 230 = (4361349636715:ℝ)/1000000000000 := rfl
    have hx : (point 230+point 231)/2 = (26598833:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_230
  · change upperValue ((point 231+point 232)/2) ≤ payment 231
    have hp : payment 231 = (4352516360174:ℝ)/1000000000000 := rfl
    have hx : (point 231+point 232)/2 = (26640539:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_231
  · change upperValue ((point 232+point 233)/2) ≤ payment 232
    have hp : payment 232 = (4343707218019:ℝ)/1000000000000 := rfl
    have hx : (point 232+point 233)/2 = (26682245:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_232
  · change upperValue ((point 233+point 234)/2) ≤ payment 233
    have hp : payment 233 = (4334922091189:ℝ)/1000000000000 := rfl
    have hx : (point 233+point 234)/2 = (26723951:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_233
  · change upperValue ((point 234+point 235)/2) ≤ payment 234
    have hp : payment 234 = (4326160861350:ℝ)/1000000000000 := rfl
    have hx : (point 234+point 235)/2 = (26765657:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_234
  · change upperValue ((point 235+point 236)/2) ≤ payment 235
    have hp : payment 235 = (4317423410893:ℝ)/1000000000000 := rfl
    have hx : (point 235+point 236)/2 = (26807363:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_235
  · change upperValue ((point 236+point 237)/2) ≤ payment 236
    have hp : payment 236 = (4308709622928:ℝ)/1000000000000 := rfl
    have hx : (point 236+point 237)/2 = (26849069:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_236
  · change upperValue ((point 237+point 238)/2) ≤ payment 237
    have hp : payment 237 = (4300019381274:ℝ)/1000000000000 := rfl
    have hx : (point 237+point 238)/2 = (26890775:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_237
  · change upperValue ((point 238+point 239)/2) ≤ payment 238
    have hp : payment 238 = (4291352570462:ℝ)/1000000000000 := rfl
    have hx : (point 238+point 239)/2 = (26932481:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_238
  · change upperValue ((point 239+point 240)/2) ≤ payment 239
    have hp : payment 239 = (4282709075720:ℝ)/1000000000000 := rfl
    have hx : (point 239+point 240)/2 = (26974187:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_239
  · change upperValue ((point 240+point 241)/2) ≤ payment 240
    have hp : payment 240 = (4274088782974:ℝ)/1000000000000 := rfl
    have hx : (point 240+point 241)/2 = (27015893:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_240
  · change upperValue ((point 241+point 242)/2) ≤ payment 241
    have hp : payment 241 = (4265491578841:ℝ)/1000000000000 := rfl
    have hx : (point 241+point 242)/2 = (27057599:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_241
  · change upperValue ((point 242+point 243)/2) ≤ payment 242
    have hp : payment 242 = (4256917350623:ℝ)/1000000000000 := rfl
    have hx : (point 242+point 243)/2 = (27099305:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_242
  · change upperValue ((point 243+point 244)/2) ≤ payment 243
    have hp : payment 243 = (4248365986301:ℝ)/1000000000000 := rfl
    have hx : (point 243+point 244)/2 = (27141011:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_243
  · change upperValue ((point 244+point 245)/2) ≤ payment 244
    have hp : payment 244 = (4239837374530:ℝ)/1000000000000 := rfl
    have hx : (point 244+point 245)/2 = (27182717:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_244
  · change upperValue ((point 245+point 246)/2) ≤ payment 245
    have hp : payment 245 = (4231331404638:ℝ)/1000000000000 := rfl
    have hx : (point 245+point 246)/2 = (27224423:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_245
  · change upperValue ((point 246+point 247)/2) ≤ payment 246
    have hp : payment 246 = (4222847966614:ℝ)/1000000000000 := rfl
    have hx : (point 246+point 247)/2 = (27266129:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_246
  · change upperValue ((point 247+point 248)/2) ≤ payment 247
    have hp : payment 247 = (4214386951107:ℝ)/1000000000000 := rfl
    have hx : (point 247+point 248)/2 = (27307835:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_247
  · change upperValue ((point 248+point 249)/2) ≤ payment 248
    have hp : payment 248 = (4205948249421:ℝ)/1000000000000 := rfl
    have hx : (point 248+point 249)/2 = (27349541:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_248
  · change upperValue ((point 249+point 250)/2) ≤ payment 249
    have hp : payment 249 = (4197531753508:ℝ)/1000000000000 := rfl
    have hx : (point 249+point 250)/2 = (27391247:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_249
  · change upperValue ((point 250+point 251)/2) ≤ payment 250
    have hp : payment 250 = (4189137355967:ℝ)/1000000000000 := rfl
    have hx : (point 250+point 251)/2 = (27432953:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_250
  · change upperValue ((point 251+point 252)/2) ≤ payment 251
    have hp : payment 251 = (4180764950031:ℝ)/1000000000000 := rfl
    have hx : (point 251+point 252)/2 = (27474659:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_251
  · change upperValue ((point 252+point 253)/2) ≤ payment 252
    have hp : payment 252 = (4172414429574:ℝ)/1000000000000 := rfl
    have hx : (point 252+point 253)/2 = (27516365:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_252
  · change upperValue ((point 253+point 254)/2) ≤ payment 253
    have hp : payment 253 = (4164085689093:ℝ)/1000000000000 := rfl
    have hx : (point 253+point 254)/2 = (27558071:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_253
  · change upperValue ((point 254+point 255)/2) ≤ payment 254
    have hp : payment 254 = (4155778623716:ℝ)/1000000000000 := rfl
    have hx : (point 254+point 255)/2 = (267959:ℝ)/1358848 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_254
  · change upperValue ((point 255+point 256)/2) ≤ payment 255
    have hp : payment 255 = (4147493129185:ℝ)/1000000000000 := rfl
    have hx : (point 255+point 256)/2 = (27641483:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_255
  · change upperValue ((point 256+point 257)/2) ≤ payment 256
    have hp : payment 256 = (4139229101863:ℝ)/1000000000000 := rfl
    have hx : (point 256+point 257)/2 = (27683189:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_256
  · change upperValue ((point 257+point 258)/2) ≤ payment 257
    have hp : payment 257 = (4130986438719:ℝ)/1000000000000 := rfl
    have hx : (point 257+point 258)/2 = (27724895:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_257
  · change upperValue ((point 258+point 259)/2) ≤ payment 258
    have hp : payment 258 = (4122765037331:ℝ)/1000000000000 := rfl
    have hx : (point 258+point 259)/2 = (27766601:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_258
  · change upperValue ((point 259+point 260)/2) ≤ payment 259
    have hp : payment 259 = (4114564795877:ℝ)/1000000000000 := rfl
    have hx : (point 259+point 260)/2 = (27808307:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_259
  · change upperValue ((point 260+point 261)/2) ≤ payment 260
    have hp : payment 260 = (4106385613133:ℝ)/1000000000000 := rfl
    have hx : (point 260+point 261)/2 = (27850013:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_260
  · change upperValue ((point 261+point 262)/2) ≤ payment 261
    have hp : payment 261 = (4098227388467:ℝ)/1000000000000 := rfl
    have hx : (point 261+point 262)/2 = (27891719:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_261
  · change upperValue ((point 262+point 263)/2) ≤ payment 262
    have hp : payment 262 = (4090090021835:ℝ)/1000000000000 := rfl
    have hx : (point 262+point 263)/2 = (27933425:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_262
  · change upperValue ((point 263+point 264)/2) ≤ payment 263
    have hp : payment 263 = (4081973413776:ℝ)/1000000000000 := rfl
    have hx : (point 263+point 264)/2 = (27975131:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_263
  · change upperValue ((point 264+point 265)/2) ≤ payment 264
    have hp : payment 264 = (4073877465409:ℝ)/1000000000000 := rfl
    have hx : (point 264+point 265)/2 = (28016837:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_264
  · change upperValue ((point 265+point 266)/2) ≤ payment 265
    have hp : payment 265 = (4065802078427:ℝ)/1000000000000 := rfl
    have hx : (point 265+point 266)/2 = (28058543:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_265
  · change upperValue ((point 266+point 267)/2) ≤ payment 266
    have hp : payment 266 = (4057747155094:ℝ)/1000000000000 := rfl
    have hx : (point 266+point 267)/2 = (28100249:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_266
  · change upperValue ((point 267+point 268)/2) ≤ payment 267
    have hp : payment 267 = (4049712598242:ℝ)/1000000000000 := rfl
    have hx : (point 267+point 268)/2 = (28141955:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_267
  · change upperValue ((point 268+point 269)/2) ≤ payment 268
    have hp : payment 268 = (4041698311262:ℝ)/1000000000000 := rfl
    have hx : (point 268+point 269)/2 = (28183661:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_268
  · change upperValue ((point 269+point 270)/2) ≤ payment 269
    have hp : payment 269 = (4033704198104:ℝ)/1000000000000 := rfl
    have hx : (point 269+point 270)/2 = (28225367:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_269
  · change upperValue ((point 270+point 271)/2) ≤ payment 270
    have hp : payment 270 = (4025730163274:ℝ)/1000000000000 := rfl
    have hx : (point 270+point 271)/2 = (28267073:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_270
  · change upperValue ((point 271+point 272)/2) ≤ payment 271
    have hp : payment 271 = (4017776111824:ℝ)/1000000000000 := rfl
    have hx : (point 271+point 272)/2 = (28308779:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_271
  · change upperValue ((point 272+point 273)/2) ≤ payment 272
    have hp : payment 272 = (4009841949354:ℝ)/1000000000000 := rfl
    have hx : (point 272+point 273)/2 = (28350485:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_272
  · change upperValue ((point 273+point 274)/2) ≤ payment 273
    have hp : payment 273 = (4001927582005:ℝ)/1000000000000 := rfl
    have hx : (point 273+point 274)/2 = (28392191:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_273
  · change upperValue ((point 274+point 275)/2) ≤ payment 274
    have hp : payment 274 = (3994032916455:ℝ)/1000000000000 := rfl
    have hx : (point 274+point 275)/2 = (28433897:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_274
  · change upperValue ((point 275+point 276)/2) ≤ payment 275
    have hp : payment 275 = (3986157859916:ℝ)/1000000000000 := rfl
    have hx : (point 275+point 276)/2 = (28475603:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_275
  · change upperValue ((point 276+point 277)/2) ≤ payment 276
    have hp : payment 276 = (3978302320129:ℝ)/1000000000000 := rfl
    have hx : (point 276+point 277)/2 = (28517309:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_276
  · change upperValue ((point 277+point 278)/2) ≤ payment 277
    have hp : payment 277 = (3970466205362:ℝ)/1000000000000 := rfl
    have hx : (point 277+point 278)/2 = (28559015:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_277
  · change upperValue ((point 278+point 279)/2) ≤ payment 278
    have hp : payment 278 = (3962649424404:ℝ)/1000000000000 := rfl
    have hx : (point 278+point 279)/2 = (28600721:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_278
  · change upperValue ((point 279+point 280)/2) ≤ payment 279
    have hp : payment 279 = (3954851886561:ℝ)/1000000000000 := rfl
    have hx : (point 279+point 280)/2 = (28642427:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_279
  · change upperValue ((point 280+point 281)/2) ≤ payment 280
    have hp : payment 280 = (3947073501655:ℝ)/1000000000000 := rfl
    have hx : (point 280+point 281)/2 = (28684133:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_280
  · change upperValue ((point 281+point 282)/2) ≤ payment 281
    have hp : payment 281 = (3939314180017:ℝ)/1000000000000 := rfl
    have hx : (point 281+point 282)/2 = (28725839:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_281
  · change upperValue ((point 282+point 283)/2) ≤ payment 282
    have hp : payment 282 = (3931573832487:ℝ)/1000000000000 := rfl
    have hx : (point 282+point 283)/2 = (28767545:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_282
  · change upperValue ((point 283+point 284)/2) ≤ payment 283
    have hp : payment 283 = (3923852370404:ℝ)/1000000000000 := rfl
    have hx : (point 283+point 284)/2 = (28809251:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_283
  · change upperValue ((point 284+point 285)/2) ≤ payment 284
    have hp : payment 284 = (3916149705611:ℝ)/1000000000000 := rfl
    have hx : (point 284+point 285)/2 = (28850957:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_284
  · change upperValue ((point 285+point 286)/2) ≤ payment 285
    have hp : payment 285 = (3908465750443:ℝ)/1000000000000 := rfl
    have hx : (point 285+point 286)/2 = (28892663:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_285
  · change upperValue ((point 286+point 287)/2) ≤ payment 286
    have hp : payment 286 = (3900800417729:ℝ)/1000000000000 := rfl
    have hx : (point 286+point 287)/2 = (28934369:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_286
  · change upperValue ((point 287+point 288)/2) ≤ payment 287
    have hp : payment 287 = (3893153620785:ℝ)/1000000000000 := rfl
    have hx : (point 287+point 288)/2 = (28976075:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_287
  · change upperValue ((point 288+point 289)/2) ≤ payment 288
    have hp : payment 288 = (3885525273415:ℝ)/1000000000000 := rfl
    have hx : (point 288+point 289)/2 = (29017781:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_288
  · change upperValue ((point 289+point 290)/2) ≤ payment 289
    have hp : payment 289 = (3877915289900:ℝ)/1000000000000 := rfl
    have hx : (point 289+point 290)/2 = (29059487:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_289
  · change upperValue ((point 290+point 291)/2) ≤ payment 290
    have hp : payment 290 = (3870323585004:ℝ)/1000000000000 := rfl
    have hx : (point 290+point 291)/2 = (29101193:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_290
  · change upperValue ((point 291+point 292)/2) ≤ payment 291
    have hp : payment 291 = (3862750073961:ℝ)/1000000000000 := rfl
    have hx : (point 291+point 292)/2 = (29142899:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_291
  · change upperValue ((point 292+point 293)/2) ≤ payment 292
    have hp : payment 292 = (3855194672478:ℝ)/1000000000000 := rfl
    have hx : (point 292+point 293)/2 = (29184605:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_292
  · change upperValue ((point 293+point 294)/2) ≤ payment 293
    have hp : payment 293 = (3847657296731:ℝ)/1000000000000 := rfl
    have hx : (point 293+point 294)/2 = (29226311:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_293
  · change upperValue ((point 294+point 295)/2) ≤ payment 294
    have hp : payment 294 = (3840137863358:ℝ)/1000000000000 := rfl
    have hx : (point 294+point 295)/2 = (29268017:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_294
  · change upperValue ((point 295+point 296)/2) ≤ payment 295
    have hp : payment 295 = (3832636289459:ℝ)/1000000000000 := rfl
    have hx : (point 295+point 296)/2 = (29309723:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_295
  · change upperValue ((point 296+point 297)/2) ≤ payment 296
    have hp : payment 296 = (3825152492592:ℝ)/1000000000000 := rfl
    have hx : (point 296+point 297)/2 = (29351429:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_296
  · change upperValue ((point 297+point 298)/2) ≤ payment 297
    have hp : payment 297 = (3817686390769:ℝ)/1000000000000 := rfl
    have hx : (point 297+point 298)/2 = (29393135:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_297
  · change upperValue ((point 298+point 299)/2) ≤ payment 298
    have hp : payment 298 = (3810237902454:ℝ)/1000000000000 := rfl
    have hx : (point 298+point 299)/2 = (29434841:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_298
  · change upperValue ((point 299+point 300)/2) ≤ payment 299
    have hp : payment 299 = (3802806946557:ℝ)/1000000000000 := rfl
    have hx : (point 299+point 300)/2 = (29476547:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_299
  · change upperValue ((point 300+point 301)/2) ≤ payment 300
    have hp : payment 300 = (3795393442434:ℝ)/1000000000000 := rfl
    have hx : (point 300+point 301)/2 = (29518253:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_300
  · change upperValue ((point 301+point 302)/2) ≤ payment 301
    have hp : payment 301 = (3787997309883:ℝ)/1000000000000 := rfl
    have hx : (point 301+point 302)/2 = (29559959:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_301
  · change upperValue ((point 302+point 303)/2) ≤ payment 302
    have hp : payment 302 = (3780618469140:ℝ)/1000000000000 := rfl
    have hx : (point 302+point 303)/2 = (29601665:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_302
  · change upperValue ((point 303+point 304)/2) ≤ payment 303
    have hp : payment 303 = (3773256840876:ℝ)/1000000000000 := rfl
    have hx : (point 303+point 304)/2 = (29643371:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_303
  · change upperValue ((point 304+point 305)/2) ≤ payment 304
    have hp : payment 304 = (3765912346194:ℝ)/1000000000000 := rfl
    have hx : (point 304+point 305)/2 = (29685077:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_304
  · change upperValue ((point 305+point 306)/2) ≤ payment 305
    have hp : payment 305 = (3758584906626:ℝ)/1000000000000 := rfl
    have hx : (point 305+point 306)/2 = (29726783:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_305
  · change upperValue ((point 306+point 307)/2) ≤ payment 306
    have hp : payment 306 = (3751274444131:ℝ)/1000000000000 := rfl
    have hx : (point 306+point 307)/2 = (29768489:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_306
  · change upperValue ((point 307+point 308)/2) ≤ payment 307
    have hp : payment 307 = (3743980881091:ℝ)/1000000000000 := rfl
    have hx : (point 307+point 308)/2 = (29810195:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_307
  · change upperValue ((point 308+point 309)/2) ≤ payment 308
    have hp : payment 308 = (3736704140307:ℝ)/1000000000000 := rfl
    have hx : (point 308+point 309)/2 = (29851901:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_308
  · change upperValue ((point 309+point 310)/2) ≤ payment 309
    have hp : payment 309 = (3729444144998:ℝ)/1000000000000 := rfl
    have hx : (point 309+point 310)/2 = (29893607:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_309
  · change upperValue ((point 310+point 311)/2) ≤ payment 310
    have hp : payment 310 = (3722200818797:ℝ)/1000000000000 := rfl
    have hx : (point 310+point 311)/2 = (29935313:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_310
  · change upperValue ((point 311+point 312)/2) ≤ payment 311
    have hp : payment 311 = (3714974085748:ℝ)/1000000000000 := rfl
    have hx : (point 311+point 312)/2 = (29977019:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_311
  · change upperValue ((point 312+point 313)/2) ≤ payment 312
    have hp : payment 312 = (3707763870304:ℝ)/1000000000000 := rfl
    have hx : (point 312+point 313)/2 = (30018725:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_312
  · change upperValue ((point 313+point 314)/2) ≤ payment 313
    have hp : payment 313 = (3700570097322:ℝ)/1000000000000 := rfl
    have hx : (point 313+point 314)/2 = (30060431:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_313
  · change upperValue ((point 314+point 315)/2) ≤ payment 314
    have hp : payment 314 = (3693392692064:ℝ)/1000000000000 := rfl
    have hx : (point 314+point 315)/2 = (30102137:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_314
  · change upperValue ((point 315+point 316)/2) ≤ payment 315
    have hp : payment 315 = (3686231580190:ℝ)/1000000000000 := rfl
    have hx : (point 315+point 316)/2 = (30143843:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_315
  · change upperValue ((point 316+point 317)/2) ≤ payment 316
    have hp : payment 316 = (3679086687758:ℝ)/1000000000000 := rfl
    have hx : (point 316+point 317)/2 = (30185549:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_316
  · change upperValue ((point 317+point 318)/2) ≤ payment 317
    have hp : payment 317 = (3671957941218:ℝ)/1000000000000 := rfl
    have hx : (point 317+point 318)/2 = (30227255:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_317
  · change upperValue ((point 318+point 319)/2) ≤ payment 318
    have hp : payment 318 = (3664845267416:ℝ)/1000000000000 := rfl
    have hx : (point 318+point 319)/2 = (30268961:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_318
  · change upperValue ((point 319+point 320)/2) ≤ payment 319
    have hp : payment 319 = (3657748593582:ℝ)/1000000000000 := rfl
    have hx : (point 319+point 320)/2 = (30310667:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_319
  · change upperValue ((point 320+point 321)/2) ≤ payment 320
    have hp : payment 320 = (3650667847334:ℝ)/1000000000000 := rfl
    have hx : (point 320+point 321)/2 = (30352373:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_320
  · change upperValue ((point 321+point 322)/2) ≤ payment 321
    have hp : payment 321 = (3643602956676:ℝ)/1000000000000 := rfl
    have hx : (point 321+point 322)/2 = (30394079:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_321
  · change upperValue ((point 322+point 323)/2) ≤ payment 322
    have hp : payment 322 = (3636553849987:ℝ)/1000000000000 := rfl
    have hx : (point 322+point 323)/2 = (30435785:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_322
  · change upperValue ((point 323+point 324)/2) ≤ payment 323
    have hp : payment 323 = (3629520456030:ℝ)/1000000000000 := rfl
    have hx : (point 323+point 324)/2 = (30477491:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_323
  · change upperValue ((point 324+point 325)/2) ≤ payment 324
    have hp : payment 324 = (3622502703939:ℝ)/1000000000000 := rfl
    have hx : (point 324+point 325)/2 = (30519197:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_324
  · change upperValue ((point 325+point 326)/2) ≤ payment 325
    have hp : payment 325 = (3615500523224:ℝ)/1000000000000 := rfl
    have hx : (point 325+point 326)/2 = (30560903:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_325
  · change upperValue ((point 326+point 327)/2) ≤ payment 326
    have hp : payment 326 = (3608513843763:ℝ)/1000000000000 := rfl
    have hx : (point 326+point 327)/2 = (30602609:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_326
  · change upperValue ((point 327+point 328)/2) ≤ payment 327
    have hp : payment 327 = (3601542595802:ℝ)/1000000000000 := rfl
    have hx : (point 327+point 328)/2 = (30644315:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_327
  · change upperValue ((point 328+point 329)/2) ≤ payment 328
    have hp : payment 328 = (3594586709955:ℝ)/1000000000000 := rfl
    have hx : (point 328+point 329)/2 = (30686021:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_328
  · change upperValue ((point 329+point 330)/2) ≤ payment 329
    have hp : payment 329 = (3587646117194:ℝ)/1000000000000 := rfl
    have hx : (point 329+point 330)/2 = (30727727:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_329
  · change upperValue ((point 330+point 331)/2) ≤ payment 330
    have hp : payment 330 = (3580720748856:ℝ)/1000000000000 := rfl
    have hx : (point 330+point 331)/2 = (30769433:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_330
  · change upperValue ((point 331+point 332)/2) ≤ payment 331
    have hp : payment 331 = (3573810536632:ℝ)/1000000000000 := rfl
    have hx : (point 331+point 332)/2 = (30811139:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_331
  · change upperValue ((point 332+point 333)/2) ≤ payment 332
    have hp : payment 332 = (3566915412570:ℝ)/1000000000000 := rfl
    have hx : (point 332+point 333)/2 = (30852845:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_332
  · change upperValue ((point 333+point 334)/2) ≤ payment 333
    have hp : payment 333 = (3560035309070:ℝ)/1000000000000 := rfl
    have hx : (point 333+point 334)/2 = (30894551:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_333
  · change upperValue ((point 334+point 335)/2) ≤ payment 334
    have hp : payment 334 = (3553170158883:ℝ)/1000000000000 := rfl
    have hx : (point 334+point 335)/2 = (30936257:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_334
  · change upperValue ((point 335+point 336)/2) ≤ payment 335
    have hp : payment 335 = (3546319895109:ℝ)/1000000000000 := rfl
    have hx : (point 335+point 336)/2 = (30977963:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_335
  · change upperValue ((point 336+point 337)/2) ≤ payment 336
    have hp : payment 336 = (3539484451192:ℝ)/1000000000000 := rfl
    have hx : (point 336+point 337)/2 = (31019669:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_336
  · change upperValue ((point 337+point 338)/2) ≤ payment 337
    have hp : payment 337 = (3532663760919:ℝ)/1000000000000 := rfl
    have hx : (point 337+point 338)/2 = (31061375:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_337
  · change upperValue ((point 338+point 339)/2) ≤ payment 338
    have hp : payment 338 = (3525857758419:ℝ)/1000000000000 := rfl
    have hx : (point 338+point 339)/2 = (31103081:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_338
  · change upperValue ((point 339+point 340)/2) ≤ payment 339
    have hp : payment 339 = (3519066378159:ℝ)/1000000000000 := rfl
    have hx : (point 339+point 340)/2 = (31144787:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_339
  · change upperValue ((point 340+point 341)/2) ≤ payment 340
    have hp : payment 340 = (3512289554944:ℝ)/1000000000000 := rfl
    have hx : (point 340+point 341)/2 = (31186493:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_340
  · change upperValue ((point 341+point 342)/2) ≤ payment 341
    have hp : payment 341 = (3505527223911:ℝ)/1000000000000 := rfl
    have hx : (point 341+point 342)/2 = (31228199:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_341
  · change upperValue ((point 342+point 343)/2) ≤ payment 342
    have hp : payment 342 = (3498779320529:ℝ)/1000000000000 := rfl
    have hx : (point 342+point 343)/2 = (31269905:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_342
  · change upperValue ((point 343+point 344)/2) ≤ payment 343
    have hp : payment 343 = (3492045780598:ℝ)/1000000000000 := rfl
    have hx : (point 343+point 344)/2 = (31311611:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_343
  · change upperValue ((point 344+point 345)/2) ≤ payment 344
    have hp : payment 344 = (3485326540242:ℝ)/1000000000000 := rfl
    have hx : (point 344+point 345)/2 = (31353317:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_344
  · change upperValue ((point 345+point 346)/2) ≤ payment 345
    have hp : payment 345 = (3478621535915:ℝ)/1000000000000 := rfl
    have hx : (point 345+point 346)/2 = (31395023:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_345
  · change upperValue ((point 346+point 347)/2) ≤ payment 346
    have hp : payment 346 = (3471930704390:ℝ)/1000000000000 := rfl
    have hx : (point 346+point 347)/2 = (31436729:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_346
  · change upperValue ((point 347+point 348)/2) ≤ payment 347
    have hp : payment 347 = (3465253982762:ℝ)/1000000000000 := rfl
    have hx : (point 347+point 348)/2 = (31478435:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_347
  · change upperValue ((point 348+point 349)/2) ≤ payment 348
    have hp : payment 348 = (3458591308444:ℝ)/1000000000000 := rfl
    have hx : (point 348+point 349)/2 = (31520141:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_348
  · change upperValue ((point 349+point 350)/2) ≤ payment 349
    have hp : payment 349 = (3451942619167:ℝ)/1000000000000 := rfl
    have hx : (point 349+point 350)/2 = (31561847:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_349
  · change upperValue ((point 350+point 351)/2) ≤ payment 350
    have hp : payment 350 = (3445307852974:ℝ)/1000000000000 := rfl
    have hx : (point 350+point 351)/2 = (31603553:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_350
  · change upperValue ((point 351+point 352)/2) ≤ payment 351
    have hp : payment 351 = (3438686948222:ℝ)/1000000000000 := rfl
    have hx : (point 351+point 352)/2 = (31645259:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_351
  · change upperValue ((point 352+point 353)/2) ≤ payment 352
    have hp : payment 352 = (3432079843577:ℝ)/1000000000000 := rfl
    have hx : (point 352+point 353)/2 = (31686965:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_352
  · change upperValue ((point 353+point 354)/2) ≤ payment 353
    have hp : payment 353 = (3425486478014:ℝ)/1000000000000 := rfl
    have hx : (point 353+point 354)/2 = (31728671:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_353
  · change upperValue ((point 354+point 355)/2) ≤ payment 354
    have hp : payment 354 = (3418906790813:ℝ)/1000000000000 := rfl
    have hx : (point 354+point 355)/2 = (31770377:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_354
  · change upperValue ((point 355+point 356)/2) ≤ payment 355
    have hp : payment 355 = (3412340721558:ℝ)/1000000000000 := rfl
    have hx : (point 355+point 356)/2 = (31812083:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_355
  · change upperValue ((point 356+point 357)/2) ≤ payment 356
    have hp : payment 356 = (3405788210136:ℝ)/1000000000000 := rfl
    have hx : (point 356+point 357)/2 = (31853789:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_356
  · change upperValue ((point 357+point 358)/2) ≤ payment 357
    have hp : payment 357 = (3399249196732:ℝ)/1000000000000 := rfl
    have hx : (point 357+point 358)/2 = (309665:ℝ)/1358848 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_357
  · change upperValue ((point 358+point 359)/2) ≤ payment 358
    have hp : payment 358 = (3392723621830:ℝ)/1000000000000 := rfl
    have hx : (point 358+point 359)/2 = (31937201:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_358
  · change upperValue ((point 359+point 360)/2) ≤ payment 359
    have hp : payment 359 = (3386211426210:ℝ)/1000000000000 := rfl
    have hx : (point 359+point 360)/2 = (31978907:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_359
  · change upperValue ((point 360+point 361)/2) ≤ payment 360
    have hp : payment 360 = (3379712550945:ℝ)/1000000000000 := rfl
    have hx : (point 360+point 361)/2 = (32020613:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_360
  · change upperValue ((point 361+point 362)/2) ≤ payment 361
    have hp : payment 361 = (3373226937402:ℝ)/1000000000000 := rfl
    have hx : (point 361+point 362)/2 = (32062319:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_361
  · change upperValue ((point 362+point 363)/2) ≤ payment 362
    have hp : payment 362 = (3366754527235:ℝ)/1000000000000 := rfl
    have hx : (point 362+point 363)/2 = (32104025:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_362
  · change upperValue ((point 363+point 364)/2) ≤ payment 363
    have hp : payment 363 = (3360295262389:ℝ)/1000000000000 := rfl
    have hx : (point 363+point 364)/2 = (32145731:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_363
  · change upperValue ((point 364+point 365)/2) ≤ payment 364
    have hp : payment 364 = (3353849085094:ℝ)/1000000000000 := rfl
    have hx : (point 364+point 365)/2 = (32187437:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_364
  · change upperValue ((point 365+point 366)/2) ≤ payment 365
    have hp : payment 365 = (3347415937863:ℝ)/1000000000000 := rfl
    have hx : (point 365+point 366)/2 = (32229143:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_365
  · change upperValue ((point 366+point 367)/2) ≤ payment 366
    have hp : payment 366 = (3340995763494:ℝ)/1000000000000 := rfl
    have hx : (point 366+point 367)/2 = (32270849:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_366
  · change upperValue ((point 367+point 368)/2) ≤ payment 367
    have hp : payment 367 = (3334588505064:ℝ)/1000000000000 := rfl
    have hx : (point 367+point 368)/2 = (32312555:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_367
  · change upperValue ((point 368+point 369)/2) ≤ payment 368
    have hp : payment 368 = (3328194105928:ℝ)/1000000000000 := rfl
    have hx : (point 368+point 369)/2 = (32354261:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_368
  · change upperValue ((point 369+point 370)/2) ≤ payment 369
    have hp : payment 369 = (3321812509720:ℝ)/1000000000000 := rfl
    have hx : (point 369+point 370)/2 = (32395967:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_369
  · change upperValue ((point 370+point 371)/2) ≤ payment 370
    have hp : payment 370 = (3315443660348:ℝ)/1000000000000 := rfl
    have hx : (point 370+point 371)/2 = (32437673:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_370
  · change upperValue ((point 371+point 372)/2) ≤ payment 371
    have hp : payment 371 = (3309087501992:ℝ)/1000000000000 := rfl
    have hx : (point 371+point 372)/2 = (32479379:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_371
  · change upperValue ((point 372+point 373)/2) ≤ payment 372
    have hp : payment 372 = (3302743979107:ℝ)/1000000000000 := rfl
    have hx : (point 372+point 373)/2 = (32521085:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_372
  · change upperValue ((point 373+point 374)/2) ≤ payment 373
    have hp : payment 373 = (3296413036413:ℝ)/1000000000000 := rfl
    have hx : (point 373+point 374)/2 = (32562791:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_373
  · change upperValue ((point 374+point 375)/2) ≤ payment 374
    have hp : payment 374 = (3290094618902:ℝ)/1000000000000 := rfl
    have hx : (point 374+point 375)/2 = (32604497:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_374
  · change upperValue ((point 375+point 376)/2) ≤ payment 375
    have hp : payment 375 = (3283788671830:ℝ)/1000000000000 := rfl
    have hx : (point 375+point 376)/2 = (32646203:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_375
  · change upperValue ((point 376+point 377)/2) ≤ payment 376
    have hp : payment 376 = (3277495140718:ℝ)/1000000000000 := rfl
    have hx : (point 376+point 377)/2 = (32687909:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_376
  · change upperValue ((point 377+point 378)/2) ≤ payment 377
    have hp : payment 377 = (3271213971350:ℝ)/1000000000000 := rfl
    have hx : (point 377+point 378)/2 = (32729615:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_377
  · change upperValue ((point 378+point 379)/2) ≤ payment 378
    have hp : payment 378 = (3264945109770:ℝ)/1000000000000 := rfl
    have hx : (point 378+point 379)/2 = (32771321:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_378
  · change upperValue ((point 379+point 380)/2) ≤ payment 379
    have hp : payment 379 = (3258688502283:ℝ)/1000000000000 := rfl
    have hx : (point 379+point 380)/2 = (32813027:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_379
  · change upperValue ((point 380+point 381)/2) ≤ payment 380
    have hp : payment 380 = (3252444095450:ℝ)/1000000000000 := rfl
    have hx : (point 380+point 381)/2 = (32854733:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_380
  · change upperValue ((point 381+point 382)/2) ≤ payment 381
    have hp : payment 381 = (3246211836089:ℝ)/1000000000000 := rfl
    have hx : (point 381+point 382)/2 = (32896439:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_381
  · change upperValue ((point 382+point 383)/2) ≤ payment 382
    have hp : payment 382 = (3239991671272:ℝ)/1000000000000 := rfl
    have hx : (point 382+point 383)/2 = (32938145:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_382
  · change upperValue ((point 383+point 384)/2) ≤ payment 383
    have hp : payment 383 = (3233783548323:ℝ)/1000000000000 := rfl
    have hx : (point 383+point 384)/2 = (32979851:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_383
  · change upperValue ((point 384+point 385)/2) ≤ payment 384
    have hp : payment 384 = (3227587414819:ℝ)/1000000000000 := rfl
    have hx : (point 384+point 385)/2 = (33021557:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_384
  · change upperValue ((point 385+point 386)/2) ≤ payment 385
    have hp : payment 385 = (3221403218583:ℝ)/1000000000000 := rfl
    have hx : (point 385+point 386)/2 = (33063263:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_385
  · change upperValue ((point 386+point 387)/2) ≤ payment 386
    have hp : payment 386 = (3215230907688:ℝ)/1000000000000 := rfl
    have hx : (point 386+point 387)/2 = (33104969:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_386
  · change upperValue ((point 387+point 388)/2) ≤ payment 387
    have hp : payment 387 = (3209070430455:ℝ)/1000000000000 := rfl
    have hx : (point 387+point 388)/2 = (33146675:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_387
  · change upperValue ((point 388+point 389)/2) ≤ payment 388
    have hp : payment 388 = (3202921735445:ℝ)/1000000000000 := rfl
    have hx : (point 388+point 389)/2 = (33188381:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_388
  · change upperValue ((point 389+point 390)/2) ≤ payment 389
    have hp : payment 389 = (3196784771466:ℝ)/1000000000000 := rfl
    have hx : (point 389+point 390)/2 = (33230087:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_389
  · change upperValue ((point 390+point 391)/2) ≤ payment 390
    have hp : payment 390 = (3190659487566:ℝ)/1000000000000 := rfl
    have hx : (point 390+point 391)/2 = (33271793:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_390
  · change upperValue ((point 391+point 392)/2) ≤ payment 391
    have hp : payment 391 = (3184545833032:ℝ)/1000000000000 := rfl
    have hx : (point 391+point 392)/2 = (33313499:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_391
  · change upperValue ((point 392+point 393)/2) ≤ payment 392
    have hp : payment 392 = (3178443757390:ℝ)/1000000000000 := rfl
    have hx : (point 392+point 393)/2 = (33355205:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_392
  · change upperValue ((point 393+point 394)/2) ≤ payment 393
    have hp : payment 393 = (3172353210404:ℝ)/1000000000000 := rfl
    have hx : (point 393+point 394)/2 = (33396911:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_393
  · change upperValue ((point 394+point 395)/2) ≤ payment 394
    have hp : payment 394 = (3166274142073:ℝ)/1000000000000 := rfl
    have hx : (point 394+point 395)/2 = (33438617:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_394
  · change upperValue ((point 395+point 396)/2) ≤ payment 395
    have hp : payment 395 = (3160206502627:ℝ)/1000000000000 := rfl
    have hx : (point 395+point 396)/2 = (33480323:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_395
  · change upperValue ((point 396+point 397)/2) ≤ payment 396
    have hp : payment 396 = (3154150242532:ℝ)/1000000000000 := rfl
    have hx : (point 396+point 397)/2 = (33522029:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_396
  · change upperValue ((point 397+point 398)/2) ≤ payment 397
    have hp : payment 397 = (3148105312482:ℝ)/1000000000000 := rfl
    have hx : (point 397+point 398)/2 = (33563735:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_397
  · change upperValue ((point 398+point 399)/2) ≤ payment 398
    have hp : payment 398 = (3142071663404:ℝ)/1000000000000 := rfl
    have hx : (point 398+point 399)/2 = (33605441:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_398
  · change upperValue ((point 399+point 400)/2) ≤ payment 399
    have hp : payment 399 = (3136049246448:ℝ)/1000000000000 := rfl
    have hx : (point 399+point 400)/2 = (33647147:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_399
  · change upperValue ((point 400+point 401)/2) ≤ payment 400
    have hp : payment 400 = (3130038012994:ℝ)/1000000000000 := rfl
    have hx : (point 400+point 401)/2 = (33688853:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_400
  · change upperValue ((point 401+point 402)/2) ≤ payment 401
    have hp : payment 401 = (3124037914645:ℝ)/1000000000000 := rfl
    have hx : (point 401+point 402)/2 = (33730559:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_401
  · change upperValue ((point 402+point 403)/2) ≤ payment 402
    have hp : payment 402 = (3118048903230:ℝ)/1000000000000 := rfl
    have hx : (point 402+point 403)/2 = (33772265:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_402
  · change upperValue ((point 403+point 404)/2) ≤ payment 403
    have hp : payment 403 = (3112070930798:ℝ)/1000000000000 := rfl
    have hx : (point 403+point 404)/2 = (33813971:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_403
  · change upperValue ((point 404+point 405)/2) ≤ payment 404
    have hp : payment 404 = (3106103949619:ℝ)/1000000000000 := rfl
    have hx : (point 404+point 405)/2 = (33855677:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_404
  · change upperValue ((point 405+point 406)/2) ≤ payment 405
    have hp : payment 405 = (3100147912183:ℝ)/1000000000000 := rfl
    have hx : (point 405+point 406)/2 = (33897383:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_405
  · change upperValue ((point 406+point 407)/2) ≤ payment 406
    have hp : payment 406 = (3094202771198:ℝ)/1000000000000 := rfl
    have hx : (point 406+point 407)/2 = (33939089:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_406
  · change upperValue ((point 407+point 408)/2) ≤ payment 407
    have hp : payment 407 = (3088268479587:ℝ)/1000000000000 := rfl
    have hx : (point 407+point 408)/2 = (33980795:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_407
  · change upperValue ((point 408+point 409)/2) ≤ payment 408
    have hp : payment 408 = (3082344990490:ℝ)/1000000000000 := rfl
    have hx : (point 408+point 409)/2 = (34022501:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_408
  · change upperValue ((point 409+point 410)/2) ≤ payment 409
    have hp : payment 409 = (3076432257260:ℝ)/1000000000000 := rfl
    have hx : (point 409+point 410)/2 = (34064207:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_409
  · change upperValue ((point 410+point 411)/2) ≤ payment 410
    have hp : payment 410 = (3070530233464:ℝ)/1000000000000 := rfl
    have hx : (point 410+point 411)/2 = (34105913:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_410
  · change upperValue ((point 411+point 412)/2) ≤ payment 411
    have hp : payment 411 = (3064638872877:ℝ)/1000000000000 := rfl
    have hx : (point 411+point 412)/2 = (34147619:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_411
  · change upperValue ((point 412+point 413)/2) ≤ payment 412
    have hp : payment 412 = (3058758129486:ℝ)/1000000000000 := rfl
    have hx : (point 412+point 413)/2 = (34189325:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_412
  · change upperValue ((point 413+point 414)/2) ≤ payment 413
    have hp : payment 413 = (3052887957486:ℝ)/1000000000000 := rfl
    have hx : (point 413+point 414)/2 = (34231031:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_413
  · change upperValue ((point 414+point 415)/2) ≤ payment 414
    have hp : payment 414 = (3047028311281:ℝ)/1000000000000 := rfl
    have hx : (point 414+point 415)/2 = (34272737:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_414
  · change upperValue ((point 415+point 416)/2) ≤ payment 415
    have hp : payment 415 = (3041179145477:ℝ)/1000000000000 := rfl
    have hx : (point 415+point 416)/2 = (34314443:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_415
  · change upperValue ((point 416+point 417)/2) ≤ payment 416
    have hp : payment 416 = (3035340414887:ℝ)/1000000000000 := rfl
    have hx : (point 416+point 417)/2 = (34356149:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_416
  · change upperValue ((point 417+point 418)/2) ≤ payment 417
    have hp : payment 417 = (3029512074528:ℝ)/1000000000000 := rfl
    have hx : (point 417+point 418)/2 = (34397855:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_417
  · change upperValue ((point 418+point 419)/2) ≤ payment 418
    have hp : payment 418 = (3023694079618:ℝ)/1000000000000 := rfl
    have hx : (point 418+point 419)/2 = (34439561:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_418
  · change upperValue ((point 419+point 420)/2) ≤ payment 419
    have hp : payment 419 = (3017886385576:ℝ)/1000000000000 := rfl
    have hx : (point 419+point 420)/2 = (34481267:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_419
  · change upperValue ((point 420+point 421)/2) ≤ payment 420
    have hp : payment 420 = (3012088948019:ℝ)/1000000000000 := rfl
    have hx : (point 420+point 421)/2 = (34522973:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_420
  · change upperValue ((point 421+point 422)/2) ≤ payment 421
    have hp : payment 421 = (3006301722764:ℝ)/1000000000000 := rfl
    have hx : (point 421+point 422)/2 = (34564679:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_421
  · change upperValue ((point 422+point 423)/2) ≤ payment 422
    have hp : payment 422 = (3000524665826:ℝ)/1000000000000 := rfl
    have hx : (point 422+point 423)/2 = (34606385:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_422
  · change upperValue ((point 423+point 424)/2) ≤ payment 423
    have hp : payment 423 = (2994757733413:ℝ)/1000000000000 := rfl
    have hx : (point 423+point 424)/2 = (34648091:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_423
  · change upperValue ((point 424+point 425)/2) ≤ payment 424
    have hp : payment 424 = (2989000881929:ℝ)/1000000000000 := rfl
    have hx : (point 424+point 425)/2 = (34689797:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_424
  · change upperValue ((point 425+point 426)/2) ≤ payment 425
    have hp : payment 425 = (2983254067972:ℝ)/1000000000000 := rfl
    have hx : (point 425+point 426)/2 = (34731503:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_425
  · change upperValue ((point 426+point 427)/2) ≤ payment 426
    have hp : payment 426 = (2977517248331:ℝ)/1000000000000 := rfl
    have hx : (point 426+point 427)/2 = (34773209:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_426
  · change upperValue ((point 427+point 428)/2) ≤ payment 427
    have hp : payment 427 = (2971790379986:ℝ)/1000000000000 := rfl
    have hx : (point 427+point 428)/2 = (34814915:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_427
  · change upperValue ((point 428+point 429)/2) ≤ payment 428
    have hp : payment 428 = (2966073420109:ℝ)/1000000000000 := rfl
    have hx : (point 428+point 429)/2 = (34856621:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_428
  · change upperValue ((point 429+point 430)/2) ≤ payment 429
    have hp : payment 429 = (2960366326056:ℝ)/1000000000000 := rfl
    have hx : (point 429+point 430)/2 = (34898327:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_429
  · change upperValue ((point 430+point 431)/2) ≤ payment 430
    have hp : payment 430 = (2954669055376:ℝ)/1000000000000 := rfl
    have hx : (point 430+point 431)/2 = (34940033:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_430
  · change upperValue ((point 431+point 432)/2) ≤ payment 431
    have hp : payment 431 = (2948981565800:ℝ)/1000000000000 := rfl
    have hx : (point 431+point 432)/2 = (34981739:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_431
  · change upperValue ((point 432+point 433)/2) ≤ payment 432
    have hp : payment 432 = (2943303815246:ℝ)/1000000000000 := rfl
    have hx : (point 432+point 433)/2 = (35023445:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_432
  · change upperValue ((point 433+point 434)/2) ≤ payment 433
    have hp : payment 433 = (2937635761815:ℝ)/1000000000000 := rfl
    have hx : (point 433+point 434)/2 = (35065151:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_433
  · change upperValue ((point 434+point 435)/2) ≤ payment 434
    have hp : payment 434 = (2931977363792:ℝ)/1000000000000 := rfl
    have hx : (point 434+point 435)/2 = (35106857:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_434
  · change upperValue ((point 435+point 436)/2) ≤ payment 435
    have hp : payment 435 = (2926328579643:ℝ)/1000000000000 := rfl
    have hx : (point 435+point 436)/2 = (35148563:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_435
  · change upperValue ((point 436+point 437)/2) ≤ payment 436
    have hp : payment 436 = (2920689368014:ℝ)/1000000000000 := rfl
    have hx : (point 436+point 437)/2 = (35190269:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_436
  · change upperValue ((point 437+point 438)/2) ≤ payment 437
    have hp : payment 437 = (2915059687733:ℝ)/1000000000000 := rfl
    have hx : (point 437+point 438)/2 = (35231975:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_437
  · change upperValue ((point 438+point 439)/2) ≤ payment 438
    have hp : payment 438 = (2909439497802:ℝ)/1000000000000 := rfl
    have hx : (point 438+point 439)/2 = (35273681:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_438
  · change upperValue ((point 439+point 440)/2) ≤ payment 439
    have hp : payment 439 = (2903828757404:ℝ)/1000000000000 := rfl
    have hx : (point 439+point 440)/2 = (35315387:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_439
  · change upperValue ((point 440+point 441)/2) ≤ payment 440
    have hp : payment 440 = (2898227425897:ℝ)/1000000000000 := rfl
    have hx : (point 440+point 441)/2 = (35357093:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_440
  · change upperValue ((point 441+point 442)/2) ≤ payment 441
    have hp : payment 441 = (2892635462814:ℝ)/1000000000000 := rfl
    have hx : (point 441+point 442)/2 = (35398799:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_441
  · change upperValue ((point 442+point 443)/2) ≤ payment 442
    have hp : payment 442 = (2887052827862:ℝ)/1000000000000 := rfl
    have hx : (point 442+point 443)/2 = (35440505:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_442
  · change upperValue ((point 443+point 444)/2) ≤ payment 443
    have hp : payment 443 = (2881479480920:ℝ)/1000000000000 := rfl
    have hx : (point 443+point 444)/2 = (35482211:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_443
  · change upperValue ((point 444+point 445)/2) ≤ payment 444
    have hp : payment 444 = (2875915382042:ℝ)/1000000000000 := rfl
    have hx : (point 444+point 445)/2 = (35523917:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_444
  · change upperValue ((point 445+point 446)/2) ≤ payment 445
    have hp : payment 445 = (2870360491448:ℝ)/1000000000000 := rfl
    have hx : (point 445+point 446)/2 = (35565623:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_445
  · change upperValue ((point 446+point 447)/2) ≤ payment 446
    have hp : payment 446 = (2864814769532:ℝ)/1000000000000 := rfl
    have hx : (point 446+point 447)/2 = (35607329:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_446
  · change upperValue ((point 447+point 448)/2) ≤ payment 447
    have hp : payment 447 = (2859278176855:ℝ)/1000000000000 := rfl
    have hx : (point 447+point 448)/2 = (35649035:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_447
  · change upperValue ((point 448+point 449)/2) ≤ payment 448
    have hp : payment 448 = (2853750674146:ℝ)/1000000000000 := rfl
    have hx : (point 448+point 449)/2 = (35690741:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_448
  · change upperValue ((point 449+point 450)/2) ≤ payment 449
    have hp : payment 449 = (2848232222300:ℝ)/1000000000000 := rfl
    have hx : (point 449+point 450)/2 = (35732447:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_449
  · change upperValue ((point 450+point 451)/2) ≤ payment 450
    have hp : payment 450 = (2842722782379:ℝ)/1000000000000 := rfl
    have hx : (point 450+point 451)/2 = (35774153:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_450
  · change upperValue ((point 451+point 452)/2) ≤ payment 451
    have hp : payment 451 = (2837222315608:ℝ)/1000000000000 := rfl
    have hx : (point 451+point 452)/2 = (35815859:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_451
  · change upperValue ((point 452+point 453)/2) ≤ payment 452
    have hp : payment 452 = (2831730783377:ℝ)/1000000000000 := rfl
    have hx : (point 452+point 453)/2 = (35857565:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_452
  · change upperValue ((point 453+point 454)/2) ≤ payment 453
    have hp : payment 453 = (2826248147239:ℝ)/1000000000000 := rfl
    have hx : (point 453+point 454)/2 = (35899271:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_453
  · change upperValue ((point 454+point 455)/2) ≤ payment 454
    have hp : payment 454 = (2820774368906:ℝ)/1000000000000 := rfl
    have hx : (point 454+point 455)/2 = (35940977:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_454
  · change upperValue ((point 455+point 456)/2) ≤ payment 455
    have hp : payment 455 = (2815309410255:ℝ)/1000000000000 := rfl
    have hx : (point 455+point 456)/2 = (35982683:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_455
  · change upperValue ((point 456+point 457)/2) ≤ payment 456
    have hp : payment 456 = (2809853233318:ℝ)/1000000000000 := rfl
    have hx : (point 456+point 457)/2 = (36024389:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_456
  · change upperValue ((point 457+point 458)/2) ≤ payment 457
    have hp : payment 457 = (2804405800290:ℝ)/1000000000000 := rfl
    have hx : (point 457+point 458)/2 = (36066095:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_457
  · change upperValue ((point 458+point 459)/2) ≤ payment 458
    have hp : payment 458 = (2798967073520:ℝ)/1000000000000 := rfl
    have hx : (point 458+point 459)/2 = (36107801:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_458
  · change upperValue ((point 459+point 460)/2) ≤ payment 459
    have hp : payment 459 = (2793537015517:ℝ)/1000000000000 := rfl
    have hx : (point 459+point 460)/2 = (36149507:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_459
  · change upperValue ((point 460+point 461)/2) ≤ payment 460
    have hp : payment 460 = (2788115588943:ℝ)/1000000000000 := rfl
    have hx : (point 460+point 461)/2 = (351371:ℝ)/1358848 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_460
  · change upperValue ((point 461+point 462)/2) ≤ payment 461
    have hp : payment 461 = (2782702756618:ℝ)/1000000000000 := rfl
    have hx : (point 461+point 462)/2 = (36232919:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_461
  · change upperValue ((point 462+point 463)/2) ≤ payment 462
    have hp : payment 462 = (2777298481514:ℝ)/1000000000000 := rfl
    have hx : (point 462+point 463)/2 = (36274625:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_462
  · change upperValue ((point 463+point 464)/2) ≤ payment 463
    have hp : payment 463 = (2771902726755:ℝ)/1000000000000 := rfl
    have hx : (point 463+point 464)/2 = (36316331:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_463
  · change upperValue ((point 464+point 465)/2) ≤ payment 464
    have hp : payment 464 = (2766515455620:ℝ)/1000000000000 := rfl
    have hx : (point 464+point 465)/2 = (36358037:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_464
  · change upperValue ((point 465+point 466)/2) ≤ payment 465
    have hp : payment 465 = (2761136631538:ℝ)/1000000000000 := rfl
    have hx : (point 465+point 466)/2 = (36399743:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_465
  · change upperValue ((point 466+point 467)/2) ≤ payment 466
    have hp : payment 466 = (2755766218087:ℝ)/1000000000000 := rfl
    have hx : (point 466+point 467)/2 = (36441449:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_466
  · change upperValue ((point 467+point 468)/2) ≤ payment 467
    have hp : payment 467 = (2750404178995:ℝ)/1000000000000 := rfl
    have hx : (point 467+point 468)/2 = (36483155:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_467
  · change upperValue ((point 468+point 469)/2) ≤ payment 468
    have hp : payment 468 = (2745050478141:ℝ)/1000000000000 := rfl
    have hx : (point 468+point 469)/2 = (36524861:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_468
  · change upperValue ((point 469+point 470)/2) ≤ payment 469
    have hp : payment 469 = (2739705079547:ℝ)/1000000000000 := rfl
    have hx : (point 469+point 470)/2 = (36566567:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_469
  · change upperValue ((point 470+point 471)/2) ≤ payment 470
    have hp : payment 470 = (2734367947386:ℝ)/1000000000000 := rfl
    have hx : (point 470+point 471)/2 = (36608273:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_470
  · change upperValue ((point 471+point 472)/2) ≤ payment 471
    have hp : payment 471 = (2729039045975:ℝ)/1000000000000 := rfl
    have hx : (point 471+point 472)/2 = (36649979:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_471
  · change upperValue ((point 472+point 473)/2) ≤ payment 472
    have hp : payment 472 = (2723718339775:ℝ)/1000000000000 := rfl
    have hx : (point 472+point 473)/2 = (36691685:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_472
  · change upperValue ((point 473+point 474)/2) ≤ payment 473
    have hp : payment 473 = (2718405793393:ℝ)/1000000000000 := rfl
    have hx : (point 473+point 474)/2 = (36733391:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_473
  · change upperValue ((point 474+point 475)/2) ≤ payment 474
    have hp : payment 474 = (2713101371578:ℝ)/1000000000000 := rfl
    have hx : (point 474+point 475)/2 = (36775097:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_474
  · change upperValue ((point 475+point 476)/2) ≤ payment 475
    have hp : payment 475 = (2707805039221:ℝ)/1000000000000 := rfl
    have hx : (point 475+point 476)/2 = (36816803:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_475
  · change upperValue ((point 476+point 477)/2) ≤ payment 476
    have hp : payment 476 = (2702516761356:ℝ)/1000000000000 := rfl
    have hx : (point 476+point 477)/2 = (36858509:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_476
  · change upperValue ((point 477+point 478)/2) ≤ payment 477
    have hp : payment 477 = (2697236503155:ℝ)/1000000000000 := rfl
    have hx : (point 477+point 478)/2 = (36900215:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_477
  · change upperValue ((point 478+point 479)/2) ≤ payment 478
    have hp : payment 478 = (2691964229934:ℝ)/1000000000000 := rfl
    have hx : (point 478+point 479)/2 = (36941921:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_478
  · change upperValue ((point 479+point 480)/2) ≤ payment 479
    have hp : payment 479 = (2686699907144:ℝ)/1000000000000 := rfl
    have hx : (point 479+point 480)/2 = (36983627:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_479
  · change upperValue ((point 480+point 481)/2) ≤ payment 480
    have hp : payment 480 = (2681443500377:ℝ)/1000000000000 := rfl
    have hx : (point 480+point 481)/2 = (37025333:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_480
  · change upperValue ((point 481+point 482)/2) ≤ payment 481
    have hp : payment 481 = (2676194975359:ℝ)/1000000000000 := rfl
    have hx : (point 481+point 482)/2 = (37067039:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_481
  · change upperValue ((point 482+point 483)/2) ≤ payment 482
    have hp : payment 482 = (2670954297955:ℝ)/1000000000000 := rfl
    have hx : (point 482+point 483)/2 = (37108745:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_482
  · change upperValue ((point 483+point 484)/2) ≤ payment 483
    have hp : payment 483 = (2665721434166:ℝ)/1000000000000 := rfl
    have hx : (point 483+point 484)/2 = (37150451:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_483
  · change upperValue ((point 484+point 485)/2) ≤ payment 484
    have hp : payment 484 = (2660496350127:ℝ)/1000000000000 := rfl
    have hx : (point 484+point 485)/2 = (37192157:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_484
  · change upperValue ((point 485+point 486)/2) ≤ payment 485
    have hp : payment 485 = (2655279012105:ℝ)/1000000000000 := rfl
    have hx : (point 485+point 486)/2 = (37233863:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_485
  · change upperValue ((point 486+point 487)/2) ≤ payment 486
    have hp : payment 486 = (2650069386505:ℝ)/1000000000000 := rfl
    have hx : (point 486+point 487)/2 = (37275569:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_486
  · change upperValue ((point 487+point 488)/2) ≤ payment 487
    have hp : payment 487 = (2644867439860:ℝ)/1000000000000 := rfl
    have hx : (point 487+point 488)/2 = (37317275:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_487
  · change upperValue ((point 488+point 489)/2) ≤ payment 488
    have hp : payment 488 = (2639673138838:ℝ)/1000000000000 := rfl
    have hx : (point 488+point 489)/2 = (37358981:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_488
  · change upperValue ((point 489+point 490)/2) ≤ payment 489
    have hp : payment 489 = (2634486450234:ℝ)/1000000000000 := rfl
    have hx : (point 489+point 490)/2 = (37400687:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_489
  · change upperValue ((point 490+point 491)/2) ≤ payment 490
    have hp : payment 490 = (2629307340977:ℝ)/1000000000000 := rfl
    have hx : (point 490+point 491)/2 = (37442393:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_490
  · change upperValue ((point 491+point 492)/2) ≤ payment 491
    have hp : payment 491 = (2624135778123:ℝ)/1000000000000 := rfl
    have hx : (point 491+point 492)/2 = (37484099:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_491
  · change upperValue ((point 492+point 493)/2) ≤ payment 492
    have hp : payment 492 = (2618971728858:ℝ)/1000000000000 := rfl
    have hx : (point 492+point 493)/2 = (37525805:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_492
  · change upperValue ((point 493+point 494)/2) ≤ payment 493
    have hp : payment 493 = (2613815160495:ℝ)/1000000000000 := rfl
    have hx : (point 493+point 494)/2 = (37567511:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_493
  · change upperValue ((point 494+point 495)/2) ≤ payment 494
    have hp : payment 494 = (2608666040474:ℝ)/1000000000000 := rfl
    have hx : (point 494+point 495)/2 = (37609217:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_494
  · change upperValue ((point 495+point 496)/2) ≤ payment 495
    have hp : payment 495 = (2603524336361:ℝ)/1000000000000 := rfl
    have hx : (point 495+point 496)/2 = (37650923:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_495
  · change upperValue ((point 496+point 497)/2) ≤ payment 496
    have hp : payment 496 = (2598390015848:ℝ)/1000000000000 := rfl
    have hx : (point 496+point 497)/2 = (37692629:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_496
  · change upperValue ((point 497+point 498)/2) ≤ payment 497
    have hp : payment 497 = (2593263046752:ℝ)/1000000000000 := rfl
    have hx : (point 497+point 498)/2 = (37734335:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_497
  · change upperValue ((point 498+point 499)/2) ≤ payment 498
    have hp : payment 498 = (2588143397014:ℝ)/1000000000000 := rfl
    have hx : (point 498+point 499)/2 = (37776041:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_498
  · change upperValue ((point 499+point 500)/2) ≤ payment 499
    have hp : payment 499 = (2583031034698:ℝ)/1000000000000 := rfl
    have hx : (point 499+point 500)/2 = (37817747:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_499
  · change upperValue ((point 500+point 501)/2) ≤ payment 500
    have hp : payment 500 = (2577925927991:ℝ)/1000000000000 := rfl
    have hx : (point 500+point 501)/2 = (37859453:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_500
  · change upperValue ((point 501+point 502)/2) ≤ payment 501
    have hp : payment 501 = (2572828045201:ℝ)/1000000000000 := rfl
    have hx : (point 501+point 502)/2 = (37901159:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_501
  · change upperValue ((point 502+point 503)/2) ≤ payment 502
    have hp : payment 502 = (2567737354758:ℝ)/1000000000000 := rfl
    have hx : (point 502+point 503)/2 = (37942865:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_502
  · change upperValue ((point 503+point 504)/2) ≤ payment 503
    have hp : payment 503 = (2562653825213:ℝ)/1000000000000 := rfl
    have hx : (point 503+point 504)/2 = (37984571:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_503
  · change upperValue ((point 504+point 505)/2) ≤ payment 504
    have hp : payment 504 = (2557577425234:ℝ)/1000000000000 := rfl
    have hx : (point 504+point 505)/2 = (38026277:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_504
  · change upperValue ((point 505+point 506)/2) ≤ payment 505
    have hp : payment 505 = (2552508123611:ℝ)/1000000000000 := rfl
    have hx : (point 505+point 506)/2 = (38067983:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_505
  · change upperValue ((point 506+point 507)/2) ≤ payment 506
    have hp : payment 506 = (2547445889251:ℝ)/1000000000000 := rfl
    have hx : (point 506+point 507)/2 = (38109689:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_506
  · change upperValue ((point 507+point 508)/2) ≤ payment 507
    have hp : payment 507 = (2542390691178:ℝ)/1000000000000 := rfl
    have hx : (point 507+point 508)/2 = (38151395:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_507
  · change upperValue ((point 508+point 509)/2) ≤ payment 508
    have hp : payment 508 = (2537342498535:ℝ)/1000000000000 := rfl
    have hx : (point 508+point 509)/2 = (38193101:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_508
  · change upperValue ((point 509+point 510)/2) ≤ payment 509
    have hp : payment 509 = (2532301280579:ℝ)/1000000000000 := rfl
    have hx : (point 509+point 510)/2 = (38234807:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_509
  · change upperValue ((point 510+point 511)/2) ≤ payment 510
    have hp : payment 510 = (2527267006684:ℝ)/1000000000000 := rfl
    have hx : (point 510+point 511)/2 = (38276513:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_510
  · change upperValue ((point 511+point 512)/2) ≤ payment 511
    have hp : payment 511 = (2522239646337:ℝ)/1000000000000 := rfl
    have hx : (point 511+point 512)/2 = (38318219:ℝ)/139961344 := by
      norm_num [point,step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]
    rw [hp,hx]
    exact point_upper_511

theorem ninth_main_upper : Wu08TerminalAlignment.ninthMain ≤ (268621:ℝ)/50000 := by
  have h := uniform_upper payment (fun i hi => payments_paid ⟨i,hi⟩)
  apply h.trans
  simp only [payment,← sum_div,← Nat.cast_sum,numerator_sum]
  norm_num [step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]

end WuPaper.ClassicalNinth
#print axioms WuPaper.ClassicalNinth.ninth_main_upper
