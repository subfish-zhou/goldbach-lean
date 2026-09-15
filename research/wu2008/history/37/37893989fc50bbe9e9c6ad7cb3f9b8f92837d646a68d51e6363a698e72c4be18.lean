import W05JFeedback

noncomputable section
namespace WuTarget.W05
open Wu2008DoubleSieve NodeExtension ActualNineFeedback
open CoupledIntegralRecovery FiniteEndpointPayment

def coupledTable0_s : Fin 9 → ℝ := ![22928979/241709600, 2183/82401, 577561/20375520, 46818/1560625, 3127697/112260126, 13/531, 39/1652, 39/1711, 13/590]

theorem coupledTable0_s_exact (k : Fin 9) :
    rationalJCoefficient (coupledRow 0).s (coupledRow 0).S k = coupledTable0_s k := by
  fin_cases k <;>
    norm_num [coupledTable0_s, rationalJCoefficient, rationalCell, jStart, left, right, clip,
      upperNode, upperLeft, firstNode, firstS, coupledRow,
      SecondFunctionalPositive.parameters, SecondFunctionalParameters.row1,
      SecondFunctionalParameters.row2, SecondFunctionalParameters.row3,
      SecondFunctionalParameters.row4]

def coupledTable0_kappa2 : Fin 9 → ℝ := ![73887939/6719926400, 1127389/99929940, 3267/223822, 289393/16457500, 3033188/163027995, 82/4779, 41/2478, 82/5133, 41/2655]

theorem coupledTable0_kappa2_exact (k : Fin 9) :
    rationalJCoefficient (coupledRow 0).kappa2 (coupledRow 0).S k = coupledTable0_kappa2 k := by
  fin_cases k <;>
    norm_num [coupledTable0_kappa2, rationalJCoefficient, rationalCell, jStart, left, right, clip,
      upperNode, upperLeft, firstNode, firstS, coupledRow,
      SecondFunctionalPositive.parameters, SecondFunctionalParameters.row1,
      SecondFunctionalParameters.row2, SecondFunctionalParameters.row3,
      SecondFunctionalParameters.row4]

def coupledTable0_kappa3 : Fin 9 → ℝ := ![486538983/9291337000, 5479094/262746825, 13128019/564957600, 1537227/60580625, 4965924991/202323363450, 35/1593, 5/236, 35/1711, 7/354]

theorem coupledTable0_kappa3_exact (k : Fin 9) :
    rationalJCoefficient (coupledRow 0).kappa3 (coupledRow 0).S k = coupledTable0_kappa3 k := by
  fin_cases k <;>
    norm_num [coupledTable0_kappa3, rationalJCoefficient, rationalCell, jStart, left, right, clip,
      upperNode, upperLeft, firstNode, firstS, coupledRow,
      SecondFunctionalPositive.parameters, SecondFunctionalParameters.row1,
      SecondFunctionalParameters.row2, SecondFunctionalParameters.row3,
      SecondFunctionalParameters.row4]

def coupledTable1_s : Fin 9 → ℝ := ![13520993/167587200, 5239/209484, 28567/1055700, 34889/1207500, 11/455, 22/945, 11/490, 22/1015, 11/525]

theorem coupledTable1_s_exact (k : Fin 9) :
    rationalJCoefficient (coupledRow 1).s (coupledRow 1).S k = coupledTable1_s k := by
  fin_cases k <;>
    norm_num [coupledTable1_s, rationalJCoefficient, rationalCell, jStart, left, right, clip,
      upperNode, upperLeft, firstNode, firstS, coupledRow,
      SecondFunctionalPositive.parameters, SecondFunctionalParameters.row1,
      SecondFunctionalParameters.row2, SecondFunctionalParameters.row3,
      SecondFunctionalParameters.row4]

def coupledTable1_kappa2 : Fin 9 → ℝ := ![168021/11264000, 389/30360, 4367/272000, 3321/175000, 81/4550, 3/175, 81/4900, 81/5075, 27/1750]

theorem coupledTable1_kappa2_exact (k : Fin 9) :
    rationalJCoefficient (coupledRow 1).kappa2 (coupledRow 1).S k = coupledTable1_kappa2 k := by
  fin_cases k <;>
    norm_num [coupledTable1_kappa2, rationalJCoefficient, rationalCell, jStart, left, right, clip,
      upperNode, upperLeft, firstNode, firstS, coupledRow,
      SecondFunctionalPositive.parameters, SecondFunctionalParameters.row1,
      SecondFunctionalParameters.row2, SecondFunctionalParameters.row3,
      SecondFunctionalParameters.row4]

def coupledTable1_kappa3 : Fin 9 → ℝ := ![688231/11664000, 18083/819720, 268711/11016000, 125137/4725000, 207/9100, 23/1050, 207/9800, 207/10150, 69/3500]

theorem coupledTable1_kappa3_exact (k : Fin 9) :
    rationalJCoefficient (coupledRow 1).kappa3 (coupledRow 1).S k = coupledTable1_kappa3 k := by
  fin_cases k <;>
    norm_num [coupledTable1_kappa3, rationalJCoefficient, rationalCell, jStart, left, right, clip,
      upperNode, upperLeft, firstNode, firstS, coupledRow,
      SecondFunctionalPositive.parameters, SecondFunctionalParameters.row1,
      SecondFunctionalParameters.row2, SecondFunctionalParameters.row3,
      SecondFunctionalParameters.row4]

def coupledTable2_s : Fin 9 → ℝ := ![78230767/1130342400, 240791/10155420, 283319/10918080, 62249671/2372608500, 103/4498, 103/4671, 103/4844, 103/5017, 103/5190]

theorem coupledTable2_s_exact (k : Fin 9) :
    rationalJCoefficient (coupledRow 2).s (coupledRow 2).S k = coupledTable2_s k := by
  fin_cases k <;>
    norm_num [coupledTable2_s, rationalJCoefficient, rationalCell, jStart, left, right, clip,
      upperNode, upperLeft, firstNode, firstS, coupledRow,
      SecondFunctionalPositive.parameters, SecondFunctionalParameters.row1,
      SecondFunctionalParameters.row2, SecondFunctionalParameters.row3,
      SecondFunctionalParameters.row4]

def coupledTable2_kappa2 : Fin 9 → ℝ := ![60715666971/3232818512000, 45846921/3238450600, 90589987/5222481600, 8748135597/453959093000, 159/8996, 53/3114, 159/9688, 159/10034, 53/3460]

theorem coupledTable2_kappa2_exact (k : Fin 9) :
    rationalJCoefficient (coupledRow 2).kappa2 (coupledRow 2).S k = coupledTable2_kappa2 k := by
  fin_cases k <;>
    norm_num [coupledTable2_kappa2, rationalJCoefficient, rationalCell, jStart, left, right, clip,
      upperNode, upperLeft, firstNode, firstS, coupledRow,
      SecondFunctionalPositive.parameters, SecondFunctionalParameters.row1,
      SecondFunctionalParameters.row2, SecondFunctionalParameters.row3,
      SecondFunctionalParameters.row4]

def coupledTable2_kappa3 : Fin 9 → ℝ := ![78230767/1130342400, 240791/10155420, 283319/10918080, 62249671/2372608500, 103/4498, 103/4671, 103/4844, 103/5017, 103/5190]

theorem coupledTable2_kappa3_exact (k : Fin 9) :
    rationalJCoefficient (coupledRow 2).kappa3 (coupledRow 2).S k = coupledTable2_kappa3 k := by
  fin_cases k <;>
    norm_num [coupledTable2_kappa3, rationalJCoefficient, rationalCell, jStart, left, right, clip,
      upperNode, upperLeft, firstNode, firstS, coupledRow,
      SecondFunctionalPositive.parameters, SecondFunctionalParameters.row1,
      SecondFunctionalParameters.row2, SecondFunctionalParameters.row3,
      SecondFunctionalParameters.row4]

def coupledTable3_s : Fin 9 → ℝ := ![2160729/19515925, 27/1196, 9/416, 27/1300, 27/1352, 1/52, 27/1456, 27/1508, 9/520]

theorem coupledTable3_s_exact (k : Fin 9) :
    rationalJCoefficient (coupledRow 3).s (coupledRow 3).S k = coupledTable3_s k := by
  fin_cases k <;>
    norm_num [coupledTable3_s, rationalJCoefficient, rationalCell, jStart, left, right, clip,
      upperNode, upperLeft, firstNode, firstS, coupledRow,
      SecondFunctionalPositive.parameters, SecondFunctionalParameters.row1,
      SecondFunctionalParameters.row2, SecondFunctionalParameters.row3,
      SecondFunctionalParameters.row4]

def coupledTable3_kappa2 : Fin 9 → ℝ := ![40365251113/721146783240, 121/7176, 121/7488, 121/7800, 121/8112, 121/8424, 121/8736, 121/9048, 121/9360]

theorem coupledTable3_kappa2_exact (k : Fin 9) :
    rationalJCoefficient (coupledRow 3).kappa2 (coupledRow 3).S k = coupledTable3_kappa2 k := by
  fin_cases k <;>
    norm_num [coupledTable3_kappa2, rationalJCoefficient, rationalCell, jStart, left, right, clip,
      upperNode, upperLeft, firstNode, firstS, coupledRow,
      SecondFunctionalPositive.parameters, SecondFunctionalParameters.row1,
      SecondFunctionalParameters.row2, SecondFunctionalParameters.row3,
      SecondFunctionalParameters.row4]

def coupledTable3_kappa3 : Fin 9 → ℝ := ![2160729/19515925, 27/1196, 9/416, 27/1300, 27/1352, 1/52, 27/1456, 27/1508, 9/520]

theorem coupledTable3_kappa3_exact (k : Fin 9) :
    rationalJCoefficient (coupledRow 3).kappa3 (coupledRow 3).S k = coupledTable3_kappa3 k := by
  fin_cases k <;>
    norm_num [coupledTable3_kappa3, rationalJCoefficient, rationalCell, jStart, left, right, clip,
      upperNode, upperLeft, firstNode, firstS, coupledRow,
      SecondFunctionalPositive.parameters, SecondFunctionalParameters.row1,
      SecondFunctionalParameters.row2, SecondFunctionalParameters.row3,
      SecondFunctionalParameters.row4]

def firstTable0 : Fin 9 → ℝ := ![123915757/788643570, 49/2967, 49/3096, 49/3225, 49/3354, 49/3483, 7/516, 49/3741, 49/3870]

theorem firstTable0_exact (k : Fin 9) :
    rationalJCoefficient (firstNode 0) (firstS 0) k = firstTable0 k := by
  fin_cases k <;>
    norm_num [firstTable0, rationalJCoefficient, rationalCell, jStart, left, right, clip,
      upperNode, upperLeft, firstNode, firstS, coupledRow,
      SecondFunctionalPositive.parameters, SecondFunctionalParameters.row1,
      SecondFunctionalParameters.row2, SecondFunctionalParameters.row3,
      SecondFunctionalParameters.row4]

def firstTable1 : Fin 9 → ℝ := ![510474179/3748911660, 77/5681, 77/5928, 77/6175, 77/6422, 77/6669, 11/988, 77/7163, 77/7410]

theorem firstTable1_exact (k : Fin 9) :
    rationalJCoefficient (firstNode 1) (firstS 1) k = firstTable1 k := by
  fin_cases k <;>
    norm_num [firstTable1, rationalJCoefficient, rationalCell, jStart, left, right, clip,
      upperNode, upperLeft, firstNode, firstS, coupledRow,
      SecondFunctionalPositive.parameters, SecondFunctionalParameters.row1,
      SecondFunctionalParameters.row2, SecondFunctionalParameters.row3,
      SecondFunctionalParameters.row4]

def firstTable2 : Fin 9 → ℝ := ![337988751/3136052920, 3/299, 1/104, 3/325, 3/338, 1/117, 3/364, 3/377, 1/130]

theorem firstTable2_exact (k : Fin 9) :
    rationalJCoefficient (firstNode 2) (firstS 2) k = firstTable2 k := by
  fin_cases k <;>
    norm_num [firstTable2, rationalJCoefficient, rationalCell, jStart, left, right, clip,
      upperNode, upperLeft, firstNode, firstS, coupledRow,
      SecondFunctionalPositive.parameters, SecondFunctionalParameters.row1,
      SecondFunctionalParameters.row2, SecondFunctionalParameters.row3,
      SecondFunctionalParameters.row4]

def firstTable3 : Fin 9 → ℝ := ![54493/819060, 29/5037, 29/5256, 29/5475, 29/5694, 29/5913, 29/6132, 1/219, 29/6570]

theorem firstTable3_exact (k : Fin 9) :
    rationalJCoefficient (firstNode 3) (firstS 3) k = firstTable3 k := by
  fin_cases k <;>
    norm_num [firstTable3, rationalJCoefficient, rationalCell, jStart, left, right, clip,
      upperNode, upperLeft, firstNode, firstS, coupledRow,
      SecondFunctionalPositive.parameters, SecondFunctionalParameters.row1,
      SecondFunctionalParameters.row2, SecondFunctionalParameters.row3,
      SecondFunctionalParameters.row4]

def firstTable4 : Fin 9 → ℝ := ![0, 0, 0, 0, 0, 0, 0, 0, 0]

theorem firstTable4_exact (k : Fin 9) :
    rationalJCoefficient (firstNode 4) (firstS 4) k = firstTable4 k := by
  fin_cases k <;>
    norm_num [firstTable4, rationalJCoefficient, rationalCell, jStart, left, right, clip,
      upperNode, upperLeft, firstNode, firstS, coupledRow,
      SecondFunctionalPositive.parameters, SecondFunctionalParameters.row1,
      SecondFunctionalParameters.row2, SecondFunctionalParameters.row3,
      SecondFunctionalParameters.row4]

end WuTarget.W05
