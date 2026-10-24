import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatCPay001
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem CPay_block_001 (j : Fin 64) (hj : 64*1+j.val < 2540) :
    CPay (64*1+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.CPay_64
  · exact WuPaper.ClassicalFourthNat.CPay_65
  · exact WuPaper.ClassicalFourthNat.CPay_66
  · exact WuPaper.ClassicalFourthNat.CPay_67
  · exact WuPaper.ClassicalFourthNat.CPay_68
  · exact WuPaper.ClassicalFourthNat.CPay_69
  · exact WuPaper.ClassicalFourthNat.CPay_70
  · exact WuPaper.ClassicalFourthNat.CPay_71
  · exact WuPaper.ClassicalFourthNat.CPay_72
  · exact WuPaper.ClassicalFourthNat.CPay_73
  · exact WuPaper.ClassicalFourthNat.CPay_74
  · exact WuPaper.ClassicalFourthNat.CPay_75
  · exact WuPaper.ClassicalFourthNat.CPay_76
  · exact WuPaper.ClassicalFourthNat.CPay_77
  · exact WuPaper.ClassicalFourthNat.CPay_78
  · exact WuPaper.ClassicalFourthNat.CPay_79
  · exact WuPaper.ClassicalFourthNat.CPay_80
  · exact WuPaper.ClassicalFourthNat.CPay_81
  · exact WuPaper.ClassicalFourthNat.CPay_82
  · exact WuPaper.ClassicalFourthNat.CPay_83
  · exact WuPaper.ClassicalFourthNat.CPay_84
  · exact WuPaper.ClassicalFourthNat.CPay_85
  · exact WuPaper.ClassicalFourthNat.CPay_86
  · exact WuPaper.ClassicalFourthNat.CPay_87
  · exact WuPaper.ClassicalFourthNat.CPay_88
  · exact WuPaper.ClassicalFourthNat.CPay_89
  · exact WuPaper.ClassicalFourthNat.CPay_90
  · exact WuPaper.ClassicalFourthNat.CPay_91
  · exact WuPaper.ClassicalFourthNat.CPay_92
  · exact WuPaper.ClassicalFourthNat.CPay_93
  · exact WuPaper.ClassicalFourthNat.CPay_94
  · exact WuPaper.ClassicalFourthNat.CPay_95
  · exact WuPaper.ClassicalFourthNat.CPay_96
  · exact WuPaper.ClassicalFourthNat.CPay_97
  · exact WuPaper.ClassicalFourthNat.CPay_98
  · exact WuPaper.ClassicalFourthNat.CPay_99
  · exact WuPaper.ClassicalFourthNat.CPay_100
  · exact WuPaper.ClassicalFourthNat.CPay_101
  · exact WuPaper.ClassicalFourthNat.CPay_102
  · exact WuPaper.ClassicalFourthNat.CPay_103
  · exact WuPaper.ClassicalFourthNat.CPay_104
  · exact WuPaper.ClassicalFourthNat.CPay_105
  · exact WuPaper.ClassicalFourthNat.CPay_106
  · exact WuPaper.ClassicalFourthNat.CPay_107
  · exact WuPaper.ClassicalFourthNat.CPay_108
  · exact WuPaper.ClassicalFourthNat.CPay_109
  · exact WuPaper.ClassicalFourthNat.CPay_110
  · exact WuPaper.ClassicalFourthNat.CPay_111
  · exact WuPaper.ClassicalFourthNat.CPay_112
  · exact WuPaper.ClassicalFourthNat.CPay_113
  · exact WuPaper.ClassicalFourthNat.CPay_114
  · exact WuPaper.ClassicalFourthNat.CPay_115
  · exact WuPaper.ClassicalFourthNat.CPay_116
  · exact WuPaper.ClassicalFourthNat.CPay_117
  · exact WuPaper.ClassicalFourthNat.CPay_118
  · exact WuPaper.ClassicalFourthNat.CPay_119
  · exact WuPaper.ClassicalFourthNat.CPay_120
  · exact WuPaper.ClassicalFourthNat.CPay_121
  · exact WuPaper.ClassicalFourthNat.CPay_122
  · exact WuPaper.ClassicalFourthNat.CPay_123
  · exact WuPaper.ClassicalFourthNat.CPay_124
  · exact WuPaper.ClassicalFourthNat.CPay_125
  · exact WuPaper.ClassicalFourthNat.CPay_126
  · exact WuPaper.ClassicalFourthNat.CPay_127
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.CPay_block_001
