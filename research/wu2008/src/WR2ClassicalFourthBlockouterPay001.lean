import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatouterPay001
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem outerPay_block_001 (j : Fin 64) (hj : 64*1+j.val < 10540) :
    OuterPay (64*1+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.outerPay_64
  · exact WuPaper.ClassicalFourthNat.outerPay_65
  · exact WuPaper.ClassicalFourthNat.outerPay_66
  · exact WuPaper.ClassicalFourthNat.outerPay_67
  · exact WuPaper.ClassicalFourthNat.outerPay_68
  · exact WuPaper.ClassicalFourthNat.outerPay_69
  · exact WuPaper.ClassicalFourthNat.outerPay_70
  · exact WuPaper.ClassicalFourthNat.outerPay_71
  · exact WuPaper.ClassicalFourthNat.outerPay_72
  · exact WuPaper.ClassicalFourthNat.outerPay_73
  · exact WuPaper.ClassicalFourthNat.outerPay_74
  · exact WuPaper.ClassicalFourthNat.outerPay_75
  · exact WuPaper.ClassicalFourthNat.outerPay_76
  · exact WuPaper.ClassicalFourthNat.outerPay_77
  · exact WuPaper.ClassicalFourthNat.outerPay_78
  · exact WuPaper.ClassicalFourthNat.outerPay_79
  · exact WuPaper.ClassicalFourthNat.outerPay_80
  · exact WuPaper.ClassicalFourthNat.outerPay_81
  · exact WuPaper.ClassicalFourthNat.outerPay_82
  · exact WuPaper.ClassicalFourthNat.outerPay_83
  · exact WuPaper.ClassicalFourthNat.outerPay_84
  · exact WuPaper.ClassicalFourthNat.outerPay_85
  · exact WuPaper.ClassicalFourthNat.outerPay_86
  · exact WuPaper.ClassicalFourthNat.outerPay_87
  · exact WuPaper.ClassicalFourthNat.outerPay_88
  · exact WuPaper.ClassicalFourthNat.outerPay_89
  · exact WuPaper.ClassicalFourthNat.outerPay_90
  · exact WuPaper.ClassicalFourthNat.outerPay_91
  · exact WuPaper.ClassicalFourthNat.outerPay_92
  · exact WuPaper.ClassicalFourthNat.outerPay_93
  · exact WuPaper.ClassicalFourthNat.outerPay_94
  · exact WuPaper.ClassicalFourthNat.outerPay_95
  · exact WuPaper.ClassicalFourthNat.outerPay_96
  · exact WuPaper.ClassicalFourthNat.outerPay_97
  · exact WuPaper.ClassicalFourthNat.outerPay_98
  · exact WuPaper.ClassicalFourthNat.outerPay_99
  · exact WuPaper.ClassicalFourthNat.outerPay_100
  · exact WuPaper.ClassicalFourthNat.outerPay_101
  · exact WuPaper.ClassicalFourthNat.outerPay_102
  · exact WuPaper.ClassicalFourthNat.outerPay_103
  · exact WuPaper.ClassicalFourthNat.outerPay_104
  · exact WuPaper.ClassicalFourthNat.outerPay_105
  · exact WuPaper.ClassicalFourthNat.outerPay_106
  · exact WuPaper.ClassicalFourthNat.outerPay_107
  · exact WuPaper.ClassicalFourthNat.outerPay_108
  · exact WuPaper.ClassicalFourthNat.outerPay_109
  · exact WuPaper.ClassicalFourthNat.outerPay_110
  · exact WuPaper.ClassicalFourthNat.outerPay_111
  · exact WuPaper.ClassicalFourthNat.outerPay_112
  · exact WuPaper.ClassicalFourthNat.outerPay_113
  · exact WuPaper.ClassicalFourthNat.outerPay_114
  · exact WuPaper.ClassicalFourthNat.outerPay_115
  · exact WuPaper.ClassicalFourthNat.outerPay_116
  · exact WuPaper.ClassicalFourthNat.outerPay_117
  · exact WuPaper.ClassicalFourthNat.outerPay_118
  · exact WuPaper.ClassicalFourthNat.outerPay_119
  · exact WuPaper.ClassicalFourthNat.outerPay_120
  · exact WuPaper.ClassicalFourthNat.outerPay_121
  · exact WuPaper.ClassicalFourthNat.outerPay_122
  · exact WuPaper.ClassicalFourthNat.outerPay_123
  · exact WuPaper.ClassicalFourthNat.outerPay_124
  · exact WuPaper.ClassicalFourthNat.outerPay_125
  · exact WuPaper.ClassicalFourthNat.outerPay_126
  · exact WuPaper.ClassicalFourthNat.outerPay_127
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.outerPay_block_001
