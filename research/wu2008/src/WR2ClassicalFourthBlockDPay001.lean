import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatDPay001
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem DPay_block_001 (j : Fin 64) (hj : 64*1+j.val < 2540) :
    DPay (64*1+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.DPay_64
  · exact WuPaper.ClassicalFourthNat.DPay_65
  · exact WuPaper.ClassicalFourthNat.DPay_66
  · exact WuPaper.ClassicalFourthNat.DPay_67
  · exact WuPaper.ClassicalFourthNat.DPay_68
  · exact WuPaper.ClassicalFourthNat.DPay_69
  · exact WuPaper.ClassicalFourthNat.DPay_70
  · exact WuPaper.ClassicalFourthNat.DPay_71
  · exact WuPaper.ClassicalFourthNat.DPay_72
  · exact WuPaper.ClassicalFourthNat.DPay_73
  · exact WuPaper.ClassicalFourthNat.DPay_74
  · exact WuPaper.ClassicalFourthNat.DPay_75
  · exact WuPaper.ClassicalFourthNat.DPay_76
  · exact WuPaper.ClassicalFourthNat.DPay_77
  · exact WuPaper.ClassicalFourthNat.DPay_78
  · exact WuPaper.ClassicalFourthNat.DPay_79
  · exact WuPaper.ClassicalFourthNat.DPay_80
  · exact WuPaper.ClassicalFourthNat.DPay_81
  · exact WuPaper.ClassicalFourthNat.DPay_82
  · exact WuPaper.ClassicalFourthNat.DPay_83
  · exact WuPaper.ClassicalFourthNat.DPay_84
  · exact WuPaper.ClassicalFourthNat.DPay_85
  · exact WuPaper.ClassicalFourthNat.DPay_86
  · exact WuPaper.ClassicalFourthNat.DPay_87
  · exact WuPaper.ClassicalFourthNat.DPay_88
  · exact WuPaper.ClassicalFourthNat.DPay_89
  · exact WuPaper.ClassicalFourthNat.DPay_90
  · exact WuPaper.ClassicalFourthNat.DPay_91
  · exact WuPaper.ClassicalFourthNat.DPay_92
  · exact WuPaper.ClassicalFourthNat.DPay_93
  · exact WuPaper.ClassicalFourthNat.DPay_94
  · exact WuPaper.ClassicalFourthNat.DPay_95
  · exact WuPaper.ClassicalFourthNat.DPay_96
  · exact WuPaper.ClassicalFourthNat.DPay_97
  · exact WuPaper.ClassicalFourthNat.DPay_98
  · exact WuPaper.ClassicalFourthNat.DPay_99
  · exact WuPaper.ClassicalFourthNat.DPay_100
  · exact WuPaper.ClassicalFourthNat.DPay_101
  · exact WuPaper.ClassicalFourthNat.DPay_102
  · exact WuPaper.ClassicalFourthNat.DPay_103
  · exact WuPaper.ClassicalFourthNat.DPay_104
  · exact WuPaper.ClassicalFourthNat.DPay_105
  · exact WuPaper.ClassicalFourthNat.DPay_106
  · exact WuPaper.ClassicalFourthNat.DPay_107
  · exact WuPaper.ClassicalFourthNat.DPay_108
  · exact WuPaper.ClassicalFourthNat.DPay_109
  · exact WuPaper.ClassicalFourthNat.DPay_110
  · exact WuPaper.ClassicalFourthNat.DPay_111
  · exact WuPaper.ClassicalFourthNat.DPay_112
  · exact WuPaper.ClassicalFourthNat.DPay_113
  · exact WuPaper.ClassicalFourthNat.DPay_114
  · exact WuPaper.ClassicalFourthNat.DPay_115
  · exact WuPaper.ClassicalFourthNat.DPay_116
  · exact WuPaper.ClassicalFourthNat.DPay_117
  · exact WuPaper.ClassicalFourthNat.DPay_118
  · exact WuPaper.ClassicalFourthNat.DPay_119
  · exact WuPaper.ClassicalFourthNat.DPay_120
  · exact WuPaper.ClassicalFourthNat.DPay_121
  · exact WuPaper.ClassicalFourthNat.DPay_122
  · exact WuPaper.ClassicalFourthNat.DPay_123
  · exact WuPaper.ClassicalFourthNat.DPay_124
  · exact WuPaper.ClassicalFourthNat.DPay_125
  · exact WuPaper.ClassicalFourthNat.DPay_126
  · exact WuPaper.ClassicalFourthNat.DPay_127
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.DPay_block_001
