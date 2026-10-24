import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay001
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_001 (j : Fin 64) (hj : 64*1+j.val < 10540) :
    BPay (64*1+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_64
  · exact WuPaper.ClassicalFourthNat.BPay_65
  · exact WuPaper.ClassicalFourthNat.BPay_66
  · exact WuPaper.ClassicalFourthNat.BPay_67
  · exact WuPaper.ClassicalFourthNat.BPay_68
  · exact WuPaper.ClassicalFourthNat.BPay_69
  · exact WuPaper.ClassicalFourthNat.BPay_70
  · exact WuPaper.ClassicalFourthNat.BPay_71
  · exact WuPaper.ClassicalFourthNat.BPay_72
  · exact WuPaper.ClassicalFourthNat.BPay_73
  · exact WuPaper.ClassicalFourthNat.BPay_74
  · exact WuPaper.ClassicalFourthNat.BPay_75
  · exact WuPaper.ClassicalFourthNat.BPay_76
  · exact WuPaper.ClassicalFourthNat.BPay_77
  · exact WuPaper.ClassicalFourthNat.BPay_78
  · exact WuPaper.ClassicalFourthNat.BPay_79
  · exact WuPaper.ClassicalFourthNat.BPay_80
  · exact WuPaper.ClassicalFourthNat.BPay_81
  · exact WuPaper.ClassicalFourthNat.BPay_82
  · exact WuPaper.ClassicalFourthNat.BPay_83
  · exact WuPaper.ClassicalFourthNat.BPay_84
  · exact WuPaper.ClassicalFourthNat.BPay_85
  · exact WuPaper.ClassicalFourthNat.BPay_86
  · exact WuPaper.ClassicalFourthNat.BPay_87
  · exact WuPaper.ClassicalFourthNat.BPay_88
  · exact WuPaper.ClassicalFourthNat.BPay_89
  · exact WuPaper.ClassicalFourthNat.BPay_90
  · exact WuPaper.ClassicalFourthNat.BPay_91
  · exact WuPaper.ClassicalFourthNat.BPay_92
  · exact WuPaper.ClassicalFourthNat.BPay_93
  · exact WuPaper.ClassicalFourthNat.BPay_94
  · exact WuPaper.ClassicalFourthNat.BPay_95
  · exact WuPaper.ClassicalFourthNat.BPay_96
  · exact WuPaper.ClassicalFourthNat.BPay_97
  · exact WuPaper.ClassicalFourthNat.BPay_98
  · exact WuPaper.ClassicalFourthNat.BPay_99
  · exact WuPaper.ClassicalFourthNat.BPay_100
  · exact WuPaper.ClassicalFourthNat.BPay_101
  · exact WuPaper.ClassicalFourthNat.BPay_102
  · exact WuPaper.ClassicalFourthNat.BPay_103
  · exact WuPaper.ClassicalFourthNat.BPay_104
  · exact WuPaper.ClassicalFourthNat.BPay_105
  · exact WuPaper.ClassicalFourthNat.BPay_106
  · exact WuPaper.ClassicalFourthNat.BPay_107
  · exact WuPaper.ClassicalFourthNat.BPay_108
  · exact WuPaper.ClassicalFourthNat.BPay_109
  · exact WuPaper.ClassicalFourthNat.BPay_110
  · exact WuPaper.ClassicalFourthNat.BPay_111
  · exact WuPaper.ClassicalFourthNat.BPay_112
  · exact WuPaper.ClassicalFourthNat.BPay_113
  · exact WuPaper.ClassicalFourthNat.BPay_114
  · exact WuPaper.ClassicalFourthNat.BPay_115
  · exact WuPaper.ClassicalFourthNat.BPay_116
  · exact WuPaper.ClassicalFourthNat.BPay_117
  · exact WuPaper.ClassicalFourthNat.BPay_118
  · exact WuPaper.ClassicalFourthNat.BPay_119
  · exact WuPaper.ClassicalFourthNat.BPay_120
  · exact WuPaper.ClassicalFourthNat.BPay_121
  · exact WuPaper.ClassicalFourthNat.BPay_122
  · exact WuPaper.ClassicalFourthNat.BPay_123
  · exact WuPaper.ClassicalFourthNat.BPay_124
  · exact WuPaper.ClassicalFourthNat.BPay_125
  · exact WuPaper.ClassicalFourthNat.BPay_126
  · exact WuPaper.ClassicalFourthNat.BPay_127
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_001
