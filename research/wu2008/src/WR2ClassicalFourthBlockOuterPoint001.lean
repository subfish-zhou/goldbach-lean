import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatOuterPoint001
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem OuterPoint_block_001 (j : Fin 64) (hj : 64*1+j.val < 10541) :
    OuterPoint (64*1+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.OuterPoint_64
  · exact WuPaper.ClassicalFourthNat.OuterPoint_65
  · exact WuPaper.ClassicalFourthNat.OuterPoint_66
  · exact WuPaper.ClassicalFourthNat.OuterPoint_67
  · exact WuPaper.ClassicalFourthNat.OuterPoint_68
  · exact WuPaper.ClassicalFourthNat.OuterPoint_69
  · exact WuPaper.ClassicalFourthNat.OuterPoint_70
  · exact WuPaper.ClassicalFourthNat.OuterPoint_71
  · exact WuPaper.ClassicalFourthNat.OuterPoint_72
  · exact WuPaper.ClassicalFourthNat.OuterPoint_73
  · exact WuPaper.ClassicalFourthNat.OuterPoint_74
  · exact WuPaper.ClassicalFourthNat.OuterPoint_75
  · exact WuPaper.ClassicalFourthNat.OuterPoint_76
  · exact WuPaper.ClassicalFourthNat.OuterPoint_77
  · exact WuPaper.ClassicalFourthNat.OuterPoint_78
  · exact WuPaper.ClassicalFourthNat.OuterPoint_79
  · exact WuPaper.ClassicalFourthNat.OuterPoint_80
  · exact WuPaper.ClassicalFourthNat.OuterPoint_81
  · exact WuPaper.ClassicalFourthNat.OuterPoint_82
  · exact WuPaper.ClassicalFourthNat.OuterPoint_83
  · exact WuPaper.ClassicalFourthNat.OuterPoint_84
  · exact WuPaper.ClassicalFourthNat.OuterPoint_85
  · exact WuPaper.ClassicalFourthNat.OuterPoint_86
  · exact WuPaper.ClassicalFourthNat.OuterPoint_87
  · exact WuPaper.ClassicalFourthNat.OuterPoint_88
  · exact WuPaper.ClassicalFourthNat.OuterPoint_89
  · exact WuPaper.ClassicalFourthNat.OuterPoint_90
  · exact WuPaper.ClassicalFourthNat.OuterPoint_91
  · exact WuPaper.ClassicalFourthNat.OuterPoint_92
  · exact WuPaper.ClassicalFourthNat.OuterPoint_93
  · exact WuPaper.ClassicalFourthNat.OuterPoint_94
  · exact WuPaper.ClassicalFourthNat.OuterPoint_95
  · exact WuPaper.ClassicalFourthNat.OuterPoint_96
  · exact WuPaper.ClassicalFourthNat.OuterPoint_97
  · exact WuPaper.ClassicalFourthNat.OuterPoint_98
  · exact WuPaper.ClassicalFourthNat.OuterPoint_99
  · exact WuPaper.ClassicalFourthNat.OuterPoint_100
  · exact WuPaper.ClassicalFourthNat.OuterPoint_101
  · exact WuPaper.ClassicalFourthNat.OuterPoint_102
  · exact WuPaper.ClassicalFourthNat.OuterPoint_103
  · exact WuPaper.ClassicalFourthNat.OuterPoint_104
  · exact WuPaper.ClassicalFourthNat.OuterPoint_105
  · exact WuPaper.ClassicalFourthNat.OuterPoint_106
  · exact WuPaper.ClassicalFourthNat.OuterPoint_107
  · exact WuPaper.ClassicalFourthNat.OuterPoint_108
  · exact WuPaper.ClassicalFourthNat.OuterPoint_109
  · exact WuPaper.ClassicalFourthNat.OuterPoint_110
  · exact WuPaper.ClassicalFourthNat.OuterPoint_111
  · exact WuPaper.ClassicalFourthNat.OuterPoint_112
  · exact WuPaper.ClassicalFourthNat.OuterPoint_113
  · exact WuPaper.ClassicalFourthNat.OuterPoint_114
  · exact WuPaper.ClassicalFourthNat.OuterPoint_115
  · exact WuPaper.ClassicalFourthNat.OuterPoint_116
  · exact WuPaper.ClassicalFourthNat.OuterPoint_117
  · exact WuPaper.ClassicalFourthNat.OuterPoint_118
  · exact WuPaper.ClassicalFourthNat.OuterPoint_119
  · exact WuPaper.ClassicalFourthNat.OuterPoint_120
  · exact WuPaper.ClassicalFourthNat.OuterPoint_121
  · exact WuPaper.ClassicalFourthNat.OuterPoint_122
  · exact WuPaper.ClassicalFourthNat.OuterPoint_123
  · exact WuPaper.ClassicalFourthNat.OuterPoint_124
  · exact WuPaper.ClassicalFourthNat.OuterPoint_125
  · exact WuPaper.ClassicalFourthNat.OuterPoint_126
  · exact WuPaper.ClassicalFourthNat.OuterPoint_127
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.OuterPoint_block_001
