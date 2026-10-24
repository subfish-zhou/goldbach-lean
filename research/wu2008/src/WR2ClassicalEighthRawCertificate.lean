import WR2ClassicalEighthRawGridBlock000
import WR2ClassicalEighthRawGridBlock001
import WR2ClassicalEighthRawGridBlock002
import WR2ClassicalEighthRawGridBlock003
import WR2ClassicalEighthRawGridBlock004
import WR2ClassicalEighthRawGridBlock005
import WR2ClassicalEighthRawGridBlock006
import WR2ClassicalEighthRawGridBlock007
import WR2ClassicalEighthRawGridBlock008
import WR2ClassicalEighthRawGridBlock009
import WR2ClassicalEighthRawGridBlock010
import WR2ClassicalEighthRawGridBlock011
import WR2ClassicalEighthRawGridBlock012
import WR2ClassicalEighthRawGridBlock013
import WR2ClassicalEighthRawGridBlock014
import WR2ClassicalEighthRawGridBlock015
import WR2ClassicalEighthRawGridBlock016
import WR2ClassicalEighthRawGridBlock017
import WR2ClassicalEighthRawGridBlock018
import WR2ClassicalEighthRawGridBlock019
import WR2ClassicalEighthRawGridBlock020
import WR2ClassicalEighthRawGridBlock021
import WR2ClassicalEighthRawGridBlock022
import WR2ClassicalEighthRawGridBlock023
import WR2ClassicalEighthRawGridBlock024
import WR2ClassicalEighthRawGridBlock025
import WR2ClassicalEighthRawGridBlock026
import WR2ClassicalEighthRawGridBlock027
import WR2ClassicalEighthRawGridBlock028
import WR2ClassicalEighthRawGridBlock029
import WR2ClassicalEighthRawGridBlock030
import WR2ClassicalEighthRawGridBlock031
import WR2ClassicalEighthRawGridBlock032
import WR2ClassicalEighthRawGridBlock033
import WR2ClassicalEighthRawGridBlock034
import WR2ClassicalEighthRawGridBlock035
import WR2ClassicalEighthRawGridBlock036
import WR2ClassicalEighthRawGridBlock037
import WR2ClassicalEighthRawGridBlock038
import WR2ClassicalEighthRawGridBlock039
import WR2ClassicalEighthRawGridBlock040
import WR2ClassicalEighthRawGridBlock041
import WR2ClassicalEighthRawGridBlock042
import WR2ClassicalEighthRawGridBlock043
import WR2ClassicalEighthRawGridBlock044
import WR2ClassicalEighthRawGridBlock045
import WR2ClassicalEighthRawGridBlock046
import WR2ClassicalEighthRawGridBlock047
import WR2ClassicalEighthRawGridBlock048
import WR2ClassicalEighthRawGridBlock049
import WR2ClassicalEighthRawGridBlock050
import WR2ClassicalEighthRawGridBlock051
import WR2ClassicalEighthRawGridBlock052
import WR2ClassicalEighthRawGridBlock053
import WR2ClassicalEighthRawGridBlock054
import WR2ClassicalEighthRawGridBlock055
import WR2ClassicalEighthRawGridBlock056
import WR2ClassicalEighthRawGridBlock057
import WR2ClassicalEighthRawGridBlock058
import WR2ClassicalEighthRawGridBlock059
import WR2ClassicalEighthRawGridBlock060
import WR2ClassicalEighthRawGridBlock061
import WR2ClassicalEighthRawGridBlock062
import WR2ClassicalEighthRawGridBlock063
import WR2ClassicalEighthRawGridBlock064
import WR2ClassicalEighthRawGridBlock065
import WR2ClassicalEighthRawGridBlock066
import WR2ClassicalEighthRawGridBlock067
import WR2ClassicalEighthRawGridBlock068
import WR2ClassicalEighthRawGridBlock069
import WR2ClassicalEighthRawGridBlock070
import WR2ClassicalEighthRawGridBlock071
import WR2ClassicalEighthRawGridBlock072
import WR2ClassicalEighthRawGridBlock073
import WR2ClassicalEighthRawGridBlock074
import WR2ClassicalEighthRawGridBlock075
import WR2ClassicalEighthRawGridBlock076
import WR2ClassicalEighthRawGridBlock077
import WR2ClassicalEighthRawGridBlock078
import WR2ClassicalEighthRawGridBlock079
import WR2ClassicalEighthRawGridBlock080
import WR2ClassicalEighthRawGridBlock081
import WR2ClassicalEighthRawGridBlock082
import WR2ClassicalEighthRawGridBlock083
import WR2ClassicalEighthRawGridBlock084
import WR2ClassicalEighthRawGridBlock085
import WR2ClassicalEighthRawGridBlock086
import WR2ClassicalEighthRawGridBlock087
import WR2ClassicalEighthRawGridBlock088
import WR2ClassicalEighthRawGridBlock089
import WR2ClassicalEighthRawGridBlock090
import WR2ClassicalEighthRawGridBlock091
import WR2ClassicalEighthRawGridBlock092
import WR2ClassicalEighthRawGridBlock093
import WR2ClassicalEighthRawGridBlock094
import WR2ClassicalEighthRawGridBlock095
import WR2ClassicalEighthRawGridBlock096
import WR2ClassicalEighthRawGridBlock097
import WR2ClassicalEighthRawGridBlock098
import WR2ClassicalEighthRawGridBlock099
import WR2ClassicalEighthRawGridBlock100
import WR2ClassicalEighthRawGridBlock101
import WR2ClassicalEighthRawGridBlock102
import WR2ClassicalEighthRawGridBlock103
import WR2ClassicalEighthRawGridBlock104
import WR2ClassicalEighthRawGridBlock105
import WR2ClassicalEighthRawGridBlock106
import WR2ClassicalEighthRawGridBlock107
import WR2ClassicalEighthRawGridBlock108
import WR2ClassicalEighthRawGridBlock109
import WR2ClassicalEighthRawGridBlock110
import WR2ClassicalEighthRawGridBlock111
import WR2ClassicalEighthRawGridBlock112
import WR2ClassicalEighthRawGridBlock113
import WR2ClassicalEighthRawGridBlock114
import WR2ClassicalEighthRawGridBlock115
import WR2ClassicalEighthRawGridBlock116
import WR2ClassicalEighthRawGridBlock117
import WR2ClassicalEighthRawGridBlock118
import WR2ClassicalEighthRawGridBlock119
import WR2ClassicalEighthRawGridBlock120
import WR2ClassicalEighthRawGridBlock121
import WR2ClassicalEighthRawGridBlock122
import WR2ClassicalEighthRawGridBlock123
import WR2ClassicalEighthRawGridBlock124
import WR2ClassicalEighthRawGridBlock125
import WR2ClassicalEighthRawGridBlock126
import WR2ClassicalEighthRawGridBlock127
noncomputable section
namespace WuPaper.ClassicalEighth
open Finset
set_option maxHeartbeats 4000000 in
theorem all_paid (i : ℕ) (hi : i < 2048) : upperValue ((point (i)+point ((i)+1))/2) ≤ payment (i) := by
  have hj : i%16 < 16 := Nat.mod_lt _ (by norm_num)
  have hb : i/16 < 128 := by omega
  have hh (b : Fin 128) : upperValue ((point (16*b.val+i%16)+point ((16*b.val+i%16)+1))/2) ≤ payment (16*b.val+i%16) := by
    fin_cases b
    · exact grid_block_000 ⟨i%16,hj⟩
    · exact grid_block_001 ⟨i%16,hj⟩
    · exact grid_block_002 ⟨i%16,hj⟩
    · exact grid_block_003 ⟨i%16,hj⟩
    · exact grid_block_004 ⟨i%16,hj⟩
    · exact grid_block_005 ⟨i%16,hj⟩
    · exact grid_block_006 ⟨i%16,hj⟩
    · exact grid_block_007 ⟨i%16,hj⟩
    · exact grid_block_008 ⟨i%16,hj⟩
    · exact grid_block_009 ⟨i%16,hj⟩
    · exact grid_block_010 ⟨i%16,hj⟩
    · exact grid_block_011 ⟨i%16,hj⟩
    · exact grid_block_012 ⟨i%16,hj⟩
    · exact grid_block_013 ⟨i%16,hj⟩
    · exact grid_block_014 ⟨i%16,hj⟩
    · exact grid_block_015 ⟨i%16,hj⟩
    · exact grid_block_016 ⟨i%16,hj⟩
    · exact grid_block_017 ⟨i%16,hj⟩
    · exact grid_block_018 ⟨i%16,hj⟩
    · exact grid_block_019 ⟨i%16,hj⟩
    · exact grid_block_020 ⟨i%16,hj⟩
    · exact grid_block_021 ⟨i%16,hj⟩
    · exact grid_block_022 ⟨i%16,hj⟩
    · exact grid_block_023 ⟨i%16,hj⟩
    · exact grid_block_024 ⟨i%16,hj⟩
    · exact grid_block_025 ⟨i%16,hj⟩
    · exact grid_block_026 ⟨i%16,hj⟩
    · exact grid_block_027 ⟨i%16,hj⟩
    · exact grid_block_028 ⟨i%16,hj⟩
    · exact grid_block_029 ⟨i%16,hj⟩
    · exact grid_block_030 ⟨i%16,hj⟩
    · exact grid_block_031 ⟨i%16,hj⟩
    · exact grid_block_032 ⟨i%16,hj⟩
    · exact grid_block_033 ⟨i%16,hj⟩
    · exact grid_block_034 ⟨i%16,hj⟩
    · exact grid_block_035 ⟨i%16,hj⟩
    · exact grid_block_036 ⟨i%16,hj⟩
    · exact grid_block_037 ⟨i%16,hj⟩
    · exact grid_block_038 ⟨i%16,hj⟩
    · exact grid_block_039 ⟨i%16,hj⟩
    · exact grid_block_040 ⟨i%16,hj⟩
    · exact grid_block_041 ⟨i%16,hj⟩
    · exact grid_block_042 ⟨i%16,hj⟩
    · exact grid_block_043 ⟨i%16,hj⟩
    · exact grid_block_044 ⟨i%16,hj⟩
    · exact grid_block_045 ⟨i%16,hj⟩
    · exact grid_block_046 ⟨i%16,hj⟩
    · exact grid_block_047 ⟨i%16,hj⟩
    · exact grid_block_048 ⟨i%16,hj⟩
    · exact grid_block_049 ⟨i%16,hj⟩
    · exact grid_block_050 ⟨i%16,hj⟩
    · exact grid_block_051 ⟨i%16,hj⟩
    · exact grid_block_052 ⟨i%16,hj⟩
    · exact grid_block_053 ⟨i%16,hj⟩
    · exact grid_block_054 ⟨i%16,hj⟩
    · exact grid_block_055 ⟨i%16,hj⟩
    · exact grid_block_056 ⟨i%16,hj⟩
    · exact grid_block_057 ⟨i%16,hj⟩
    · exact grid_block_058 ⟨i%16,hj⟩
    · exact grid_block_059 ⟨i%16,hj⟩
    · exact grid_block_060 ⟨i%16,hj⟩
    · exact grid_block_061 ⟨i%16,hj⟩
    · exact grid_block_062 ⟨i%16,hj⟩
    · exact grid_block_063 ⟨i%16,hj⟩
    · exact grid_block_064 ⟨i%16,hj⟩
    · exact grid_block_065 ⟨i%16,hj⟩
    · exact grid_block_066 ⟨i%16,hj⟩
    · exact grid_block_067 ⟨i%16,hj⟩
    · exact grid_block_068 ⟨i%16,hj⟩
    · exact grid_block_069 ⟨i%16,hj⟩
    · exact grid_block_070 ⟨i%16,hj⟩
    · exact grid_block_071 ⟨i%16,hj⟩
    · exact grid_block_072 ⟨i%16,hj⟩
    · exact grid_block_073 ⟨i%16,hj⟩
    · exact grid_block_074 ⟨i%16,hj⟩
    · exact grid_block_075 ⟨i%16,hj⟩
    · exact grid_block_076 ⟨i%16,hj⟩
    · exact grid_block_077 ⟨i%16,hj⟩
    · exact grid_block_078 ⟨i%16,hj⟩
    · exact grid_block_079 ⟨i%16,hj⟩
    · exact grid_block_080 ⟨i%16,hj⟩
    · exact grid_block_081 ⟨i%16,hj⟩
    · exact grid_block_082 ⟨i%16,hj⟩
    · exact grid_block_083 ⟨i%16,hj⟩
    · exact grid_block_084 ⟨i%16,hj⟩
    · exact grid_block_085 ⟨i%16,hj⟩
    · exact grid_block_086 ⟨i%16,hj⟩
    · exact grid_block_087 ⟨i%16,hj⟩
    · exact grid_block_088 ⟨i%16,hj⟩
    · exact grid_block_089 ⟨i%16,hj⟩
    · exact grid_block_090 ⟨i%16,hj⟩
    · exact grid_block_091 ⟨i%16,hj⟩
    · exact grid_block_092 ⟨i%16,hj⟩
    · exact grid_block_093 ⟨i%16,hj⟩
    · exact grid_block_094 ⟨i%16,hj⟩
    · exact grid_block_095 ⟨i%16,hj⟩
    · exact grid_block_096 ⟨i%16,hj⟩
    · exact grid_block_097 ⟨i%16,hj⟩
    · exact grid_block_098 ⟨i%16,hj⟩
    · exact grid_block_099 ⟨i%16,hj⟩
    · exact grid_block_100 ⟨i%16,hj⟩
    · exact grid_block_101 ⟨i%16,hj⟩
    · exact grid_block_102 ⟨i%16,hj⟩
    · exact grid_block_103 ⟨i%16,hj⟩
    · exact grid_block_104 ⟨i%16,hj⟩
    · exact grid_block_105 ⟨i%16,hj⟩
    · exact grid_block_106 ⟨i%16,hj⟩
    · exact grid_block_107 ⟨i%16,hj⟩
    · exact grid_block_108 ⟨i%16,hj⟩
    · exact grid_block_109 ⟨i%16,hj⟩
    · exact grid_block_110 ⟨i%16,hj⟩
    · exact grid_block_111 ⟨i%16,hj⟩
    · exact grid_block_112 ⟨i%16,hj⟩
    · exact grid_block_113 ⟨i%16,hj⟩
    · exact grid_block_114 ⟨i%16,hj⟩
    · exact grid_block_115 ⟨i%16,hj⟩
    · exact grid_block_116 ⟨i%16,hj⟩
    · exact grid_block_117 ⟨i%16,hj⟩
    · exact grid_block_118 ⟨i%16,hj⟩
    · exact grid_block_119 ⟨i%16,hj⟩
    · exact grid_block_120 ⟨i%16,hj⟩
    · exact grid_block_121 ⟨i%16,hj⟩
    · exact grid_block_122 ⟨i%16,hj⟩
    · exact grid_block_123 ⟨i%16,hj⟩
    · exact grid_block_124 ⟨i%16,hj⟩
    · exact grid_block_125 ⟨i%16,hj⟩
    · exact grid_block_126 ⟨i%16,hj⟩
    · exact grid_block_127 ⟨i%16,hj⟩
  have he : 16*(i/16)+i%16=i := by omega
  simpa only [he] using hh ⟨i/16,hb⟩
theorem raw_upper : 8*Wu2008DoubleSieve.SeventhEighth.J8 ≤ (52990343:ℝ)/10000000 := by
  apply (uniform_upper payment all_paid).trans
  simp only [payment,← sum_div,← Nat.cast_sum,numerator_sum]
  norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
end WuPaper.ClassicalEighth
#print axioms WuPaper.ClassicalEighth.raw_upper
