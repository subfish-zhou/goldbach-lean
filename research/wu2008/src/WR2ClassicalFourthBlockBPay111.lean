import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay111
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_111 (j : Fin 64) (hj : 64*111+j.val < 10540) :
    BPay (64*111+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_7104
  · exact WuPaper.ClassicalFourthNat.BPay_7105
  · exact WuPaper.ClassicalFourthNat.BPay_7106
  · exact WuPaper.ClassicalFourthNat.BPay_7107
  · exact WuPaper.ClassicalFourthNat.BPay_7108
  · exact WuPaper.ClassicalFourthNat.BPay_7109
  · exact WuPaper.ClassicalFourthNat.BPay_7110
  · exact WuPaper.ClassicalFourthNat.BPay_7111
  · exact WuPaper.ClassicalFourthNat.BPay_7112
  · exact WuPaper.ClassicalFourthNat.BPay_7113
  · exact WuPaper.ClassicalFourthNat.BPay_7114
  · exact WuPaper.ClassicalFourthNat.BPay_7115
  · exact WuPaper.ClassicalFourthNat.BPay_7116
  · exact WuPaper.ClassicalFourthNat.BPay_7117
  · exact WuPaper.ClassicalFourthNat.BPay_7118
  · exact WuPaper.ClassicalFourthNat.BPay_7119
  · exact WuPaper.ClassicalFourthNat.BPay_7120
  · exact WuPaper.ClassicalFourthNat.BPay_7121
  · exact WuPaper.ClassicalFourthNat.BPay_7122
  · exact WuPaper.ClassicalFourthNat.BPay_7123
  · exact WuPaper.ClassicalFourthNat.BPay_7124
  · exact WuPaper.ClassicalFourthNat.BPay_7125
  · exact WuPaper.ClassicalFourthNat.BPay_7126
  · exact WuPaper.ClassicalFourthNat.BPay_7127
  · exact WuPaper.ClassicalFourthNat.BPay_7128
  · exact WuPaper.ClassicalFourthNat.BPay_7129
  · exact WuPaper.ClassicalFourthNat.BPay_7130
  · exact WuPaper.ClassicalFourthNat.BPay_7131
  · exact WuPaper.ClassicalFourthNat.BPay_7132
  · exact WuPaper.ClassicalFourthNat.BPay_7133
  · exact WuPaper.ClassicalFourthNat.BPay_7134
  · exact WuPaper.ClassicalFourthNat.BPay_7135
  · exact WuPaper.ClassicalFourthNat.BPay_7136
  · exact WuPaper.ClassicalFourthNat.BPay_7137
  · exact WuPaper.ClassicalFourthNat.BPay_7138
  · exact WuPaper.ClassicalFourthNat.BPay_7139
  · exact WuPaper.ClassicalFourthNat.BPay_7140
  · exact WuPaper.ClassicalFourthNat.BPay_7141
  · exact WuPaper.ClassicalFourthNat.BPay_7142
  · exact WuPaper.ClassicalFourthNat.BPay_7143
  · exact WuPaper.ClassicalFourthNat.BPay_7144
  · exact WuPaper.ClassicalFourthNat.BPay_7145
  · exact WuPaper.ClassicalFourthNat.BPay_7146
  · exact WuPaper.ClassicalFourthNat.BPay_7147
  · exact WuPaper.ClassicalFourthNat.BPay_7148
  · exact WuPaper.ClassicalFourthNat.BPay_7149
  · exact WuPaper.ClassicalFourthNat.BPay_7150
  · exact WuPaper.ClassicalFourthNat.BPay_7151
  · exact WuPaper.ClassicalFourthNat.BPay_7152
  · exact WuPaper.ClassicalFourthNat.BPay_7153
  · exact WuPaper.ClassicalFourthNat.BPay_7154
  · exact WuPaper.ClassicalFourthNat.BPay_7155
  · exact WuPaper.ClassicalFourthNat.BPay_7156
  · exact WuPaper.ClassicalFourthNat.BPay_7157
  · exact WuPaper.ClassicalFourthNat.BPay_7158
  · exact WuPaper.ClassicalFourthNat.BPay_7159
  · exact WuPaper.ClassicalFourthNat.BPay_7160
  · exact WuPaper.ClassicalFourthNat.BPay_7161
  · exact WuPaper.ClassicalFourthNat.BPay_7162
  · exact WuPaper.ClassicalFourthNat.BPay_7163
  · exact WuPaper.ClassicalFourthNat.BPay_7164
  · exact WuPaper.ClassicalFourthNat.BPay_7165
  · exact WuPaper.ClassicalFourthNat.BPay_7166
  · exact WuPaper.ClassicalFourthNat.BPay_7167
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_111
