import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay063
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_063 (j : Fin 64) (hj : 64*63+j.val < 10540) :
    BPay (64*63+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_4032
  · exact WuPaper.ClassicalFourthNat.BPay_4033
  · exact WuPaper.ClassicalFourthNat.BPay_4034
  · exact WuPaper.ClassicalFourthNat.BPay_4035
  · exact WuPaper.ClassicalFourthNat.BPay_4036
  · exact WuPaper.ClassicalFourthNat.BPay_4037
  · exact WuPaper.ClassicalFourthNat.BPay_4038
  · exact WuPaper.ClassicalFourthNat.BPay_4039
  · exact WuPaper.ClassicalFourthNat.BPay_4040
  · exact WuPaper.ClassicalFourthNat.BPay_4041
  · exact WuPaper.ClassicalFourthNat.BPay_4042
  · exact WuPaper.ClassicalFourthNat.BPay_4043
  · exact WuPaper.ClassicalFourthNat.BPay_4044
  · exact WuPaper.ClassicalFourthNat.BPay_4045
  · exact WuPaper.ClassicalFourthNat.BPay_4046
  · exact WuPaper.ClassicalFourthNat.BPay_4047
  · exact WuPaper.ClassicalFourthNat.BPay_4048
  · exact WuPaper.ClassicalFourthNat.BPay_4049
  · exact WuPaper.ClassicalFourthNat.BPay_4050
  · exact WuPaper.ClassicalFourthNat.BPay_4051
  · exact WuPaper.ClassicalFourthNat.BPay_4052
  · exact WuPaper.ClassicalFourthNat.BPay_4053
  · exact WuPaper.ClassicalFourthNat.BPay_4054
  · exact WuPaper.ClassicalFourthNat.BPay_4055
  · exact WuPaper.ClassicalFourthNat.BPay_4056
  · exact WuPaper.ClassicalFourthNat.BPay_4057
  · exact WuPaper.ClassicalFourthNat.BPay_4058
  · exact WuPaper.ClassicalFourthNat.BPay_4059
  · exact WuPaper.ClassicalFourthNat.BPay_4060
  · exact WuPaper.ClassicalFourthNat.BPay_4061
  · exact WuPaper.ClassicalFourthNat.BPay_4062
  · exact WuPaper.ClassicalFourthNat.BPay_4063
  · exact WuPaper.ClassicalFourthNat.BPay_4064
  · exact WuPaper.ClassicalFourthNat.BPay_4065
  · exact WuPaper.ClassicalFourthNat.BPay_4066
  · exact WuPaper.ClassicalFourthNat.BPay_4067
  · exact WuPaper.ClassicalFourthNat.BPay_4068
  · exact WuPaper.ClassicalFourthNat.BPay_4069
  · exact WuPaper.ClassicalFourthNat.BPay_4070
  · exact WuPaper.ClassicalFourthNat.BPay_4071
  · exact WuPaper.ClassicalFourthNat.BPay_4072
  · exact WuPaper.ClassicalFourthNat.BPay_4073
  · exact WuPaper.ClassicalFourthNat.BPay_4074
  · exact WuPaper.ClassicalFourthNat.BPay_4075
  · exact WuPaper.ClassicalFourthNat.BPay_4076
  · exact WuPaper.ClassicalFourthNat.BPay_4077
  · exact WuPaper.ClassicalFourthNat.BPay_4078
  · exact WuPaper.ClassicalFourthNat.BPay_4079
  · exact WuPaper.ClassicalFourthNat.BPay_4080
  · exact WuPaper.ClassicalFourthNat.BPay_4081
  · exact WuPaper.ClassicalFourthNat.BPay_4082
  · exact WuPaper.ClassicalFourthNat.BPay_4083
  · exact WuPaper.ClassicalFourthNat.BPay_4084
  · exact WuPaper.ClassicalFourthNat.BPay_4085
  · exact WuPaper.ClassicalFourthNat.BPay_4086
  · exact WuPaper.ClassicalFourthNat.BPay_4087
  · exact WuPaper.ClassicalFourthNat.BPay_4088
  · exact WuPaper.ClassicalFourthNat.BPay_4089
  · exact WuPaper.ClassicalFourthNat.BPay_4090
  · exact WuPaper.ClassicalFourthNat.BPay_4091
  · exact WuPaper.ClassicalFourthNat.BPay_4092
  · exact WuPaper.ClassicalFourthNat.BPay_4093
  · exact WuPaper.ClassicalFourthNat.BPay_4094
  · exact WuPaper.ClassicalFourthNat.BPay_4095
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_063
