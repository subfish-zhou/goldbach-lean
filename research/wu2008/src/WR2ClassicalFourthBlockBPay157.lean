import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay157
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_157 (j : Fin 64) (hj : 64*157+j.val < 10540) :
    BPay (64*157+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_10048
  · exact WuPaper.ClassicalFourthNat.BPay_10049
  · exact WuPaper.ClassicalFourthNat.BPay_10050
  · exact WuPaper.ClassicalFourthNat.BPay_10051
  · exact WuPaper.ClassicalFourthNat.BPay_10052
  · exact WuPaper.ClassicalFourthNat.BPay_10053
  · exact WuPaper.ClassicalFourthNat.BPay_10054
  · exact WuPaper.ClassicalFourthNat.BPay_10055
  · exact WuPaper.ClassicalFourthNat.BPay_10056
  · exact WuPaper.ClassicalFourthNat.BPay_10057
  · exact WuPaper.ClassicalFourthNat.BPay_10058
  · exact WuPaper.ClassicalFourthNat.BPay_10059
  · exact WuPaper.ClassicalFourthNat.BPay_10060
  · exact WuPaper.ClassicalFourthNat.BPay_10061
  · exact WuPaper.ClassicalFourthNat.BPay_10062
  · exact WuPaper.ClassicalFourthNat.BPay_10063
  · exact WuPaper.ClassicalFourthNat.BPay_10064
  · exact WuPaper.ClassicalFourthNat.BPay_10065
  · exact WuPaper.ClassicalFourthNat.BPay_10066
  · exact WuPaper.ClassicalFourthNat.BPay_10067
  · exact WuPaper.ClassicalFourthNat.BPay_10068
  · exact WuPaper.ClassicalFourthNat.BPay_10069
  · exact WuPaper.ClassicalFourthNat.BPay_10070
  · exact WuPaper.ClassicalFourthNat.BPay_10071
  · exact WuPaper.ClassicalFourthNat.BPay_10072
  · exact WuPaper.ClassicalFourthNat.BPay_10073
  · exact WuPaper.ClassicalFourthNat.BPay_10074
  · exact WuPaper.ClassicalFourthNat.BPay_10075
  · exact WuPaper.ClassicalFourthNat.BPay_10076
  · exact WuPaper.ClassicalFourthNat.BPay_10077
  · exact WuPaper.ClassicalFourthNat.BPay_10078
  · exact WuPaper.ClassicalFourthNat.BPay_10079
  · exact WuPaper.ClassicalFourthNat.BPay_10080
  · exact WuPaper.ClassicalFourthNat.BPay_10081
  · exact WuPaper.ClassicalFourthNat.BPay_10082
  · exact WuPaper.ClassicalFourthNat.BPay_10083
  · exact WuPaper.ClassicalFourthNat.BPay_10084
  · exact WuPaper.ClassicalFourthNat.BPay_10085
  · exact WuPaper.ClassicalFourthNat.BPay_10086
  · exact WuPaper.ClassicalFourthNat.BPay_10087
  · exact WuPaper.ClassicalFourthNat.BPay_10088
  · exact WuPaper.ClassicalFourthNat.BPay_10089
  · exact WuPaper.ClassicalFourthNat.BPay_10090
  · exact WuPaper.ClassicalFourthNat.BPay_10091
  · exact WuPaper.ClassicalFourthNat.BPay_10092
  · exact WuPaper.ClassicalFourthNat.BPay_10093
  · exact WuPaper.ClassicalFourthNat.BPay_10094
  · exact WuPaper.ClassicalFourthNat.BPay_10095
  · exact WuPaper.ClassicalFourthNat.BPay_10096
  · exact WuPaper.ClassicalFourthNat.BPay_10097
  · exact WuPaper.ClassicalFourthNat.BPay_10098
  · exact WuPaper.ClassicalFourthNat.BPay_10099
  · exact WuPaper.ClassicalFourthNat.BPay_10100
  · exact WuPaper.ClassicalFourthNat.BPay_10101
  · exact WuPaper.ClassicalFourthNat.BPay_10102
  · exact WuPaper.ClassicalFourthNat.BPay_10103
  · exact WuPaper.ClassicalFourthNat.BPay_10104
  · exact WuPaper.ClassicalFourthNat.BPay_10105
  · exact WuPaper.ClassicalFourthNat.BPay_10106
  · exact WuPaper.ClassicalFourthNat.BPay_10107
  · exact WuPaper.ClassicalFourthNat.BPay_10108
  · exact WuPaper.ClassicalFourthNat.BPay_10109
  · exact WuPaper.ClassicalFourthNat.BPay_10110
  · exact WuPaper.ClassicalFourthNat.BPay_10111
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_157
