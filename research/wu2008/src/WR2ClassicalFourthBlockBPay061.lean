import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay061
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_061 (j : Fin 64) (hj : 64*61+j.val < 10540) :
    BPay (64*61+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_3904
  · exact WuPaper.ClassicalFourthNat.BPay_3905
  · exact WuPaper.ClassicalFourthNat.BPay_3906
  · exact WuPaper.ClassicalFourthNat.BPay_3907
  · exact WuPaper.ClassicalFourthNat.BPay_3908
  · exact WuPaper.ClassicalFourthNat.BPay_3909
  · exact WuPaper.ClassicalFourthNat.BPay_3910
  · exact WuPaper.ClassicalFourthNat.BPay_3911
  · exact WuPaper.ClassicalFourthNat.BPay_3912
  · exact WuPaper.ClassicalFourthNat.BPay_3913
  · exact WuPaper.ClassicalFourthNat.BPay_3914
  · exact WuPaper.ClassicalFourthNat.BPay_3915
  · exact WuPaper.ClassicalFourthNat.BPay_3916
  · exact WuPaper.ClassicalFourthNat.BPay_3917
  · exact WuPaper.ClassicalFourthNat.BPay_3918
  · exact WuPaper.ClassicalFourthNat.BPay_3919
  · exact WuPaper.ClassicalFourthNat.BPay_3920
  · exact WuPaper.ClassicalFourthNat.BPay_3921
  · exact WuPaper.ClassicalFourthNat.BPay_3922
  · exact WuPaper.ClassicalFourthNat.BPay_3923
  · exact WuPaper.ClassicalFourthNat.BPay_3924
  · exact WuPaper.ClassicalFourthNat.BPay_3925
  · exact WuPaper.ClassicalFourthNat.BPay_3926
  · exact WuPaper.ClassicalFourthNat.BPay_3927
  · exact WuPaper.ClassicalFourthNat.BPay_3928
  · exact WuPaper.ClassicalFourthNat.BPay_3929
  · exact WuPaper.ClassicalFourthNat.BPay_3930
  · exact WuPaper.ClassicalFourthNat.BPay_3931
  · exact WuPaper.ClassicalFourthNat.BPay_3932
  · exact WuPaper.ClassicalFourthNat.BPay_3933
  · exact WuPaper.ClassicalFourthNat.BPay_3934
  · exact WuPaper.ClassicalFourthNat.BPay_3935
  · exact WuPaper.ClassicalFourthNat.BPay_3936
  · exact WuPaper.ClassicalFourthNat.BPay_3937
  · exact WuPaper.ClassicalFourthNat.BPay_3938
  · exact WuPaper.ClassicalFourthNat.BPay_3939
  · exact WuPaper.ClassicalFourthNat.BPay_3940
  · exact WuPaper.ClassicalFourthNat.BPay_3941
  · exact WuPaper.ClassicalFourthNat.BPay_3942
  · exact WuPaper.ClassicalFourthNat.BPay_3943
  · exact WuPaper.ClassicalFourthNat.BPay_3944
  · exact WuPaper.ClassicalFourthNat.BPay_3945
  · exact WuPaper.ClassicalFourthNat.BPay_3946
  · exact WuPaper.ClassicalFourthNat.BPay_3947
  · exact WuPaper.ClassicalFourthNat.BPay_3948
  · exact WuPaper.ClassicalFourthNat.BPay_3949
  · exact WuPaper.ClassicalFourthNat.BPay_3950
  · exact WuPaper.ClassicalFourthNat.BPay_3951
  · exact WuPaper.ClassicalFourthNat.BPay_3952
  · exact WuPaper.ClassicalFourthNat.BPay_3953
  · exact WuPaper.ClassicalFourthNat.BPay_3954
  · exact WuPaper.ClassicalFourthNat.BPay_3955
  · exact WuPaper.ClassicalFourthNat.BPay_3956
  · exact WuPaper.ClassicalFourthNat.BPay_3957
  · exact WuPaper.ClassicalFourthNat.BPay_3958
  · exact WuPaper.ClassicalFourthNat.BPay_3959
  · exact WuPaper.ClassicalFourthNat.BPay_3960
  · exact WuPaper.ClassicalFourthNat.BPay_3961
  · exact WuPaper.ClassicalFourthNat.BPay_3962
  · exact WuPaper.ClassicalFourthNat.BPay_3963
  · exact WuPaper.ClassicalFourthNat.BPay_3964
  · exact WuPaper.ClassicalFourthNat.BPay_3965
  · exact WuPaper.ClassicalFourthNat.BPay_3966
  · exact WuPaper.ClassicalFourthNat.BPay_3967
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_061
