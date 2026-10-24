import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay058
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_058 (j : Fin 64) (hj : 64*58+j.val < 10540) :
    BPay (64*58+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_3712
  · exact WuPaper.ClassicalFourthNat.BPay_3713
  · exact WuPaper.ClassicalFourthNat.BPay_3714
  · exact WuPaper.ClassicalFourthNat.BPay_3715
  · exact WuPaper.ClassicalFourthNat.BPay_3716
  · exact WuPaper.ClassicalFourthNat.BPay_3717
  · exact WuPaper.ClassicalFourthNat.BPay_3718
  · exact WuPaper.ClassicalFourthNat.BPay_3719
  · exact WuPaper.ClassicalFourthNat.BPay_3720
  · exact WuPaper.ClassicalFourthNat.BPay_3721
  · exact WuPaper.ClassicalFourthNat.BPay_3722
  · exact WuPaper.ClassicalFourthNat.BPay_3723
  · exact WuPaper.ClassicalFourthNat.BPay_3724
  · exact WuPaper.ClassicalFourthNat.BPay_3725
  · exact WuPaper.ClassicalFourthNat.BPay_3726
  · exact WuPaper.ClassicalFourthNat.BPay_3727
  · exact WuPaper.ClassicalFourthNat.BPay_3728
  · exact WuPaper.ClassicalFourthNat.BPay_3729
  · exact WuPaper.ClassicalFourthNat.BPay_3730
  · exact WuPaper.ClassicalFourthNat.BPay_3731
  · exact WuPaper.ClassicalFourthNat.BPay_3732
  · exact WuPaper.ClassicalFourthNat.BPay_3733
  · exact WuPaper.ClassicalFourthNat.BPay_3734
  · exact WuPaper.ClassicalFourthNat.BPay_3735
  · exact WuPaper.ClassicalFourthNat.BPay_3736
  · exact WuPaper.ClassicalFourthNat.BPay_3737
  · exact WuPaper.ClassicalFourthNat.BPay_3738
  · exact WuPaper.ClassicalFourthNat.BPay_3739
  · exact WuPaper.ClassicalFourthNat.BPay_3740
  · exact WuPaper.ClassicalFourthNat.BPay_3741
  · exact WuPaper.ClassicalFourthNat.BPay_3742
  · exact WuPaper.ClassicalFourthNat.BPay_3743
  · exact WuPaper.ClassicalFourthNat.BPay_3744
  · exact WuPaper.ClassicalFourthNat.BPay_3745
  · exact WuPaper.ClassicalFourthNat.BPay_3746
  · exact WuPaper.ClassicalFourthNat.BPay_3747
  · exact WuPaper.ClassicalFourthNat.BPay_3748
  · exact WuPaper.ClassicalFourthNat.BPay_3749
  · exact WuPaper.ClassicalFourthNat.BPay_3750
  · exact WuPaper.ClassicalFourthNat.BPay_3751
  · exact WuPaper.ClassicalFourthNat.BPay_3752
  · exact WuPaper.ClassicalFourthNat.BPay_3753
  · exact WuPaper.ClassicalFourthNat.BPay_3754
  · exact WuPaper.ClassicalFourthNat.BPay_3755
  · exact WuPaper.ClassicalFourthNat.BPay_3756
  · exact WuPaper.ClassicalFourthNat.BPay_3757
  · exact WuPaper.ClassicalFourthNat.BPay_3758
  · exact WuPaper.ClassicalFourthNat.BPay_3759
  · exact WuPaper.ClassicalFourthNat.BPay_3760
  · exact WuPaper.ClassicalFourthNat.BPay_3761
  · exact WuPaper.ClassicalFourthNat.BPay_3762
  · exact WuPaper.ClassicalFourthNat.BPay_3763
  · exact WuPaper.ClassicalFourthNat.BPay_3764
  · exact WuPaper.ClassicalFourthNat.BPay_3765
  · exact WuPaper.ClassicalFourthNat.BPay_3766
  · exact WuPaper.ClassicalFourthNat.BPay_3767
  · exact WuPaper.ClassicalFourthNat.BPay_3768
  · exact WuPaper.ClassicalFourthNat.BPay_3769
  · exact WuPaper.ClassicalFourthNat.BPay_3770
  · exact WuPaper.ClassicalFourthNat.BPay_3771
  · exact WuPaper.ClassicalFourthNat.BPay_3772
  · exact WuPaper.ClassicalFourthNat.BPay_3773
  · exact WuPaper.ClassicalFourthNat.BPay_3774
  · exact WuPaper.ClassicalFourthNat.BPay_3775
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_058
