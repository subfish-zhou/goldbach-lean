import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay013
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_013 (j : Fin 64) (hj : 64*13+j.val < 10540) :
    BPay (64*13+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_832
  · exact WuPaper.ClassicalFourthNat.BPay_833
  · exact WuPaper.ClassicalFourthNat.BPay_834
  · exact WuPaper.ClassicalFourthNat.BPay_835
  · exact WuPaper.ClassicalFourthNat.BPay_836
  · exact WuPaper.ClassicalFourthNat.BPay_837
  · exact WuPaper.ClassicalFourthNat.BPay_838
  · exact WuPaper.ClassicalFourthNat.BPay_839
  · exact WuPaper.ClassicalFourthNat.BPay_840
  · exact WuPaper.ClassicalFourthNat.BPay_841
  · exact WuPaper.ClassicalFourthNat.BPay_842
  · exact WuPaper.ClassicalFourthNat.BPay_843
  · exact WuPaper.ClassicalFourthNat.BPay_844
  · exact WuPaper.ClassicalFourthNat.BPay_845
  · exact WuPaper.ClassicalFourthNat.BPay_846
  · exact WuPaper.ClassicalFourthNat.BPay_847
  · exact WuPaper.ClassicalFourthNat.BPay_848
  · exact WuPaper.ClassicalFourthNat.BPay_849
  · exact WuPaper.ClassicalFourthNat.BPay_850
  · exact WuPaper.ClassicalFourthNat.BPay_851
  · exact WuPaper.ClassicalFourthNat.BPay_852
  · exact WuPaper.ClassicalFourthNat.BPay_853
  · exact WuPaper.ClassicalFourthNat.BPay_854
  · exact WuPaper.ClassicalFourthNat.BPay_855
  · exact WuPaper.ClassicalFourthNat.BPay_856
  · exact WuPaper.ClassicalFourthNat.BPay_857
  · exact WuPaper.ClassicalFourthNat.BPay_858
  · exact WuPaper.ClassicalFourthNat.BPay_859
  · exact WuPaper.ClassicalFourthNat.BPay_860
  · exact WuPaper.ClassicalFourthNat.BPay_861
  · exact WuPaper.ClassicalFourthNat.BPay_862
  · exact WuPaper.ClassicalFourthNat.BPay_863
  · exact WuPaper.ClassicalFourthNat.BPay_864
  · exact WuPaper.ClassicalFourthNat.BPay_865
  · exact WuPaper.ClassicalFourthNat.BPay_866
  · exact WuPaper.ClassicalFourthNat.BPay_867
  · exact WuPaper.ClassicalFourthNat.BPay_868
  · exact WuPaper.ClassicalFourthNat.BPay_869
  · exact WuPaper.ClassicalFourthNat.BPay_870
  · exact WuPaper.ClassicalFourthNat.BPay_871
  · exact WuPaper.ClassicalFourthNat.BPay_872
  · exact WuPaper.ClassicalFourthNat.BPay_873
  · exact WuPaper.ClassicalFourthNat.BPay_874
  · exact WuPaper.ClassicalFourthNat.BPay_875
  · exact WuPaper.ClassicalFourthNat.BPay_876
  · exact WuPaper.ClassicalFourthNat.BPay_877
  · exact WuPaper.ClassicalFourthNat.BPay_878
  · exact WuPaper.ClassicalFourthNat.BPay_879
  · exact WuPaper.ClassicalFourthNat.BPay_880
  · exact WuPaper.ClassicalFourthNat.BPay_881
  · exact WuPaper.ClassicalFourthNat.BPay_882
  · exact WuPaper.ClassicalFourthNat.BPay_883
  · exact WuPaper.ClassicalFourthNat.BPay_884
  · exact WuPaper.ClassicalFourthNat.BPay_885
  · exact WuPaper.ClassicalFourthNat.BPay_886
  · exact WuPaper.ClassicalFourthNat.BPay_887
  · exact WuPaper.ClassicalFourthNat.BPay_888
  · exact WuPaper.ClassicalFourthNat.BPay_889
  · exact WuPaper.ClassicalFourthNat.BPay_890
  · exact WuPaper.ClassicalFourthNat.BPay_891
  · exact WuPaper.ClassicalFourthNat.BPay_892
  · exact WuPaper.ClassicalFourthNat.BPay_893
  · exact WuPaper.ClassicalFourthNat.BPay_894
  · exact WuPaper.ClassicalFourthNat.BPay_895
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_013
