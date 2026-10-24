import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatouterPay013
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem outerPay_block_013 (j : Fin 64) (hj : 64*13+j.val < 10540) :
    OuterPay (64*13+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.outerPay_832
  · exact WuPaper.ClassicalFourthNat.outerPay_833
  · exact WuPaper.ClassicalFourthNat.outerPay_834
  · exact WuPaper.ClassicalFourthNat.outerPay_835
  · exact WuPaper.ClassicalFourthNat.outerPay_836
  · exact WuPaper.ClassicalFourthNat.outerPay_837
  · exact WuPaper.ClassicalFourthNat.outerPay_838
  · exact WuPaper.ClassicalFourthNat.outerPay_839
  · exact WuPaper.ClassicalFourthNat.outerPay_840
  · exact WuPaper.ClassicalFourthNat.outerPay_841
  · exact WuPaper.ClassicalFourthNat.outerPay_842
  · exact WuPaper.ClassicalFourthNat.outerPay_843
  · exact WuPaper.ClassicalFourthNat.outerPay_844
  · exact WuPaper.ClassicalFourthNat.outerPay_845
  · exact WuPaper.ClassicalFourthNat.outerPay_846
  · exact WuPaper.ClassicalFourthNat.outerPay_847
  · exact WuPaper.ClassicalFourthNat.outerPay_848
  · exact WuPaper.ClassicalFourthNat.outerPay_849
  · exact WuPaper.ClassicalFourthNat.outerPay_850
  · exact WuPaper.ClassicalFourthNat.outerPay_851
  · exact WuPaper.ClassicalFourthNat.outerPay_852
  · exact WuPaper.ClassicalFourthNat.outerPay_853
  · exact WuPaper.ClassicalFourthNat.outerPay_854
  · exact WuPaper.ClassicalFourthNat.outerPay_855
  · exact WuPaper.ClassicalFourthNat.outerPay_856
  · exact WuPaper.ClassicalFourthNat.outerPay_857
  · exact WuPaper.ClassicalFourthNat.outerPay_858
  · exact WuPaper.ClassicalFourthNat.outerPay_859
  · exact WuPaper.ClassicalFourthNat.outerPay_860
  · exact WuPaper.ClassicalFourthNat.outerPay_861
  · exact WuPaper.ClassicalFourthNat.outerPay_862
  · exact WuPaper.ClassicalFourthNat.outerPay_863
  · exact WuPaper.ClassicalFourthNat.outerPay_864
  · exact WuPaper.ClassicalFourthNat.outerPay_865
  · exact WuPaper.ClassicalFourthNat.outerPay_866
  · exact WuPaper.ClassicalFourthNat.outerPay_867
  · exact WuPaper.ClassicalFourthNat.outerPay_868
  · exact WuPaper.ClassicalFourthNat.outerPay_869
  · exact WuPaper.ClassicalFourthNat.outerPay_870
  · exact WuPaper.ClassicalFourthNat.outerPay_871
  · exact WuPaper.ClassicalFourthNat.outerPay_872
  · exact WuPaper.ClassicalFourthNat.outerPay_873
  · exact WuPaper.ClassicalFourthNat.outerPay_874
  · exact WuPaper.ClassicalFourthNat.outerPay_875
  · exact WuPaper.ClassicalFourthNat.outerPay_876
  · exact WuPaper.ClassicalFourthNat.outerPay_877
  · exact WuPaper.ClassicalFourthNat.outerPay_878
  · exact WuPaper.ClassicalFourthNat.outerPay_879
  · exact WuPaper.ClassicalFourthNat.outerPay_880
  · exact WuPaper.ClassicalFourthNat.outerPay_881
  · exact WuPaper.ClassicalFourthNat.outerPay_882
  · exact WuPaper.ClassicalFourthNat.outerPay_883
  · exact WuPaper.ClassicalFourthNat.outerPay_884
  · exact WuPaper.ClassicalFourthNat.outerPay_885
  · exact WuPaper.ClassicalFourthNat.outerPay_886
  · exact WuPaper.ClassicalFourthNat.outerPay_887
  · exact WuPaper.ClassicalFourthNat.outerPay_888
  · exact WuPaper.ClassicalFourthNat.outerPay_889
  · exact WuPaper.ClassicalFourthNat.outerPay_890
  · exact WuPaper.ClassicalFourthNat.outerPay_891
  · exact WuPaper.ClassicalFourthNat.outerPay_892
  · exact WuPaper.ClassicalFourthNat.outerPay_893
  · exact WuPaper.ClassicalFourthNat.outerPay_894
  · exact WuPaper.ClassicalFourthNat.outerPay_895
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.outerPay_block_013
