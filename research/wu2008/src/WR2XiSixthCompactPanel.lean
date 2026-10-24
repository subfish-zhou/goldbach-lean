import WR2XiSixthTailCertificate
import WR2XiSixthQuadrature
noncomputable section
namespace WuPaper.R2Xi.SixthContinuous
open Real Set QuarterTrim NodeExtension SourceRational WuSource.SrcSixthGain

theorem compact_panel_paid {a b p d q : ℝ} {k : ℕ}
    (ha : 2 ≤ a) (hab : a ≤ b) (hb : b ≤ endpoint)
    (hk : 2 ≤ k) (hk11 : k ≤ 11)
    (hs0 : profileLeft k ≤ b-1) (hs1 : b-1 ≤ rNode k)
    (hp0 : 0 ≤ p)
    (hp : p ≤ upperLower k*SourceLogRational.lower (rNode k/(b-1))+
      (tailNumerator k:ℝ)/1000000000000)
    (hd : d ≤ densityLower a b) (hq : q ≤ 8*(b-a)*(d*p)) :
    q ≤ 8*(b-a)*(densityLower a b*pointLower b) := by
  have hp' := hp.trans (compact_point_lower hk hk11 hs0 hs1)
  exact hq.trans (mul_le_mul_of_nonneg_left
    (mul_le_mul hd hp' hp0 (densityLower_nonneg ha hab hb))
    (mul_nonneg (by norm_num) (sub_nonneg.mpr hab)))

end WuPaper.R2Xi.SixthContinuous
#print axioms WuPaper.R2Xi.SixthContinuous.compact_panel_paid
