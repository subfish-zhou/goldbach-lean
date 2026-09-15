import E05SixthPayment

noncomputable section
open Wu2008DoubleSieve
open Wu2008DoubleSieve.SharpMassBalance
open Wu2008DoubleSieve.SharpLogRecurrence

namespace WuTarget.E05Sixth

theorem sixthCredit_exact :
    sixthCredit = 8066984221372818175051714346501/852403217090079068048245351272000 := by
  norm_num [sixthCredit,denominatorCap,a,b,lam,
    truncatedSixthLowerAlpha,truncatedSixthLowerBeta]

theorem sixthCredit_bounds : (9463/1000000:ℝ) < sixthCredit ∧
    sixthCredit < 9464/1000000 := by
  rw [sixthCredit_exact]
  norm_num

def ordinaryCredit : ℝ :=
  8066984221372818175051714346501/3409612868360316272192981405088000

theorem ordinaryCredit_eq : ordinaryCredit = sixthCredit/4 := by
  rw [sixthCredit_exact]
  norm_num [ordinaryCredit]

theorem ordinaryCredit_bounds : (2365/1000000:ℝ) < ordinaryCredit ∧
    ordinaryCredit < 2366/1000000 := by
  norm_num [ordinaryCredit]

def sixthLower : ℝ := Phase25.newSixth+sixthCredit

theorem sixthLower_exact : sixthLower =
    4791546038685779108598859719736646859698318702491580044634838565576580259629410262543761209306626076510312714948495836722766345438906967946254533251334982810497884808610993147634418286473375077/
    1266560227577067117922148411782929509583092926655824581729130538458223093026069800921359527583029777923355459074352756831259200270049778587584252271822884241375819569566884910171288622435944000 := by
  unfold sixthLower
  rw [sixthCredit_exact]
  norm_num [Phase25.newSixth,Phase25.endpointRational,Phase25.kx,
    Phase25.qb1,Phase25.qm1,Phase25.qp1,Phase25.ratioz,Phase25.ratiob,
    Phase25.ratiom,Phase25.ratiop,Phase25.polez,Phase25.poleb,Phase25.polem,
    Phase25.polep,a,b,truncatedSixthLowerAlpha,truncatedSixthLowerBeta,
    lowerLog,upperLog]

theorem sixthLower_bounds : (3783117/1000000:ℝ) ≤ sixthLower ∧
    sixthLower < 3783118/1000000 := by
  rw [sixthLower_exact]
  norm_num

theorem baseline_strictly_preserved : Phase25.newSixth < sixthLower := by
  unfold sixthLower
  linarith only [sixthCredit_bounds.1]

end WuTarget.E05Sixth
