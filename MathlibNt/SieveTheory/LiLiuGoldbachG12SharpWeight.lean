import MathlibNt.SieveTheory.LiLiuGoldbachG12AuthorWeightBounds
noncomputable section
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
namespace G12SharpWeight
/-- The original low/high Buchstab bounds, with the junction assigned high. -/
def factor (u : ℝ) : ℝ := if u < (1/10 : ℝ) then 561990/1000000 else 564383/1000000
def weight (u : ℝ) : ℝ := factor u*goldbachG11AuthorWeight u
end G12SharpWeight
