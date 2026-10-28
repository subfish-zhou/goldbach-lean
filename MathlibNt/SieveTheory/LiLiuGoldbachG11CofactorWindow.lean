import MathlibNt.SieveTheory.LiLiuGoldbachG11BuchstabGeometry
import MathlibNt.SieveTheory.LiLiuGoldbachG11RoughQuotient
import MathlibNt.SieveTheory.LiLiuPrereqBuchstabCount


set_option autoImplicit false

open LiLiuPrereqBuchstab

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

theorem goldbachG11_rough_iff_survives (q : ℝ) (m : ℕ) :
    Rough q m ↔ SurvivesSieve 1 q m :=
  (goldbachG11_survives_one_iff q m).symm


end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig