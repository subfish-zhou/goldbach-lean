import MathlibNt.SieveTheory.LiLiuGoldbachG11AuthorBuchstabIntegral

open MeasureTheory Set
open scoped Interval
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

set_option format.width 120
set_option pp.deepTerms true

/-- Definitional source-faithfulness check: the public object is the literal fourfold integral. -/
theorem goldbachG11AuthorBuchstabIntegral_eq_literal :
    goldbachG11AuthorBuchstabIntegral =
      ∫ r in (4/53 : ℝ)..(4/33), ∫ q in r..(4/33), ∫ s in q..(4/33), ∫ t in s..(4/33),
        goldbachG11AuthorWeight r * LiLiuPrereqBuchstab.buchstab ((1-r-q-s-t)/q) /
          (r*q^2*s*t) := rfl

#check @goldbachG11AuthorBuchstabIntegral
#print goldbachG11AuthorBuchstabIntegral
#print axioms goldbachG11AuthorBuchstabIntegral
#check @goldbachG11AuthorBuchstab_argument
#print axioms goldbachG11AuthorBuchstab_argument
#check @goldbachG11AuthorBuchstab_t_intervalIntegrable
#print axioms goldbachG11AuthorBuchstab_t_intervalIntegrable
#check @goldbachG11AuthorBuchstab_s_intervalIntegrable
#print axioms goldbachG11AuthorBuchstab_s_intervalIntegrable
#check @goldbachG11AuthorBuchstab_q_intervalIntegrable
#print axioms goldbachG11AuthorBuchstab_q_intervalIntegrable
#check @goldbachG11AuthorBuchstab_r_intervalIntegrable
#print axioms goldbachG11AuthorBuchstab_r_intervalIntegrable
#check @goldbachG11AuthorBuchstabIntegral_le_scalar
#print axioms goldbachG11AuthorBuchstabIntegral_le_scalar
#check @goldbachG11AuthorBuchstabIntegral_le_10191
#print axioms goldbachG11AuthorBuchstabIntegral_le_10191
#check @goldbachG11AuthorBuchstabIntegral_eq_literal
#print axioms goldbachG11AuthorBuchstabIntegral_eq_literal

-- Exact load-bearing upstream interfaces, not re-proved here.
#check @LiLiuBuchstabSharp.buchstab_sharp_tail_closed
#print axioms LiLiuBuchstabSharp.buchstab_sharp_tail_closed
#check @goldbachG11PrimeIntegral_author_scalar_le_10191
#print axioms goldbachG11PrimeIntegral_author_scalar_le_10191
#check @LiLiuPrereqBuchstab.continuous_buchstab
#print axioms LiLiuPrereqBuchstab.continuous_buchstab
#print goldbachG11AuthorWeight
#print goldbachG11PrimeIntegral