import MathlibNt.SieveTheory.LiLiuGoldbachB10IntegralScalarUpper

set_option pp.universes false
set_option pp.fullNames true
set_option pp.proofs false

open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

-- Complete new public declaration inventory (exactly two theorems).
#check @goldbachB10I10_eight_mul_le_540996
#print axioms goldbachB10I10_eight_mul_le_540996
#check @goldbachB10SiftedCount_540996_upper
#print axioms goldbachB10SiftedCount_540996_upper

-- Literal production identities, fixed exponents, original input theorem.
#print goldbachB10I10
#print goldbachB10MainIntegral
#print goldbachB10Beta
#print goldbachB10Gamma
#check @goldbachB10SiftedCount
#check @goldbachB10I10_eq_singleIntegral
#print axioms goldbachB10I10_eq_singleIntegral
#check @goldbachB10SiftedCount_I10_upper
#print axioms goldbachB10SiftedCount_I10_upper