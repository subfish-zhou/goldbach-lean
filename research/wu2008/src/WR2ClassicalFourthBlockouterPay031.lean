import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatouterPay031
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem outerPay_block_031 (j : Fin 64) (hj : 64*31+j.val < 10540) :
    OuterPay (64*31+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.outerPay_1984
  · exact WuPaper.ClassicalFourthNat.outerPay_1985
  · exact WuPaper.ClassicalFourthNat.outerPay_1986
  · exact WuPaper.ClassicalFourthNat.outerPay_1987
  · exact WuPaper.ClassicalFourthNat.outerPay_1988
  · exact WuPaper.ClassicalFourthNat.outerPay_1989
  · exact WuPaper.ClassicalFourthNat.outerPay_1990
  · exact WuPaper.ClassicalFourthNat.outerPay_1991
  · exact WuPaper.ClassicalFourthNat.outerPay_1992
  · exact WuPaper.ClassicalFourthNat.outerPay_1993
  · exact WuPaper.ClassicalFourthNat.outerPay_1994
  · exact WuPaper.ClassicalFourthNat.outerPay_1995
  · exact WuPaper.ClassicalFourthNat.outerPay_1996
  · exact WuPaper.ClassicalFourthNat.outerPay_1997
  · exact WuPaper.ClassicalFourthNat.outerPay_1998
  · exact WuPaper.ClassicalFourthNat.outerPay_1999
  · exact WuPaper.ClassicalFourthNat.outerPay_2000
  · exact WuPaper.ClassicalFourthNat.outerPay_2001
  · exact WuPaper.ClassicalFourthNat.outerPay_2002
  · exact WuPaper.ClassicalFourthNat.outerPay_2003
  · exact WuPaper.ClassicalFourthNat.outerPay_2004
  · exact WuPaper.ClassicalFourthNat.outerPay_2005
  · exact WuPaper.ClassicalFourthNat.outerPay_2006
  · exact WuPaper.ClassicalFourthNat.outerPay_2007
  · exact WuPaper.ClassicalFourthNat.outerPay_2008
  · exact WuPaper.ClassicalFourthNat.outerPay_2009
  · exact WuPaper.ClassicalFourthNat.outerPay_2010
  · exact WuPaper.ClassicalFourthNat.outerPay_2011
  · exact WuPaper.ClassicalFourthNat.outerPay_2012
  · exact WuPaper.ClassicalFourthNat.outerPay_2013
  · exact WuPaper.ClassicalFourthNat.outerPay_2014
  · exact WuPaper.ClassicalFourthNat.outerPay_2015
  · exact WuPaper.ClassicalFourthNat.outerPay_2016
  · exact WuPaper.ClassicalFourthNat.outerPay_2017
  · exact WuPaper.ClassicalFourthNat.outerPay_2018
  · exact WuPaper.ClassicalFourthNat.outerPay_2019
  · exact WuPaper.ClassicalFourthNat.outerPay_2020
  · exact WuPaper.ClassicalFourthNat.outerPay_2021
  · exact WuPaper.ClassicalFourthNat.outerPay_2022
  · exact WuPaper.ClassicalFourthNat.outerPay_2023
  · exact WuPaper.ClassicalFourthNat.outerPay_2024
  · exact WuPaper.ClassicalFourthNat.outerPay_2025
  · exact WuPaper.ClassicalFourthNat.outerPay_2026
  · exact WuPaper.ClassicalFourthNat.outerPay_2027
  · exact WuPaper.ClassicalFourthNat.outerPay_2028
  · exact WuPaper.ClassicalFourthNat.outerPay_2029
  · exact WuPaper.ClassicalFourthNat.outerPay_2030
  · exact WuPaper.ClassicalFourthNat.outerPay_2031
  · exact WuPaper.ClassicalFourthNat.outerPay_2032
  · exact WuPaper.ClassicalFourthNat.outerPay_2033
  · exact WuPaper.ClassicalFourthNat.outerPay_2034
  · exact WuPaper.ClassicalFourthNat.outerPay_2035
  · exact WuPaper.ClassicalFourthNat.outerPay_2036
  · exact WuPaper.ClassicalFourthNat.outerPay_2037
  · exact WuPaper.ClassicalFourthNat.outerPay_2038
  · exact WuPaper.ClassicalFourthNat.outerPay_2039
  · exact WuPaper.ClassicalFourthNat.outerPay_2040
  · exact WuPaper.ClassicalFourthNat.outerPay_2041
  · exact WuPaper.ClassicalFourthNat.outerPay_2042
  · exact WuPaper.ClassicalFourthNat.outerPay_2043
  · exact WuPaper.ClassicalFourthNat.outerPay_2044
  · exact WuPaper.ClassicalFourthNat.outerPay_2045
  · exact WuPaper.ClassicalFourthNat.outerPay_2046
  · exact WuPaper.ClassicalFourthNat.outerPay_2047
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.outerPay_block_031
