import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatCPay031
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem CPay_block_031 (j : Fin 64) (hj : 64*31+j.val < 2540) :
    CPay (64*31+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.CPay_1984
  · exact WuPaper.ClassicalFourthNat.CPay_1985
  · exact WuPaper.ClassicalFourthNat.CPay_1986
  · exact WuPaper.ClassicalFourthNat.CPay_1987
  · exact WuPaper.ClassicalFourthNat.CPay_1988
  · exact WuPaper.ClassicalFourthNat.CPay_1989
  · exact WuPaper.ClassicalFourthNat.CPay_1990
  · exact WuPaper.ClassicalFourthNat.CPay_1991
  · exact WuPaper.ClassicalFourthNat.CPay_1992
  · exact WuPaper.ClassicalFourthNat.CPay_1993
  · exact WuPaper.ClassicalFourthNat.CPay_1994
  · exact WuPaper.ClassicalFourthNat.CPay_1995
  · exact WuPaper.ClassicalFourthNat.CPay_1996
  · exact WuPaper.ClassicalFourthNat.CPay_1997
  · exact WuPaper.ClassicalFourthNat.CPay_1998
  · exact WuPaper.ClassicalFourthNat.CPay_1999
  · exact WuPaper.ClassicalFourthNat.CPay_2000
  · exact WuPaper.ClassicalFourthNat.CPay_2001
  · exact WuPaper.ClassicalFourthNat.CPay_2002
  · exact WuPaper.ClassicalFourthNat.CPay_2003
  · exact WuPaper.ClassicalFourthNat.CPay_2004
  · exact WuPaper.ClassicalFourthNat.CPay_2005
  · exact WuPaper.ClassicalFourthNat.CPay_2006
  · exact WuPaper.ClassicalFourthNat.CPay_2007
  · exact WuPaper.ClassicalFourthNat.CPay_2008
  · exact WuPaper.ClassicalFourthNat.CPay_2009
  · exact WuPaper.ClassicalFourthNat.CPay_2010
  · exact WuPaper.ClassicalFourthNat.CPay_2011
  · exact WuPaper.ClassicalFourthNat.CPay_2012
  · exact WuPaper.ClassicalFourthNat.CPay_2013
  · exact WuPaper.ClassicalFourthNat.CPay_2014
  · exact WuPaper.ClassicalFourthNat.CPay_2015
  · exact WuPaper.ClassicalFourthNat.CPay_2016
  · exact WuPaper.ClassicalFourthNat.CPay_2017
  · exact WuPaper.ClassicalFourthNat.CPay_2018
  · exact WuPaper.ClassicalFourthNat.CPay_2019
  · exact WuPaper.ClassicalFourthNat.CPay_2020
  · exact WuPaper.ClassicalFourthNat.CPay_2021
  · exact WuPaper.ClassicalFourthNat.CPay_2022
  · exact WuPaper.ClassicalFourthNat.CPay_2023
  · exact WuPaper.ClassicalFourthNat.CPay_2024
  · exact WuPaper.ClassicalFourthNat.CPay_2025
  · exact WuPaper.ClassicalFourthNat.CPay_2026
  · exact WuPaper.ClassicalFourthNat.CPay_2027
  · exact WuPaper.ClassicalFourthNat.CPay_2028
  · exact WuPaper.ClassicalFourthNat.CPay_2029
  · exact WuPaper.ClassicalFourthNat.CPay_2030
  · exact WuPaper.ClassicalFourthNat.CPay_2031
  · exact WuPaper.ClassicalFourthNat.CPay_2032
  · exact WuPaper.ClassicalFourthNat.CPay_2033
  · exact WuPaper.ClassicalFourthNat.CPay_2034
  · exact WuPaper.ClassicalFourthNat.CPay_2035
  · exact WuPaper.ClassicalFourthNat.CPay_2036
  · exact WuPaper.ClassicalFourthNat.CPay_2037
  · exact WuPaper.ClassicalFourthNat.CPay_2038
  · exact WuPaper.ClassicalFourthNat.CPay_2039
  · exact WuPaper.ClassicalFourthNat.CPay_2040
  · exact WuPaper.ClassicalFourthNat.CPay_2041
  · exact WuPaper.ClassicalFourthNat.CPay_2042
  · exact WuPaper.ClassicalFourthNat.CPay_2043
  · exact WuPaper.ClassicalFourthNat.CPay_2044
  · exact WuPaper.ClassicalFourthNat.CPay_2045
  · exact WuPaper.ClassicalFourthNat.CPay_2046
  · exact WuPaper.ClassicalFourthNat.CPay_2047
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.CPay_block_031
