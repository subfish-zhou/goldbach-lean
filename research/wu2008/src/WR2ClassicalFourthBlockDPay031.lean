import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatDPay031
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem DPay_block_031 (j : Fin 64) (hj : 64*31+j.val < 2540) :
    DPay (64*31+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.DPay_1984
  · exact WuPaper.ClassicalFourthNat.DPay_1985
  · exact WuPaper.ClassicalFourthNat.DPay_1986
  · exact WuPaper.ClassicalFourthNat.DPay_1987
  · exact WuPaper.ClassicalFourthNat.DPay_1988
  · exact WuPaper.ClassicalFourthNat.DPay_1989
  · exact WuPaper.ClassicalFourthNat.DPay_1990
  · exact WuPaper.ClassicalFourthNat.DPay_1991
  · exact WuPaper.ClassicalFourthNat.DPay_1992
  · exact WuPaper.ClassicalFourthNat.DPay_1993
  · exact WuPaper.ClassicalFourthNat.DPay_1994
  · exact WuPaper.ClassicalFourthNat.DPay_1995
  · exact WuPaper.ClassicalFourthNat.DPay_1996
  · exact WuPaper.ClassicalFourthNat.DPay_1997
  · exact WuPaper.ClassicalFourthNat.DPay_1998
  · exact WuPaper.ClassicalFourthNat.DPay_1999
  · exact WuPaper.ClassicalFourthNat.DPay_2000
  · exact WuPaper.ClassicalFourthNat.DPay_2001
  · exact WuPaper.ClassicalFourthNat.DPay_2002
  · exact WuPaper.ClassicalFourthNat.DPay_2003
  · exact WuPaper.ClassicalFourthNat.DPay_2004
  · exact WuPaper.ClassicalFourthNat.DPay_2005
  · exact WuPaper.ClassicalFourthNat.DPay_2006
  · exact WuPaper.ClassicalFourthNat.DPay_2007
  · exact WuPaper.ClassicalFourthNat.DPay_2008
  · exact WuPaper.ClassicalFourthNat.DPay_2009
  · exact WuPaper.ClassicalFourthNat.DPay_2010
  · exact WuPaper.ClassicalFourthNat.DPay_2011
  · exact WuPaper.ClassicalFourthNat.DPay_2012
  · exact WuPaper.ClassicalFourthNat.DPay_2013
  · exact WuPaper.ClassicalFourthNat.DPay_2014
  · exact WuPaper.ClassicalFourthNat.DPay_2015
  · exact WuPaper.ClassicalFourthNat.DPay_2016
  · exact WuPaper.ClassicalFourthNat.DPay_2017
  · exact WuPaper.ClassicalFourthNat.DPay_2018
  · exact WuPaper.ClassicalFourthNat.DPay_2019
  · exact WuPaper.ClassicalFourthNat.DPay_2020
  · exact WuPaper.ClassicalFourthNat.DPay_2021
  · exact WuPaper.ClassicalFourthNat.DPay_2022
  · exact WuPaper.ClassicalFourthNat.DPay_2023
  · exact WuPaper.ClassicalFourthNat.DPay_2024
  · exact WuPaper.ClassicalFourthNat.DPay_2025
  · exact WuPaper.ClassicalFourthNat.DPay_2026
  · exact WuPaper.ClassicalFourthNat.DPay_2027
  · exact WuPaper.ClassicalFourthNat.DPay_2028
  · exact WuPaper.ClassicalFourthNat.DPay_2029
  · exact WuPaper.ClassicalFourthNat.DPay_2030
  · exact WuPaper.ClassicalFourthNat.DPay_2031
  · exact WuPaper.ClassicalFourthNat.DPay_2032
  · exact WuPaper.ClassicalFourthNat.DPay_2033
  · exact WuPaper.ClassicalFourthNat.DPay_2034
  · exact WuPaper.ClassicalFourthNat.DPay_2035
  · exact WuPaper.ClassicalFourthNat.DPay_2036
  · exact WuPaper.ClassicalFourthNat.DPay_2037
  · exact WuPaper.ClassicalFourthNat.DPay_2038
  · exact WuPaper.ClassicalFourthNat.DPay_2039
  · exact WuPaper.ClassicalFourthNat.DPay_2040
  · exact WuPaper.ClassicalFourthNat.DPay_2041
  · exact WuPaper.ClassicalFourthNat.DPay_2042
  · exact WuPaper.ClassicalFourthNat.DPay_2043
  · exact WuPaper.ClassicalFourthNat.DPay_2044
  · exact WuPaper.ClassicalFourthNat.DPay_2045
  · exact WuPaper.ClassicalFourthNat.DPay_2046
  · exact WuPaper.ClassicalFourthNat.DPay_2047
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.DPay_block_031
