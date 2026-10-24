import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay031
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_031 (j : Fin 64) (hj : 64*31+j.val < 10540) :
    BPay (64*31+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_1984
  · exact WuPaper.ClassicalFourthNat.BPay_1985
  · exact WuPaper.ClassicalFourthNat.BPay_1986
  · exact WuPaper.ClassicalFourthNat.BPay_1987
  · exact WuPaper.ClassicalFourthNat.BPay_1988
  · exact WuPaper.ClassicalFourthNat.BPay_1989
  · exact WuPaper.ClassicalFourthNat.BPay_1990
  · exact WuPaper.ClassicalFourthNat.BPay_1991
  · exact WuPaper.ClassicalFourthNat.BPay_1992
  · exact WuPaper.ClassicalFourthNat.BPay_1993
  · exact WuPaper.ClassicalFourthNat.BPay_1994
  · exact WuPaper.ClassicalFourthNat.BPay_1995
  · exact WuPaper.ClassicalFourthNat.BPay_1996
  · exact WuPaper.ClassicalFourthNat.BPay_1997
  · exact WuPaper.ClassicalFourthNat.BPay_1998
  · exact WuPaper.ClassicalFourthNat.BPay_1999
  · exact WuPaper.ClassicalFourthNat.BPay_2000
  · exact WuPaper.ClassicalFourthNat.BPay_2001
  · exact WuPaper.ClassicalFourthNat.BPay_2002
  · exact WuPaper.ClassicalFourthNat.BPay_2003
  · exact WuPaper.ClassicalFourthNat.BPay_2004
  · exact WuPaper.ClassicalFourthNat.BPay_2005
  · exact WuPaper.ClassicalFourthNat.BPay_2006
  · exact WuPaper.ClassicalFourthNat.BPay_2007
  · exact WuPaper.ClassicalFourthNat.BPay_2008
  · exact WuPaper.ClassicalFourthNat.BPay_2009
  · exact WuPaper.ClassicalFourthNat.BPay_2010
  · exact WuPaper.ClassicalFourthNat.BPay_2011
  · exact WuPaper.ClassicalFourthNat.BPay_2012
  · exact WuPaper.ClassicalFourthNat.BPay_2013
  · exact WuPaper.ClassicalFourthNat.BPay_2014
  · exact WuPaper.ClassicalFourthNat.BPay_2015
  · exact WuPaper.ClassicalFourthNat.BPay_2016
  · exact WuPaper.ClassicalFourthNat.BPay_2017
  · exact WuPaper.ClassicalFourthNat.BPay_2018
  · exact WuPaper.ClassicalFourthNat.BPay_2019
  · exact WuPaper.ClassicalFourthNat.BPay_2020
  · exact WuPaper.ClassicalFourthNat.BPay_2021
  · exact WuPaper.ClassicalFourthNat.BPay_2022
  · exact WuPaper.ClassicalFourthNat.BPay_2023
  · exact WuPaper.ClassicalFourthNat.BPay_2024
  · exact WuPaper.ClassicalFourthNat.BPay_2025
  · exact WuPaper.ClassicalFourthNat.BPay_2026
  · exact WuPaper.ClassicalFourthNat.BPay_2027
  · exact WuPaper.ClassicalFourthNat.BPay_2028
  · exact WuPaper.ClassicalFourthNat.BPay_2029
  · exact WuPaper.ClassicalFourthNat.BPay_2030
  · exact WuPaper.ClassicalFourthNat.BPay_2031
  · exact WuPaper.ClassicalFourthNat.BPay_2032
  · exact WuPaper.ClassicalFourthNat.BPay_2033
  · exact WuPaper.ClassicalFourthNat.BPay_2034
  · exact WuPaper.ClassicalFourthNat.BPay_2035
  · exact WuPaper.ClassicalFourthNat.BPay_2036
  · exact WuPaper.ClassicalFourthNat.BPay_2037
  · exact WuPaper.ClassicalFourthNat.BPay_2038
  · exact WuPaper.ClassicalFourthNat.BPay_2039
  · exact WuPaper.ClassicalFourthNat.BPay_2040
  · exact WuPaper.ClassicalFourthNat.BPay_2041
  · exact WuPaper.ClassicalFourthNat.BPay_2042
  · exact WuPaper.ClassicalFourthNat.BPay_2043
  · exact WuPaper.ClassicalFourthNat.BPay_2044
  · exact WuPaper.ClassicalFourthNat.BPay_2045
  · exact WuPaper.ClassicalFourthNat.BPay_2046
  · exact WuPaper.ClassicalFourthNat.BPay_2047
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_031
