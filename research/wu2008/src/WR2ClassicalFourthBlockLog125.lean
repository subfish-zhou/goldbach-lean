import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints125
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_125 (j : Fin 16) (hj : 16*125+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*125+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*125+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2000) ≤ val WuPaper.ClassicalFourthData.Bq 2000
    have hp : val WuPaper.ClassicalFourthData.Bq 2000 = (162186043243266:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2000 = 162186043243266 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2000 = (5:ℝ)/2 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2000
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2001) ≤ val WuPaper.ClassicalFourthData.Bq 2001
    have hp : val WuPaper.ClassicalFourthData.Bq 2001 = (162236480706924:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2001 = 162236480706924 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2001 = (10001:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2001
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2002) ≤ val WuPaper.ClassicalFourthData.Bq 2002
    have hp : val WuPaper.ClassicalFourthData.Bq 2002 = (162286896979918:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2002 = 162286896979918 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2002 = (5001:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2002
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2003) ≤ val WuPaper.ClassicalFourthData.Bq 2003
    have hp : val WuPaper.ClassicalFourthData.Bq 2003 = (162337292072305:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2003 = 162337292072305 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2003 = (10003:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2003
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2004) ≤ val WuPaper.ClassicalFourthData.Bq 2004
    have hp : val WuPaper.ClassicalFourthData.Bq 2004 = (162387665994133:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2004 = 162387665994133 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2004 = (2501:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2004
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2005) ≤ val WuPaper.ClassicalFourthData.Bq 2005
    have hp : val WuPaper.ClassicalFourthData.Bq 2005 = (162438018755445:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2005 = 162438018755445 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2005 = (2001:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2005
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2006) ≤ val WuPaper.ClassicalFourthData.Bq 2006
    have hp : val WuPaper.ClassicalFourthData.Bq 2006 = (162488350366280:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2006 = 162488350366280 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2006 = (5003:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2006
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2007) ≤ val WuPaper.ClassicalFourthData.Bq 2007
    have hp : val WuPaper.ClassicalFourthData.Bq 2007 = (162538660836668:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2007 = 162538660836668 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2007 = (10007:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2007
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2008) ≤ val WuPaper.ClassicalFourthData.Bq 2008
    have hp : val WuPaper.ClassicalFourthData.Bq 2008 = (162588950176636:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2008 = 162588950176636 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2008 = (1251:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2008
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2009) ≤ val WuPaper.ClassicalFourthData.Bq 2009
    have hp : val WuPaper.ClassicalFourthData.Bq 2009 = (162639218396204:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2009 = 162639218396204 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2009 = (10009:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2009
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2010) ≤ val WuPaper.ClassicalFourthData.Bq 2010
    have hp : val WuPaper.ClassicalFourthData.Bq 2010 = (162689465505385:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2010 = 162689465505385 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2010 = (1001:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2010
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2011) ≤ val WuPaper.ClassicalFourthData.Bq 2011
    have hp : val WuPaper.ClassicalFourthData.Bq 2011 = (162739691514189:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2011 = 162739691514189 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2011 = (10011:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2011
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2012) ≤ val WuPaper.ClassicalFourthData.Bq 2012
    have hp : val WuPaper.ClassicalFourthData.Bq 2012 = (162789896432616:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2012 = 162789896432616 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2012 = (2503:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2012
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2013) ≤ val WuPaper.ClassicalFourthData.Bq 2013
    have hp : val WuPaper.ClassicalFourthData.Bq 2013 = (162840080270665:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2013 = 162840080270665 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2013 = (10013:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2013
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2014) ≤ val WuPaper.ClassicalFourthData.Bq 2014
    have hp : val WuPaper.ClassicalFourthData.Bq 2014 = (162890243038326:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2014 = 162890243038326 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2014 = (5007:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2014
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2015) ≤ val WuPaper.ClassicalFourthData.Bq 2015
    have hp : val WuPaper.ClassicalFourthData.Bq 2015 = (162940384745583:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2015 = 162940384745583 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2015 = (2003:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2015
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_125
