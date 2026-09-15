import F1TwoFactorPayment

noncomputable section
open Real Set MeasureTheory FirstCRationalPayment
open F1SecondLogRecovery
namespace F1BFullFTC

def oneA : ℝ := -16459422965661628/284979509086993
def oneB : ℝ := -306095516491903604/72714107151529343703
def oneC : ℝ := 18556760661804644067712/342247739960944596627
def oneD : ℝ := 817893232439494624/22899381224922225
def oneE : ℝ := 67036981856656/1532169826875
def oneF : ℝ := 825734715243200/11120854285557
def oneG : ℝ := 6815475735941488/11120854285557

def kernelOne (u : ℝ) : ℝ := 8*weight u/denomOne u
def quadOne (u : ℝ) : ℝ := (1127/200)^2+18*(1127/200)*(u+1)+21*(u+1)^2
def partialOne (u : ℝ) : ℝ :=
  oneA/(u+2)+oneB/(u-2/3)+oneC/(u+1727/600)+oneD/(u+1727/600)^2+
  oneE/(u+1727/600)^3+(oneF*u+oneG)/quadOne u

theorem partial_one {u : ℝ} (hu : 2 ≤ u) : kernelOne u = partialOne u := by
  have hu0 : 0 < u := by linarith
  have h1 : u+2 ≠ 0 := by linarith
  have h2 : u-2/3 ≠ 0 := by linarith
  have h3 : u+1727/600 ≠ 0 := by linarith
  have hq : quadOne u ≠ 0 := by unfold quadOne; positivity
  have he : denomOne u = 81*(u+2)*(u-2/3)*(u+1727/600)^3*quadOne u := by
    unfold denomOne errorDenomOne quadOne
    ring
  unfold kernelOne
  rw [he]
  unfold partialOne
  have ht : -2+u*3 ≠ 0 := by linarith
  field_simp [h1,h2,h3,hq,ht]
  unfold weight quadOne oneA oneB oneC oneD oneE oneF oneG
  ring_nf
  field_simp [ht]
  ring

def twoA : ℝ := 16459422965661628/729230510956734169
def twoB : ℝ := -306095516491903604/1253165902073508551601
def twoC : ℝ := 863503496961960057074816/133603751684856429841161
def twoD : ℝ := -1722352366386746528/18846159324745335
def twoE : ℝ := 30392236051856/22153676875
def twoF : ℝ := -187801765905252800/20519935994870787
def twoG : ℝ := -5123979923436922912/20519935994870787

def kernelTwo (u : ℝ) : ℝ := 8*weight u/denomTwo u
def quadTwo (u : ℝ) : ℝ := 21*(1127/200)^2+18*(1127/200)*(u+1)+(u+1)^2
def partialTwo (u : ℝ) : ℝ :=
  twoA/(u+2)+twoB/(u-2/3)+twoC/(u+3581/200)+twoD/(u+3581/200)^2+
  twoE/(u+3581/200)^3+(twoF*u+twoG)/quadTwo u

theorem partial_two {u : ℝ} (hu : 2 ≤ u) : kernelTwo u = partialTwo u := by
  have hu0 : 0 < u := by linarith
  have h1 : u+2 ≠ 0 := by linarith
  have h2 : u-2/3 ≠ 0 := by linarith
  have h3 : u+3581/200 ≠ 0 := by linarith
  have hq : quadTwo u ≠ 0 := by unfold quadTwo; positivity
  have he : denomTwo u = 3*(u+2)*(u-2/3)*(u+3581/200)^3*quadTwo u := by
    unfold denomTwo errorDenomTwo quadTwo
    ring
  unfold kernelTwo
  rw [he]
  unfold partialTwo
  have ht : -2+u*3 ≠ 0 := by linarith
  field_simp [h1,h2,h3,hq,ht]
  unfold weight quadTwo twoA twoB twoC twoD twoE twoF twoG
  ring_nf
  field_simp [ht]
  ring

end F1BFullFTC
