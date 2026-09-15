import TailRationalBasis

noncomputable section
open Real Set MeasureTheory TailRationalBasis
open scoped Interval
namespace TailFiniteFTC.BA21

def c0_1 : ℝ := 300522532658460461593964640000/8335779892742847993794640750349201
def c0_2 : ℝ := 0
def c0_3 : ℝ := 0
def c0_4 : ℝ := 0
def c1_1 : ℝ := 879974992043687319929136686544953106726400/5796491867717996608947409104307032449168463233967
def c1_2 : ℝ := -499407730728461904340998400/127998836125955790694650872133245487
def c1_3 : ℝ := 0
def c1_4 : ℝ := 0
def c3_1 : ℝ := -248703212790330649525589708415323764574637972355008097350218847990890448486400/433093781764633148845037144103546956048119750883382009446437488706197326206442867469
def c3_2 : ℝ := -350622234897365434570940677553988075250432349861200413792665600/31387054928387131611322376240478102099282774350838617850327920127627321
def c3_3 : ℝ := 24160877123398943127531227622469743011435364352000/2274674120380176256143058679601285937476241121929967316789
def c3_4 : ℝ := 169236915976878971630035638845440000/164849565074922728161655684203183613195499201
def c4_1 : ℝ := -248414904742489932880200333471376082777397243825027882223372170502353460143195318113/5465207879384400675174793092291322876600407953314227433147301930390625087962832675
def c4_2 : ℝ := -45967585173024046200644289657639931083301131917144734417597936533731/943304755691774759922696294439246923605877801576546460360917045000
def c4_3 : ℝ := -858605275195240653314171608190221364594068702895365273/17950475620107071880410430353535258808818813750750000
def c4_4 : ℝ := -17580369854672542911400850540582790029417/455447825733699934587408028123350000000
def c5_1 : ℝ := -21520565175963692625765651361869942916446633068424092360433303961887741994312554271936/10429687331721010198566554752763092479158159513780269824754236839845383764553560154225
def c5_2 : ℝ := 6914707280320743870361115293763130536811304645997197165013297119522808/3086676743203080410379859377613000710390012781348325610874535702776875
def c5_3 : ℝ := -76707557395533736627662707319610795148510089919936600156/44761753414660854562660428442966261078182292957745765625
def c5_4 : ℝ := 446659036109286758602476120548630032378217/649117071674868194012494207571083744921875
def g1 : ℝ := 4176111040779859623297070837564390377441442339508216512000000/16509084984212138817583568829651706451761227734870783565425274747
def f1 : ℝ := -1512498974107575789582464305151353587542549161465608160000000/5503028328070712939194522943217235483920409244956927855141758249
def g2 : ℝ := 42939596714153099443575123289253071917726762591804825886584094226/32198098399981033635916732379841638443812287166685282539338043
def f2 : ℝ := 10709763267115773885477386424494241301182870066726427255803439100/10732699466660344545305577459947212814604095722228427513112681

def kernel (u : ℝ) : ℝ := ((286277370692787362439/490000000000000000)+(-4659884708106380838849/765625000000000000)*u+(91497709118065131354861/3500000000000000000)*u^2+(-1409024895902675366407109/24500000000000000000)*u^3+(12905839312824050916302921/220500000000000000000)*u^4+(1890191563989110438505883/162000000000000000000)*u^5+(-624204536118133321441584421/5832000000000000000000)*u^6+(323271948309528050303594993509/2571912000000000000000000)*u^7+(-9442109817783674183465021998991/185177664000000000000000000)*u^8+(-407198031266567859496705294301/13226976000000000000000000)*u^9+(10309334707162243028485536957737/185177664000000000000000000)*u^10+(-4424717964199205324449017631/115736040000000000000000)*u^11+(2672768332279726145978153/165337200000000000000)*u^12+(-1910621178523399717939/413343000000000000)*u^13+(3529277224023767413/3857868000000000)*u^14+(-8970536318655337/72335025000000)*u^15+(126540866737/11481750000)*u^16+(-1048116829/1808375625)*u^17+(990377/72335025)*u^18)/((u-(0))^1*(u-(1))^2*(u-(2/3))^4*(u-(-1327/200))^4*(u-(-1727/600))^4*((21*u^2-24*u+4))*(F1BFullFTC.quadOne u))
def partialValue (u : ℝ) : ℝ := (FirstCRationalPayment.poleKernel (0) c0_1 c0_2 c0_3 u+c0_4/(u-(0))^4)+(FirstCRationalPayment.poleKernel (1) c1_1 c1_2 c1_3 u+c1_4/(u-(1))^4)+(FirstCRationalPayment.poleKernel (2/3) c3_1 c3_2 c3_3 u+c3_4/(u-(2/3))^4)+(FirstCRationalPayment.poleKernel (-1327/200) c4_1 c4_2 c4_3 u+c4_4/(u-(-1327/200))^4)+(FirstCRationalPayment.poleKernel (-1727/600) c5_1 c5_2 c5_3 u+c5_4/(u-(-1727/600))^4)+(f1*u+g1)/((21*u^2-24*u+4))+(f2*u+g2)/(F1BFullFTC.quadOne u)
def primitive (u : ℝ) : ℝ := F1FreshFTC.pole4 (0) c0_1 c0_2 c0_3 c0_4 u+F1FreshFTC.pole4 (1) c1_1 c1_2 c1_3 c1_4 u+F1FreshFTC.pole4 (2/3) c3_1 c3_2 c3_3 c3_4 u+F1FreshFTC.pole4 (-1327/200) c4_1 c4_2 c4_3 c4_4 u+F1FreshFTC.pole4 (-1727/600) c5_1 c5_2 c5_3 c5_4 u+F1ActualSecondFTC.affinePrimitive f1 g1 u+F1BFullFTC.quadPrimitiveOne f2 g2 u

theorem source_exact {u : ℝ} (hu : 2 ≤ u) :
    ActualTailVariation.floor (((1127/200)+u+1)/(2*(u+1)))*F1JointFTC.low (2*(u-1)/u)/u=kernel u := by
  have hu0 : 0 < u := by linarith
  have hum : 0 < u-1 := by linarith
  have ht : 0 < 3*u-2 := by linarith
  have ht' : 0 < u-2/3 := by linarith
  have hq : 0 < 21*u^2-24*u+4 := by nlinarith [sq_nonneg (u-2)]
  have hfour : 0 < 16-u*96+u^2*216-u^3*216+u^4*81 := by
    have he : 16-u*96+u^2*216-u^3*216+u^4*81=(3*u-2)^4 := by ring
    rw [he]
    exact pow_pos ht 4
  have hsix : 0 < 64-u*768+u^2*3504-u^3*8064+u^4*10044-u^5*6480+u^6*1701 := by
    have he : 64-u*768+u^2*3504-u^3*8064+u^4*10044-u^5*6480+u^6*1701=
        (3*u-2)^4*(21*u^2-24*u+4) := by ring
    rw [he]
    exact mul_pos (pow_pos ht 4) hq
  rw [low_rational (show 0 < (2*(u-1)/u) by positivity)]
  unfold ActualTailVariation.floor ActualTailVariation.denominator lowNumerator kernel
    F1BFullFTC.quadOne
  simp only [neg_div, sub_neg_eq_add, sub_zero]
  field_simp (disch := first | positivity | nlinarith only [hq,hfour,hsix])
  ring

theorem partial_exact {u : ℝ} (hu : 2 ≤ u) : kernel u=partialValue u := by
  have hu0 : 0 < u := by linarith
  have hum : 0 < u-1 := by linarith
  have ht : 0 < 3*u-2 := by linarith
  have ht' : 0 < u-2/3 := by linarith
  have hq : 0 < 21*u^2-24*u+4 := by nlinarith [sq_nonneg (u-2)]
  have hfour : 0 < 16-u*96+u^2*216-u^3*216+u^4*81 := by
    have he : 16-u*96+u^2*216-u^3*216+u^4*81=(3*u-2)^4 := by ring
    rw [he]
    exact pow_pos ht 4
  have hsix : 0 < 64-u*768+u^2*3504-u^3*8064+u^4*10044-u^5*6480+u^6*1701 := by
    have he : 64-u*768+u^2*3504-u^3*8064+u^4*10044-u^5*6480+u^6*1701=
        (3*u-2)^4*(21*u^2-24*u+4) := by ring
    rw [he]
    exact mul_pos (pow_pos ht 4) hq
  unfold kernel partialValue FirstCRationalPayment.poleKernel
    F1BFullFTC.quadOne
  simp only [neg_div, sub_neg_eq_add, sub_zero]
  field_simp (disch := first | positivity | nlinarith only [hq,hfour,hsix])
  unfold c0_1 c0_2 c0_3 c0_4 c1_1 c1_2 c1_3 c1_4 c3_1 c3_2 c3_3 c3_4 c4_1 c4_2 c4_3 c4_4 c5_1 c5_2 c5_3 c5_4 g1 f1 g2 f2
  ring

theorem primitive_deriv {u : ℝ} (hu : 2 ≤ u) : HasDerivAt primitive (kernel u) u := by
  have h0 := F1FreshFTC.pole4_deriv (0) c0_1 c0_2 c0_3 c0_4 u (by linarith)
  have h1 := F1FreshFTC.pole4_deriv (1) c1_1 c1_2 c1_3 c1_4 u (by linarith)
  have h2 := F1FreshFTC.pole4_deriv (2/3) c3_1 c3_2 c3_3 c3_4 u (by linarith)
  have h3 := F1FreshFTC.pole4_deriv (-1327/200) c4_1 c4_2 c4_3 c4_4 u (by linarith)
  have h4 := F1FreshFTC.pole4_deriv (-1727/600) c5_1 c5_2 c5_3 c5_4 u (by linarith)
  have h5 := F1ActualSecondFTC.affinePrimitive_deriv f1 g1 hu
  have h6 := F1BFullFTC.quadPrimitiveOne_deriv f2 g2 hu
  rw [partial_exact hu]
  exact ((((((h0.add h1).add h2).add h3).add h4).add h5).add h6)

theorem kernel_continuousOn : ContinuousOn kernel (Icc 2 (927/200)) := by
  intro u hu
  have hu := hu.1
  have hu0 : 0 < u := by linarith
  have hum : 0 < u-1 := by linarith
  have ht : 0 < 3*u-2 := by linarith
  have ht' : 0 < u-2/3 := by linarith
  have hq : 0 < 21*u^2-24*u+4 := by nlinarith [sq_nonneg (u-2)]
  have hfour : 0 < 16-u*96+u^2*216-u^3*216+u^4*81 := by
    have he : 16-u*96+u^2*216-u^3*216+u^4*81=(3*u-2)^4 := by ring
    rw [he]
    exact pow_pos ht 4
  have hsix : 0 < 64-u*768+u^2*3504-u^3*8064+u^4*10044-u^5*6480+u^6*1701 := by
    have he : 64-u*768+u^2*3504-u^3*8064+u^4*10044-u^5*6480+u^6*1701=
        (3*u-2)^4*(21*u^2-24*u+4) := by ring
    rw [he]
    exact mul_pos (pow_pos ht 4) hq
  apply ContinuousAt.continuousWithinAt
  unfold kernel F1BFullFTC.quadOne
  simp only [neg_div, sub_neg_eq_add, sub_zero]
  fun_prop (disch := positivity)

def mass : ℝ := primitive (927/200)-primitive 2

theorem integral_exact : (∫ u in (2:ℝ)..(927/200),kernel u)=mass := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro u hu
    apply primitive_deriv
    rw [uIcc_of_le (by norm_num : (2:ℝ)≤927/200)] at hu
    exact hu.1
  · exact kernel_continuousOn.intervalIntegrable_of_Icc (by norm_num)
end TailFiniteFTC.BA21
