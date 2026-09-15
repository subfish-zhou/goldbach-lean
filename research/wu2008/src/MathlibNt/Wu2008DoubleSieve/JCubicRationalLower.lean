import MathlibNt.Wu2008DoubleSieve.JCubicActualMass

namespace Wu2008DoubleSieve.JCubicRationalLower
open Real Set MeasureTheory SharpLogRecurrence SharpJBalance JCubicPrimitive JCubicActualMass

noncomputable def pairedLowerLog (l r : ℝ) : ℝ :=
  lowerLog (r/l)+lowerLog ((1-l)/(1-r))

 theorem paired_log_lower {l r : ℝ} (hl : 0 < l) (hlr : l ≤ r) (hr : r < 1) :
    pairedLowerLog l r ≤ log (crossRatio l r) := by
  have hr0 := hl.trans_le hlr
  have hl1 : 0 < 1-l := by linarith
  have hr1 : 0 < 1-r := by linarith
  have h1 := log_lower (t := r/l) ((le_div_iff₀ hl).2 (by linarith))
  have h2 := log_lower (t := (1-l)/(1-r)) ((le_div_iff₀ hr1).2 (by linarith))
  dsimp [pairedLowerLog,crossRatio]
  rw [log_div hr0.ne' hl.ne'] at h1
  rw [log_div hl1.ne' hr1.ne'] at h2
  rw [log_div (mul_ne_zero hr0.ne' hl1.ne') (mul_ne_zero hl.ne' hr1.ne'),
    log_mul hr0.ne' hl1.ne',log_mul hl.ne' hr1.ne']
  linarith

noncomputable def paidMass (v w l r p : ℝ) : ℝ :=
  (2*v+(2/3)*v^3)*p+2*(v-w)*(1/(1-r)-1/(1-l))+
  (2/3)*(rationalPart v w r-rationalPart v w l)

 theorem payment_lower (v w l r p : ℝ) (hv : 0 ≤ v)
    (hp : p ≤ log (crossRatio l r)) : paidMass v w l r p ≤ fullMass v w l r := by
  have hc : 0 ≤ 2*v+(2/3)*v^3 := by positivity
  have hm := mul_le_mul_of_nonneg_left hp hc
  dsimp [paidMass,fullMass]
  linarith

noncomputable def seventhRational : ℝ := paidMass 1 3 s (1/3) (pairedLowerLog s (1/3))
noncomputable def eighthRational : ℝ := paidMass (1/3) 1 a (1/3) (splitLowerLog (crossRatio a (1/3)))
noncomputable def ninthRational : ℝ := paidMass (1-2*s) 1 b s (pairedLowerLog b s)
noncomputable def weightedRational : ℝ := 16*seventhRational+8*eighthRational+8*ninthRational

 theorem eighth_cross_ratio : crossRatio a (1/3) = (1227/200 : ℝ) := by
  norm_num [crossRatio,a,SeventhEighth.alpha]

 theorem seventh_rational_lower : seventhRational ≤ SeventhEighth.J7 := by
  apply le_trans (payment_lower 1 3 s (1/3) _ (by norm_num) _) seventh_mass_lower
  exact paired_log_lower (by norm_num [s,SeventhEighth.sigma,SeventhEighth.alpha])
    SeventhEighth.classical_parameters.2.2.le (by norm_num)

 theorem eighth_rational_lower : eighthRational ≤ SeventhEighth.J8 := by
  apply le_trans (payment_lower (1/3) 1 a (1/3) _ (by norm_num) _) eighth_mass_lower
  apply split_log_lower
  rw [eighth_cross_ratio]
  norm_num

 theorem ninth_rational_lower : ninthRational ≤ J9 := by
  apply le_trans (payment_lower (1-2*s) 1 b s _
    (by norm_num [s,SeventhEighth.sigma,SeventhEighth.alpha]) _) ninth_mass_lower
  exact paired_log_lower (by norm_num [b,ninthProfileK2])
    (by norm_num [b,s,ninthProfileK2,SeventhEighth.sigma,SeventhEighth.alpha])
    (by norm_num [s,SeventhEighth.sigma,SeventhEighth.alpha])

 theorem weighted_J_lower : weightedRational ≤ 16*SeventhEighth.J7+8*SeventhEighth.J8+8*J9 := by
  have h7 := seventh_rational_lower
  have h8 := eighth_rational_lower
  have h9 := ninth_rational_lower
  unfold weightedRational
  linarith

 theorem each_rational_improves :
    FixedCoefficientJLowerEnclosure.seventhRational < seventhRational ∧
    FixedCoefficientJLowerEnclosure.eighthRational < eighthRational ∧
    FixedCoefficientJLowerEnclosure.ninthRational < ninthRational := by
  norm_num [FixedCoefficientJLowerEnclosure.seventhRational,
    FixedCoefficientJLowerEnclosure.eighthRational,FixedCoefficientJLowerEnclosure.ninthRational,
    seventhRational,eighthRational,ninthRational,paidMass,pairedLowerLog,splitLowerLog,
    rationalPart,crossRatio,lowerLog,a,b,s,SeventhEighth.alpha,SeventhEighth.sigma,ninthProfileK2]

 theorem weighted_improves : FixedCoefficientJLowerEnclosure.weightedRational < weightedRational := by
  obtain ⟨h7,h8,h9⟩ := each_rational_improves
  unfold FixedCoefficientJLowerEnclosure.weightedRational weightedRational
  linarith

 theorem seventh_exact : seventhRational =
    (725739378149940827219717538426619/9925542175122775804871168220601125 : ℝ) := by
  norm_num [seventhRational,paidMass,pairedLowerLog,rationalPart,lowerLog,
    s,SeventhEighth.alpha,SeventhEighth.sigma]

 theorem eighth_exact : eighthRational =
    (821724102120589147993/1246177636092655462809 : ℝ) := by
  norm_num [eighthRational,paidMass,splitLowerLog,rationalPart,crossRatio,lowerLog,
    a,SeventhEighth.alpha]

 theorem ninth_exact : ninthRational =
    (429323557093743493977357283834711825262698638985454565/
      644507866150676811075035973868203117572320621883188282 : ℝ) := by
  norm_num [ninthRational,paidMass,pairedLowerLog,rationalPart,lowerLog,
    b,s,ninthProfileK2,SeventhEighth.alpha,SeventhEighth.sigma]

 theorem weighted_exact : weightedRational =
    (331696782322904632969434394527525492101775347743287055251674000246250067857073857573943451178164/
      28171807260621087511825144682826018980793781836663301368341028518781758875993220675336803564875 : ℝ) := by
  unfold weightedRational
  rw [seventh_exact,eighth_exact,ninth_exact]
  norm_num

end Wu2008DoubleSieve.JCubicRationalLower
