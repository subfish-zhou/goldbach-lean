import MathlibNt.Wu2008DoubleSieve.FixedCoefficientLogMassEnclosure

namespace Wu2008DoubleSieve.FixedCoefficientJLowerEnclosure
open Real Set MeasureTheory ClassicalAnalyticLeaves SharpLogRecurrence SharpJBalance
open scoped Interval

 theorem tangent_lower {q : ℝ} (hq : 1 ≤ q) : 2*(q-1)/(1+q) ≤ log q := by
  have h := ClassicalLogBounds.log_tangent_lower (a := 1) (b := q) (by norm_num) hq
  simpa using h

noncomputable def seventhLower : ℝ :=
  2*log ((1/3)/s)+2*log ((1-s)/(2/3))-4*(3/2-1/(1-s))
noncomputable def eighthLower : ℝ :=
  (2/3)*log ((1/3)/a)+(2/3)*log ((1-a)/(2/3))-(4/3)*(3/2-1/(1-a))
noncomputable def ninthLower : ℝ :=
  2*(1-2*s)*(log (s/b)+log ((1-b)/(1-s)))-4*s*(1/(1-s)-1/(1-b))

 theorem seventh_lower : seventhLower ≤ SeventhEighth.J7 := by
  have hs0 : 0 < s := by norm_num [s,SeventhEighth.sigma,SeventhEighth.alpha]
  have hs : s ≤ (1/3 : ℝ) := SeventhEighth.classical_parameters.2.2.le
  have hi := packet_integrable (A := 2) (E := 0) (B := 2) (C := -4)
    (D := 0) (d := 1) (e := 1) hs0 hs (by norm_num) (by norm_num) (by norm_num)
  have hp (t : ℝ) (ht : t ∈ Icc s (1/3 : ℝ)) :
      packet 2 0 2 (-4) 0 1 1 t ≤ log ((1-2*t)/t)/(t*(1-t)) := by
    have ht0 := hs0.trans_le ht.1
    have ht1 : 0 < 1-t := by linarith [ht.2]
    have hq : 1 ≤ (1-2*t)/t := (le_div_iff₀ ht0).2 (by linarith [ht.2])
    have h := div_le_div_of_nonneg_right (tangent_lower hq) (mul_pos ht0 ht1).le
    refine le_trans (le_of_eq ?_) h
    dsimp [packet]
    have hn : 1*t ≠ 0 := by positivity
    field_simp [ht0.ne',ht1.ne',hn]
    ring_nf
    field_simp [ht1.ne']
    ring
  have hm := intervalIntegral.integral_mono_on hs hi SeventhEighth.J7_integrable hp
  rw [packet_integral hs0 hs (by norm_num) (by norm_num) (by norm_num)] at hm
  change _ ≤ SeventhEighth.J7 at hm
  norm_num [seventhLower] at hm ⊢
  linarith

 theorem eighth_lower : eighthLower ≤ SeventhEighth.J8 := by
  have ha : 0 < a := SeventhEighth.classical_parameters.1
  have hab : a ≤ (1/3 : ℝ) := SeventhEighth.classical_parameters.2.1.le.trans
    SeventhEighth.classical_parameters.2.2.le
  have hi := packet_integrable (A := 2/3) (E := 0) (B := 2/3) (C := -4/3)
    (D := 0) (d := 1) (e := 1) ha hab (by norm_num) (by norm_num) (by norm_num)
  have hp (t : ℝ) (ht : t ∈ Icc a (1/3 : ℝ)) :
      packet (2/3) 0 (2/3) (-4/3) 0 1 1 t ≤ log (2-3*t)/(t*(1-t)) := by
    have ht0 := ha.trans_le ht.1
    have ht1 : 0 < 1-t := by linarith [ht.2]
    have h := div_le_div_of_nonneg_right
      (tangent_lower (q := 2-3*t) (by linarith [ht.2])) (mul_pos ht0 ht1).le
    refine le_trans (le_of_eq ?_) h
    dsimp [packet]
    have ht3 : 3-3*t ≠ 0 := by linarith
    field_simp [ht0.ne',ht1.ne',ht3]
    ring_nf
    have ht4 : 3-t*3 ≠ 0 := by linarith
    field_simp [ht4]
    ring
  have hm := intervalIntegral.integral_mono_on hab hi SeventhEighth.J8_integrable hp
  rw [packet_integral ha hab (by norm_num) (by norm_num) (by norm_num)] at hm
  change _ ≤ SeventhEighth.J8 at hm
  norm_num [eighthLower] at hm ⊢
  linarith

 theorem ninth_lower : ninthLower ≤ J9 := by
  have hb : 0 < b := by norm_num [b,ninthProfileK2]
  have hbs : b ≤ s := by norm_num [b,s,SeventhEighth.sigma,SeventhEighth.alpha,ninthProfileK2]
  have hs1 : s < 1 := by norm_num [s,SeventhEighth.sigma,SeventhEighth.alpha]
  have hs0 : 0 < s := hb.trans_le hbs
  have hs3 : s < 1/3 := by norm_num [s,SeventhEighth.sigma,SeventhEighth.alpha]
  have hi := packet_integrable (A := 2*(1-2*s)) (E := 0) (B := 2*(1-2*s)) (C := -4*s)
    (D := 0) (d := 1) (e := 1) hb hbs hs1 (by norm_num) (by linarith)
  have hp (t : ℝ) (ht : t ∈ Icc b s) :
      packet (2*(1-2*s)) 0 (2*(1-2*s)) (-4*s) 0 1 1 t ≤
      log ((1-s-t)/s)/(t*(1-t)) := by
    have ht0 := hb.trans_le ht.1
    have ht1 : 0 < 1-t := by linarith [ht.2]
    have hq : 1 ≤ (1-s-t)/s := (le_div_iff₀ hs0).2 (by linarith [ht.2])
    have h := div_le_div_of_nonneg_right (tangent_lower hq) (mul_pos ht0 ht1).le
    refine le_trans (le_of_eq ?_) h
    dsimp [packet]
    field_simp [ht0.ne',ht1.ne',hs0.ne']
    ring_nf
    field_simp [ht1.ne']
    ring
  have hm := intervalIntegral.integral_mono_on hbs hi J9_integrable hp
  rw [packet_integral hb hbs hs1 (by norm_num) (by linarith)] at hm
  change _ ≤ J9 at hm
  norm_num [ninthLower] at hm ⊢
  linarith

noncomputable def seventhRational : ℝ :=
  2*lowerLog ((1/3)/s)+2*lowerLog ((1-s)/(2/3))-4*(3/2-1/(1-s))
noncomputable def eighthRational : ℝ :=
  (2/3)*lowerLog ((1/3)/a)+(2/3)*lowerLog ((1-a)/(2/3))-(4/3)*(3/2-1/(1-a))
noncomputable def ninthRational : ℝ :=
  2*(1-2*s)*(lowerLog (s/b)+lowerLog ((1-b)/(1-s)))-4*s*(1/(1-s)-1/(1-b))

 theorem rational_J_lower : seventhRational ≤ SeventhEighth.J7 ∧
    eighthRational ≤ SeventhEighth.J8 ∧ ninthRational ≤ J9 := by
  have h71 := log_lower (t := (1/3)/s) (by norm_num [s,SeventhEighth.sigma,SeventhEighth.alpha])
  have h72 := log_lower (t := (1-s)/(2/3)) (by norm_num [s,SeventhEighth.sigma,SeventhEighth.alpha])
  have h81 := log_lower (t := (1/3)/a) (by norm_num [a,SeventhEighth.alpha])
  have h82 := log_lower (t := (1-a)/(2/3)) (by norm_num [a,SeventhEighth.alpha])
  have h91 := log_lower (t := s/b) (by norm_num [s,b,SeventhEighth.sigma,SeventhEighth.alpha,ninthProfileK2])
  have h92 := log_lower (t := (1-b)/(1-s)) (by norm_num [s,b,SeventhEighth.sigma,SeventhEighth.alpha,ninthProfileK2])
  have h7 := seventh_lower
  have h8 := eighth_lower
  have h9 := ninth_lower
  unfold seventhRational eighthRational ninthRational seventhLower eighthLower ninthLower at *
  norm_num [s,SeventhEighth.sigma,SeventhEighth.alpha] at *
  constructor
  · linarith
  constructor <;> linarith

noncomputable def weightedRational : ℝ := 16*seventhRational+8*eighthRational+8*ninthRational

 theorem weighted_J_lower : weightedRational ≤ 16*SeventhEighth.J7+8*SeventhEighth.J8+8*J9 := by
  obtain ⟨h7,h8,h9⟩ := rational_J_lower
  unfold weightedRational
  linarith

 theorem weightedRational_gt_ten : (10 : ℝ) < weightedRational := by
  norm_num [weightedRational,seventhRational,eighthRational,ninthRational,lowerLog,
    a,b,s,SeventhEighth.alpha,SeventhEighth.sigma,ninthProfileK2]

noncomputable def rationalUpper : ℝ := FixedCoefficientLogMassEnclosure.rationalUpper-weightedRational

 theorem complete_rational_upper : TruncatedElevenClassicalCountLower.classicalCoefficient ≤ rationalUpper := by
  have hb := FixedCoefficientUpperEnclosure.base_upper
  have hf := FixedCoefficientLogMassEnclosure.fifth_log_upper
  have hs := FixedCoefficientLogMassEnclosure.sixth_log_upper
  have hp := FixedCoefficientLogMassEnclosure.positive_rational_upper
  have hg := FixedCoefficientUpperEnclosure.rationalG_lower.trans FixedCoefficientUpperEnclosure.G_pair_lower
  have hj := weighted_J_lower
  have h4 := FourRoughClosedMass.integrals_nonneg
  unfold TruncatedElevenClassicalCountLower.classicalCoefficient rationalUpper
    FixedCoefficientLogMassEnclosure.rationalUpper
  linarith

 theorem actual_interval : (3/2 : ℝ) < TruncatedElevenClassicalCountLower.classicalCoefficient ∧
    TruncatedElevenClassicalCountLower.classicalCoefficient < 18 := by
  refine ⟨RationalMovingSixth.complete_coefficient_gt_three_halves, ?_⟩
  have h1 := FixedCoefficientLogMassEnclosure.rationalUpper_lt_twenty_eight
  have h2 := weightedRational_gt_ten
  have h3 := complete_rational_upper
  unfold rationalUpper at h3
  linarith

end Wu2008DoubleSieve.FixedCoefficientJLowerEnclosure
