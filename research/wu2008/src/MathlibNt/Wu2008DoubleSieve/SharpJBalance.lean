import MathlibNt.Wu2008DoubleSieve.SharpSingleBalance

namespace Wu2008DoubleSieve.SharpJBalance
open Real Set MeasureTheory SharpLogRecurrence
open scoped Interval

noncomputable def packet (A E B C D d e t : ℝ) : ℝ :=
  A/t+E/t^2+B/(1-t)+C/(1-t)^2+D/(d-e*t)

 theorem packet_integrable {A E B C D d e l r : ℝ} (hl : 0 < l) (hlr : l ≤ r)
    (hr : r < 1) (he : 0 ≤ e) (hd : 0 < d-e*r) :
    IntervalIntegrable (packet A E B C D d e) volume l r := by
  have hn (t : ℝ) (ht : t ∈ uIcc l r) : t ≠ 0 ∧ 1-t ≠ 0 ∧ d-e*t ≠ 0 := by
    rw [uIcc_of_le hlr] at ht
    have hm := mul_le_mul_of_nonneg_left ht.2 he
    exact ⟨(hl.trans_le ht.1).ne', by linarith [ht.2], by linarith⟩
  apply ContinuousOn.intervalIntegrable
  unfold packet
  exact ((((continuousOn_const.div continuousOn_id (fun t ht => (hn t ht).1)).add
    (continuousOn_const.div (continuousOn_id.pow 2) (fun t ht => pow_ne_zero _ (hn t ht).1))).add
    (continuousOn_const.div (continuousOn_const.sub continuousOn_id) (fun t ht => (hn t ht).2.1))).add
    (continuousOn_const.div ((continuousOn_const.sub continuousOn_id).pow 2)
      (fun t ht => pow_ne_zero _ (hn t ht).2.1))).add
    (continuousOn_const.div (continuousOn_const.sub (continuousOn_const.mul continuousOn_id))
      (fun t ht => (hn t ht).2.2))

theorem packet_integral {A E B C D d e l r : ℝ} (hl : 0 < l) (hlr : l ≤ r)
    (hr : r < 1) (he : 0 < e) (hd : 0 < d-e*r) :
    (∫ t in l..r, packet A E B C D d e t) =
      A*log (r/l)+E*(1/l-1/r)+B*log ((1-l)/(1-r))+
      C*(1/(1-r)-1/(1-l))+(D/e)*log ((d-e*l)/(d-e*r)) := by
  have hd0 (t : ℝ) (ht : t ∈ uIcc l r) : t ≠ 0 ∧ 1-t ≠ 0 ∧ d-e*t ≠ 0 := by
    rw [uIcc_of_le hlr] at ht
    have hm := mul_le_mul_of_nonneg_left ht.2 he.le
    exact ⟨(hl.trans_le ht.1).ne', by linarith [ht.2], by linarith⟩
  have hder (t : ℝ) (ht : t ∈ uIcc l r) :
      HasDerivAt (fun t => A*log t-E/t-B*log (1-t)+C/(1-t)-(D/e)*log (d-e*t))
        (packet A E B C D d e t) t := by
    obtain ⟨ht0,ht1,htd⟩ := hd0 t ht
    have h := (((((hasDerivAt_log ht0).const_mul A).sub
      ((hasDerivAt_const t E).div (hasDerivAt_id t) ht0)).sub
      ((((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).log ht1).const_mul B)).add
      ((hasDerivAt_const t C).div ((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)) ht1)).sub
      ((((hasDerivAt_const t d).sub ((hasDerivAt_id t).const_mul e)).log htd).const_mul (D/e))
    convert h using 1 <;> first | rfl | (dsimp [packet]; field_simp [ht0,ht1,htd,he.ne']; ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hder (packet_integrable hl hlr hr he.le hd)]
  have hl1 : 1-l ≠ 0 := by linarith
  have hr1 : 1-r ≠ 0 := by linarith
  have hld : d-e*l ≠ 0 := by
    have hm := mul_le_mul_of_nonneg_left hlr he.le; linarith
  rw [log_div (hl.trans_le hlr).ne' hl.ne',log_div hl1 hr1,log_div hld hd.ne']
  ring

noncomputable abbrev a : ℝ := SeventhEighth.alpha
noncomputable abbrev s : ℝ := SeventhEighth.sigma
noncomputable abbrev b : ℝ := ninthProfileK2

 theorem J7_primitive_upper : SeventhEighth.J7 ≤
    (7/6)*log ((1/3)/s)+(1/6)*(1/s-3)+(4/3)*log ((1-s)/(2/3))-
      (8/3)*(3/2-1/(1-s))-(1/6)*log ((1-2*s)/(1/3)) := by
  have hs0 : 0 < s := by norm_num [s,SeventhEighth.sigma,SeventhEighth.alpha]
  have hs : s ≤ (1/3 : ℝ) := SeventhEighth.classical_parameters.2.2.le
  have hi := packet_integrable (A := 7/6) (E := 1/6) (B := 4/3) (C := -8/3)
    (D := -1/3) (d := 1) (e := 2) hs0 hs (by norm_num) (by norm_num) (by norm_num)
  have hp (t : ℝ) (ht : t ∈ Icc s (1/3 : ℝ)) :
      log ((1-2*t)/t)/(t*(1-t)) ≤ packet (7/6) (1/6) (4/3) (-8/3) (-1/3) 1 2 t := by
    have ht0 := hs0.trans_le ht.1
    have ht1 : 0 < 1-t := by linarith [ht.2]
    have ht2 : 0 < 1-2*t := by linarith [ht.2]
    have h := div_le_div_of_nonneg_right
      (log_upper (t := (1-2*t)/t) ((le_div_iff₀ ht0).2 (by linarith [ht.2])))
      (mul_pos ht0 ht1).le
    refine h.trans_eq ?_
    dsimp [packet,upperLog]
    field_simp
    ring
  have h := intervalIntegral.integral_mono_on hs SeventhEighth.J7_integrable hi hp
  rw [packet_integral hs0 hs (by norm_num) (by norm_num) (by norm_num)] at h
  change SeventhEighth.J7 ≤ _ at h
  norm_num at h ⊢
  linarith

 theorem J8_primitive_upper : SeventhEighth.J8 ≤
    (25/36)*log ((1/3)/a)+(4/9)*log ((1-a)/(2/3))-
      (8/9)*(3/2-1/(1-a))-(1/4)*log (2-3*a) := by
  have ha : 0 < a := SeventhEighth.classical_parameters.1
  have hab : a ≤ (1/3 : ℝ) := SeventhEighth.classical_parameters.2.1.le.trans
    SeventhEighth.classical_parameters.2.2.le
  have hi := packet_integrable (A := 25/36) (E := 0) (B := 4/9) (C := -8/9)
    (D := -3/4) (d := 2) (e := 3) ha hab (by norm_num) (by norm_num) (by norm_num)
  have hp (t : ℝ) (ht : t ∈ Icc a (1/3 : ℝ)) :
      log (2-3*t)/(t*(1-t)) ≤ packet (25/36) 0 (4/9) (-8/9) (-3/4) 2 3 t := by
    have ht0 := ha.trans_le ht.1
    have ht1 : 0 < 1-t := by linarith [ht.2]
    have ht2 : 0 < 2-3*t := by linarith [ht.2]
    have h := div_le_div_of_nonneg_right
      (log_upper (t := 2-3*t) (by linarith [ht.2])) (mul_pos ht0 ht1).le
    refine h.trans_eq ?_
    dsimp [packet,upperLog]
    have ht3 : 3-3*t ≠ 0 := by linarith
    field_simp [ht3]
    ring
  have h := intervalIntegral.integral_mono_on hab SeventhEighth.J8_integrable hi hp
  rw [packet_integral ha hab (by norm_num) (by norm_num) (by norm_num)] at h
  change SeventhEighth.J8 ≤ _ at h
  norm_num at h ⊢
  linarith

noncomputable def ninthA : ℝ := (1-2*s)*((1-s)^2+10*s*(1-s)+s^2)/(6*s*(1-s))
noncomputable def ninthD : ℝ := -1/(6*(1-s))
noncomputable def ninthB : ℝ := ninthA-ninthD-1/(6*s)
noncomputable def ninthC : ℝ := -8*s/3

 theorem J9_primitive_upper : J9 ≤
    ninthA*log (s/b)+ninthB*log ((1-b)/(1-s))+
      ninthC*(1/(1-s)-1/(1-b))+ninthD*log ((1-s-b)/(1-2*s)) := by
  have hb : 0 < b := by norm_num [b,ninthProfileK2]
  have hbs : b ≤ s := by norm_num [b,s,SeventhEighth.sigma,SeventhEighth.alpha,ninthProfileK2]
  have hs1 : s < 1 := by norm_num [s,SeventhEighth.sigma,SeventhEighth.alpha]
  have hs0 : 0 < s := hb.trans_le hbs
  have hs3 : s < 1/3 := by norm_num [s,SeventhEighth.sigma,SeventhEighth.alpha]
  have hi := packet_integrable (A := ninthA) (E := 0) (B := ninthB) (C := ninthC)
    (D := ninthD) (d := 1-s) (e := 1) hb hbs hs1 (by norm_num) (by linarith)
  have hp (t : ℝ) (ht : t ∈ Icc b s) :
      log ((1-s-t)/s)/(t*(1-t)) ≤ packet ninthA 0 ninthB ninthC ninthD (1-s) 1 t := by
    have ht0 := hb.trans_le ht.1
    have ht1 : 0 < 1-t := by linarith [ht.2]
    have ht2 : 0 < 1-s-t := by linarith [ht.2]
    have h := div_le_div_of_nonneg_right
      (log_upper (t := (1-s-t)/s) ((le_div_iff₀ hs0).2 (by linarith [ht.2])))
      (mul_pos ht0 ht1).le
    refine h.trans_eq ?_
    dsimp [packet,upperLog,ninthA,ninthB,ninthC,ninthD]
    have hsne : 1-s ≠ 0 := by linarith
    field_simp [hsne]
    ring
  have h := intervalIntegral.integral_mono_on hbs J9_integrable hi hp
  rw [packet_integral hb hbs hs1 (by norm_num) (by linarith)] at h
  change J9 ≤ _ at h
  norm_num at h ⊢
  rw [show 1-s-s=1-2*s by ring] at h
  exact h

 theorem log_split_two {x : ℝ} (hx : 0 < x) :
    log x = log 2+log (x/2) := by
  rw [← log_mul (by norm_num : (2 : ℝ) ≠ 0) (div_pos hx (by norm_num)).ne']
  congr 1; ring

 theorem log_split_four {x : ℝ} (hx : 0 < x) :
    log x = 2*log 2+log (x/4) := by
  rw [log_split_two hx,log_split_two (div_pos hx (by norm_num))]
  have he : x/2/2=x/4 := by ring
  rw [he]; ring

 theorem weighted_J_lt_twelve : 16*SeventhEighth.J7+8*SeventhEighth.J8+8*J9 < 12 := by
  have h7 := J7_primitive_upper
  have h8 := J8_primitive_upper
  have h9 := J9_primitive_upper
  have h71 := log_upper (t := (1/3)/s)
    (by norm_num [s,SeventhEighth.sigma,SeventhEighth.alpha])
  have h72 := log_upper (t := (1-s)/(2/3))
    (by norm_num [s,SeventhEighth.sigma,SeventhEighth.alpha])
  have h73 := log_lower (t := (1-2*s)/(1/3))
    (by norm_num [s,SeventhEighth.sigma,SeventhEighth.alpha])
  rw [log_split_four (by norm_num [a,SeventhEighth.alpha] : 0 < (1/3 : ℝ)/a)] at h8
  have h81 := log_upper (t := ((1/3)/a)/4) (by norm_num [a,SeventhEighth.alpha])
  have h82 := log_upper (t := (1-a)/(2/3)) (by norm_num [a,SeventhEighth.alpha])
  have h83 := log_lower (t := 2-3*a) (by norm_num [a,SeventhEighth.alpha])
  rw [log_split_two (by norm_num [b,s,SeventhEighth.sigma,SeventhEighth.alpha,ninthProfileK2] : 0 < s/b)] at h9
  have h91 := log_upper (t := (s/b)/2)
    (by norm_num [b,s,SeventhEighth.sigma,SeventhEighth.alpha,ninthProfileK2])
  have h92 := log_upper (t := (1-b)/(1-s))
    (by norm_num [b,s,SeventhEighth.sigma,SeventhEighth.alpha,ninthProfileK2])
  have h93 := log_lower (t := (1-s-b)/(1-2*s))
    (by norm_num [b,s,SeventhEighth.sigma,SeventhEighth.alpha,ninthProfileK2])
  have h2 := log_two_bounds.2
  norm_num [a,b,s,SeventhEighth.alpha,SeventhEighth.sigma,ninthProfileK2,
    ninthA,ninthB,ninthC,ninthD,upperLog,lowerLog] at h7 h8 h9 h71 h72 h73 h81 h82 h83 h91 h92 h93
  linarith

end Wu2008DoubleSieve.SharpJBalance
