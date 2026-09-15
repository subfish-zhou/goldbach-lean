import MathlibNt.Wu2008DoubleSieve.SharpMassBalance

namespace Wu2008DoubleSieve.UnroundedPayments
open Real Set SharpLogRecurrence

/-- The derivative is positive only in the interior; its value at one may vanish. -/
theorem lowerLog_lt_log {t : ℝ} (ht : 1 < t) : lowerLog t < log t := by
  have hm : StrictMonoOn (fun x => log x-lowerLog x) (Ici 1) :=
    strictMonoOn_of_hasDerivWithinAt_pos (convex_Ici 1)
      (fun x hx => (lower_gap_derivative hx).continuousAt.continuousWithinAt)
      (fun x hx => (lower_gap_derivative (interior_subset hx)).hasDerivWithinAt)
      (fun x hx => by
        have hx1 : 1 < x := by simpa only [interior_Ici,mem_Ioi] using hx
        exact div_pos (pow_pos (sub_pos.mpr hx1) 4)
          (mul_pos (by linarith) (pow_pos (by linarith) 4)))
  have h := hm (by simp) ht.le ht
  norm_num [lowerLog] at h
  exact h

noncomputable def fifthRational : ℝ :=
  2*SharpMassBalance.fifthDensity*(lowerLog (SharpMassBalance.b/SharpMassBalance.a))^2

/-- The original fixed density and the original fixed log payment are strictly positive. -/
theorem fifth_payment_positive :
    0 < SharpMassBalance.fifthDensity ∧
    0 < lowerLog (SharpMassBalance.b/SharpMassBalance.a) := by
  norm_num [SharpMassBalance.fifthDensity,SharpMassBalance.s0,SharpMassBalance.a,
    SharpMassBalance.b,truncatedSixthLowerAlpha,truncatedSixthLowerBeta,lowerLog]

/-- Strictness comes from the log gap, before using the existing non-strict integral bound. -/
theorem fifthRational_lt_fifthPairFlin : fifthRational < fifthPairFlin := by
  have hl := lowerLog_lt_log (t := SharpMassBalance.b/SharpMassBalance.a)
    (by norm_num [SharpMassBalance.a,SharpMassBalance.b,
      truncatedSixthLowerAlpha,truncatedSixthLowerBeta])
  obtain ⟨hd,hp⟩ := fifth_payment_positive
  have hsq : (lowerLog (SharpMassBalance.b/SharpMassBalance.a))^2 <
      (log (SharpMassBalance.b/SharpMassBalance.a))^2 := by nlinarith
  have hm := mul_lt_mul_of_pos_left hsq (mul_pos (by norm_num : (0 : ℝ) < 2) hd)
  have hi := SharpMassBalance.fifth_log_lower
  rw [← log_div (by norm_num [SharpMassBalance.b,truncatedSixthLowerBeta])
    (by norm_num [SharpMassBalance.a,truncatedSixthLowerAlpha])] at hi
  exact hm.trans_le hi

theorem fifthRational_eq : fifthRational =
    (76127082192391175783670827286107777024/49308577466178621190527521171096611221 : ℝ) := by
  norm_num [fifthRational,SharpMassBalance.fifthDensity,SharpMassBalance.s0,
    SharpMassBalance.a,SharpMassBalance.b,truncatedSixthLowerAlpha,truncatedSixthLowerBeta,lowerLog]

theorem fifthRational_gt_old : (3/2 : ℝ) < fifthRational := by
  rw [fifthRational_eq]
  norm_num

noncomputable def j7Upper : ℝ :=
  16055256726697334136505614781/219428002893992653201870442520
noncomputable def j8Upper : ℝ :=
  38631675036930513122533/58123722505742197073280
noncomputable def j9Upper : ℝ :=
  275938557198367451880230872675789916592/409354979752334202072944129963534298617
noncomputable def weightedJUpper : ℝ := 16*j7Upper+8*j8Upper+8*j9Upper

/-- Retain the payment already used in the original seventh primitive upper bound. -/
theorem J7_le_j7Upper : SeventhEighth.J7 ≤ j7Upper := by
  have h7 := SharpJBalance.J7_primitive_upper
  have h71 := log_upper (t := (1/3)/SharpJBalance.s)
    (by norm_num [SharpJBalance.s,SeventhEighth.sigma,SeventhEighth.alpha])
  have h72 := log_upper (t := (1-SharpJBalance.s)/(2/3))
    (by norm_num [SharpJBalance.s,SeventhEighth.sigma,SeventhEighth.alpha])
  have h73 := log_lower (t := (1-2*SharpJBalance.s)/(1/3))
    (by norm_num [SharpJBalance.s,SeventhEighth.sigma,SeventhEighth.alpha])
  norm_num [SharpJBalance.s,SeventhEighth.alpha,SeventhEighth.sigma,
    upperLog,lowerLog,j7Upper] at h7 h71 h72 h73 ⊢
  linarith

/-- The original four-way split and the original upper bound on log two are unchanged. -/
theorem J8_le_j8Upper : SeventhEighth.J8 ≤ j8Upper := by
  have h8 := SharpJBalance.J8_primitive_upper
  rw [SharpJBalance.log_split_four
    (by norm_num [SharpJBalance.a,SeventhEighth.alpha] : 0 < (1/3 : ℝ)/SharpJBalance.a)] at h8
  have h81 := log_upper (t := ((1/3)/SharpJBalance.a)/4)
    (by norm_num [SharpJBalance.a,SeventhEighth.alpha])
  have h82 := log_upper (t := (1-SharpJBalance.a)/(2/3))
    (by norm_num [SharpJBalance.a,SeventhEighth.alpha])
  have h83 := log_lower (t := 2-3*SharpJBalance.a)
    (by norm_num [SharpJBalance.a,SeventhEighth.alpha])
  have h2 := log_two_bounds.2
  norm_num [SharpJBalance.a,SeventhEighth.alpha,upperLog,lowerLog,j8Upper] at h8 h81 h82 h83 ⊢
  linarith

/-- The original two-way split and all signs in the ninth primitive are retained. -/
theorem J9_le_j9Upper : J9 ≤ j9Upper := by
  have h9 := SharpJBalance.J9_primitive_upper
  rw [SharpJBalance.log_split_two (by norm_num [SharpJBalance.b,SharpJBalance.s,
    SeventhEighth.sigma,SeventhEighth.alpha,ninthProfileK2] :
    0 < SharpJBalance.s/SharpJBalance.b)] at h9
  have h91 := log_upper (t := (SharpJBalance.s/SharpJBalance.b)/2)
    (by norm_num [SharpJBalance.b,SharpJBalance.s,SeventhEighth.sigma,SeventhEighth.alpha,ninthProfileK2])
  have h92 := log_upper (t := (1-SharpJBalance.b)/(1-SharpJBalance.s))
    (by norm_num [SharpJBalance.b,SharpJBalance.s,SeventhEighth.sigma,SeventhEighth.alpha,ninthProfileK2])
  have h93 := log_lower (t := (1-SharpJBalance.s-SharpJBalance.b)/(1-2*SharpJBalance.s))
    (by norm_num [SharpJBalance.b,SharpJBalance.s,SeventhEighth.sigma,SeventhEighth.alpha,ninthProfileK2])
  have h2 := log_two_bounds.2
  norm_num [SharpJBalance.b,SharpJBalance.s,SeventhEighth.alpha,SeventhEighth.sigma,
    ninthProfileK2,SharpJBalance.ninthA,SharpJBalance.ninthB,SharpJBalance.ninthC,
    SharpJBalance.ninthD,upperLog,lowerLog,j9Upper] at h9 h91 h92 h93 ⊢
  linarith

theorem original_weightedJ_le :
    16*SeventhEighth.J7+8*SeventhEighth.J8+8*J9 ≤ weightedJUpper := by
  unfold weightedJUpper
  linarith [J7_le_j7Upper,J8_le_j8Upper,J9_le_j9Upper]

theorem weightedJUpper_lt_old : weightedJUpper < 12 := by
  norm_num [weightedJUpper,j7Upper,j8Upper,j9Upper]

end Wu2008DoubleSieve.UnroundedPayments
