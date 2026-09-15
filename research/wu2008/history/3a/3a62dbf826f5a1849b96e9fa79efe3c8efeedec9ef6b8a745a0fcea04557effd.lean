import R2GammaHighThetaPrime

noncomputable section
namespace WuPaper.R2GammaHigh
open Wu2008DoubleSieve WuSource.SrcSingle Real Finset Filter Set
open scoped Classical Topology Interval

theorem prime_integral_bounds (j : Fin 3) {δ : ℝ} (hh : δ ≤ 1/100) :
    0 ≤ primeIntegral j δ ∧ primeIntegral j δ ≤ 40 := by
  have hg := interval_geometry j
  have hden (t : ℝ) (ht : t ∈ Icc (psiLeft (j.castAdd 4)) (psiRight (j.castAdd 4))) :
      (1/40 : ℝ) ≤ t*((1/2-δ)-t) := by
    have ht0 : (1/4 : ℝ) ≤ t := hg.1.le.trans ht.1
    have hd0 : (1/10 : ℝ) ≤ (1/2-δ)-t := by linarith [ht.2, hg.2.2.1]
    have h := mul_le_mul ht0 hd0 (by norm_num : (0 : ℝ) ≤ 1/10) (by linarith : 0 ≤ t)
    norm_num at h
    exact h
  have hi : IntervalIntegrable (fun t : ℝ => 1/(t*((1/2-δ)-t)))
      MeasureTheory.volume (psiLeft (j.castAdd 4)) (psiRight (j.castAdd 4)) := by
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_const.div (by fun_prop)
    intro t ht
    rw [uIcc_of_le hg.2.1.le] at ht
    exact ne_of_gt (lt_of_lt_of_le (by norm_num) (hden t ht))
  constructor
  · apply intervalIntegral.integral_nonneg hg.2.1.le
    intro t ht
    exact div_nonneg (by norm_num) (le_trans (by norm_num) (hden t ht))
  · have h := intervalIntegral.integral_mono_on hg.2.1.le hi
      (intervalIntegrable_const (c := (40 : ℝ))) (fun t ht =>
        (div_le_iff₀ (show 0 < t*((1/2-δ)-t) from
          lt_of_lt_of_le (by norm_num) (hden t ht))).mpr (by linarith [hden t ht]))
    rw [intervalIntegral.integral_const] at h
    simp only [smul_eq_mul] at h
    change primeIntegral j δ ≤ _
    linarith [hg.1, hg.2.2.1]

theorem theta_exact {N : ℕ} {δ : ℝ} (j : Fin 3) (hN : 2 ≤ N) (he : Even N) :
    theta j N δ = 4*HighSix.liRatio N*subTwoMain j N δ*truncatedSixthMassScale N := by
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  rw [theta, windows, SingleUpperNormalization.theta_single_exact hN
    (psiPrimes (j.castAdd 4) N) (by
      intro p hp
      have hpp := (mem_primeWindow.mp hp).1
      have hcop := (mem_primeWindow.mp hp).2.1
      have hp2 : 2 < p := by
        have h2N : 2 ∣ N := even_iff_two_dvd.mp he
        have hpne : p ≠ 2 := by
          intro h
          subst p
          exact hpp.coprime_iff_not_dvd.mp hcop h2N
        have := hpp.two_le
        omega
      exact ⟨hpp, hp2, hcop⟩)]
  have hs : (∑ p ∈ psiPrimes (j.castAdd 4) N,
      1/(((p : ℝ)-2)*((1/2-δ)-log p/log N))) = subTwoMain j N δ := by
    apply sum_congr rfl
    intro p _
    simp only [HighSix.primeWeight, div_eq_mul_inv, mul_inv_rev, one_mul]
  rw [hs]
  unfold HighSix.liRatio truncatedSixthMassScale
  field_simp

theorem theta_integral_error {ε : ℝ} (heps : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N → ∀ j : Fin 3,
      ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1/100 →
      |theta j N δ - 4*primeIntegral j δ*truncatedSixthMassScale N| ≤
        ε*truncatedSixthMassScale N := by
  let η := ε/168
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨T1, hT14, hquad⟩ := subTwo_integral hη
  obtain ⟨T2, _, hli⟩ := HighSix.trueLi_relative hη
  obtain ⟨T3, _, hli1⟩ := HighSix.trueLi_relative (show (0 : ℝ) < 1 by norm_num)
  refine ⟨max T1 (max T2 T3), hT14.trans (le_max_left _ _), ?_⟩
  intro N hN he j δ hd hh
  have hN4 : 4 ≤ N := by omega
  have hscale := truncatedSixthClosure_scale_nonneg hN4
  have hq := hquad N (by omega) j δ hd hh
  have hr := hli N (by omega)
  have hr1 := hli1 N (by omega)
  have hr2 : |HighSix.liRatio N| ≤ 2 :=
    abs_le.mpr ⟨by linarith [(abs_le.mp hr1).1], by linarith [(abs_le.mp hr1).2]⟩
  have hI : |primeIntegral j δ| ≤ 40 := by
    rw [abs_of_nonneg (prime_integral_bounds j hh).1]
    exact (prime_integral_bounds j hh).2
  have hb : |4*HighSix.liRatio N*subTwoMain j N δ - 4*primeIntegral j δ| ≤ ε := by
    rw [show 4*HighSix.liRatio N*subTwoMain j N δ - 4*primeIntegral j δ =
      4*HighSix.liRatio N*(subTwoMain j N δ-primeIntegral j δ) +
        4*primeIntegral j δ*(HighSix.liRatio N-1) by ring]
    apply (abs_add_le _ _).trans
    rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
    have ha := mul_le_mul (mul_le_mul_of_nonneg_left hr2 (by norm_num : (0 : ℝ) ≤ 4))
      hq (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 4*2)
    have hb := mul_le_mul (mul_le_mul_of_nonneg_left hI (by norm_num : (0 : ℝ) ≤ 4))
      hr (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 4*40)
    have hηeq : 168*η = ε := by dsimp [η]; ring
    linarith only [ha, hb, hηeq]
  rw [theta_exact j (by omega) he, ← sub_mul, abs_mul, abs_of_nonneg hscale]
  exact mul_le_mul_of_nonneg_right hb hscale

theorem prime_integral_literal (j : Fin 3) {δ : ℝ} (hh : δ ≤ 1/100) :
    primeIntegral j δ =
      log (psiRight (j.castAdd 4) * ((1/2-δ)-psiLeft (j.castAdd 4)) /
        (psiLeft (j.castAdd 4) * ((1/2-δ)-psiRight (j.castAdd 4)))) / (1/2-δ) := by
  have hg := interval_geometry j
  let a := psiLeft (j.castAdd 4)
  let b := psiRight (j.castAdd 4)
  let c := (1/2 : ℝ)-δ
  have ha : 0 < a := by dsimp [a]; linarith [hg.1]
  have hab : a ≤ b := hg.2.1.le
  have hcb : 0 < c-b := by dsimp [c, b]; linarith [hg.2.2.1]
  have hca : 0 < c-a := by linarith
  have hc : 0 < c := by dsimp [c]; linarith
  have hb : 0 < b := ha.trans_le hab
  let F := fun t : ℝ => (log t-log (c-t))/c
  have hderiv : ∀ t ∈ uIcc a b, HasDerivAt F (1/(t*(c-t))) t := by
    intro t ht
    rw [uIcc_of_le hab] at ht
    have ht0 : t ≠ 0 := (ha.trans_le ht.1).ne'
    have hct : c-t ≠ 0 := (show 0 < c-t by linarith [ht.2]).ne'
    have h := (((hasDerivAt_id t).log ht0).sub
      (((hasDerivAt_id t).const_sub c).log hct)).div_const c
    convert h using 1
    dsimp only [id_eq]
    field_simp
    ring
  have hint : IntervalIntegrable (fun t : ℝ => 1/(t*(c-t))) MeasureTheory.volume a b := by
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_const.div (by fun_prop)
    intro t ht
    rw [uIcc_of_le hab] at ht
    exact mul_ne_zero (ha.trans_le ht.1).ne' (show 0 < c-t by linarith [ht.2]).ne'
  change (∫ t in a..b, 1/(t*(c-t))) = _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  dsimp [F]
  rw [log_div (mul_pos hb hca).ne' (mul_pos ha hcb).ne',
    log_mul hb.ne' hca.ne', log_mul ha.ne' hcb.ne']
  ring

theorem prime_integral_zero (j : Fin 3) :
    4*primeIntegral j 0 = 8*psiLogWeight (j.castAdd 4) := by
  rw [prime_integral_literal j (by norm_num)]
  fin_cases j <;> norm_num [psiLeft, psiRight, psiNode, psiLogWeight,
    sourceWeight, sourceNode, truncatedSixthLowerAlpha]

theorem prime_integral_continuous (j : Fin 3) : ContinuousAt (primeIntegral j) 0 := by
  let F := fun δ : ℝ =>
    log (psiRight (j.castAdd 4) * ((1/2-δ)-psiLeft (j.castAdd 4)) /
      (psiLeft (j.castAdd 4) * ((1/2-δ)-psiRight (j.castAdd 4)))) / (1/2-δ)
  have hg := interval_geometry j
  have ha : 0 < psiLeft (j.castAdd 4) := by linarith [hg.1]
  have hb : 0 < psiRight (j.castAdd 4) := ha.trans hg.2.1
  have hca : 0 < (1/2 : ℝ)-psiLeft (j.castAdd 4) := by linarith [hg.2.1, hg.2.2.1]
  have hcb : 0 < (1/2 : ℝ)-psiRight (j.castAdd 4) := by linarith [hg.2.2.1]
  have hF : ContinuousAt F 0 := by
    dsimp [F]
    apply ContinuousAt.div
    · apply ContinuousAt.log
      · apply ContinuousAt.div <;> first | fun_prop | positivity
      · positivity
    · fun_prop
    · norm_num
  apply hF.congr_of_eventuallyEq
  filter_upwards [eventually_lt_nhds (show (0 : ℝ) < 1/100 by norm_num)] with δ hδ
  exact (prime_integral_literal j hδ.le).symm

theorem common_delta_radius {ε : ℝ} (heps : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1/100 ∧ ∀ δ : ℝ, 0 < δ → δ < r →
      ∀ j : Fin 3, |4*primeIntegral j δ - 8*psiLogWeight (j.castAdd 4)| < ε := by
  have hnear (j : Fin 3) : ∃ r : ℝ, 0 < r ∧
      ∀ δ : ℝ, dist δ 0 < r → |4*primeIntegral j δ - 8*psiLogWeight (j.castAdd 4)| < ε := by
    obtain ⟨r, hr, h⟩ := Metric.continuousAt_iff.mp
      ((prime_integral_continuous j).const_mul 4) ε heps
    refine ⟨r, hr, ?_⟩
    intro δ hδ
    have h' := h hδ
    simpa only [Real.dist_eq, prime_integral_zero] using h'
  obtain ⟨r0, hr0, h0⟩ := hnear 0
  obtain ⟨r1, hr1, h1⟩ := hnear 1
  obtain ⟨r2, hr2, h2⟩ := hnear 2
  let r := min (min r0 r1) (min r2 (1/100))
  have hr : 0 < r := lt_min (lt_min hr0 hr1) (lt_min hr2 (by norm_num))
  refine ⟨r, hr, (min_le_right _ _).trans (min_le_right _ _), ?_⟩
  intro δ hd hdr j
  have hdist : dist δ 0 < r := by simpa only [Real.dist_eq, sub_zero, abs_of_pos hd] using hdr
  fin_cases j
  · exact h0 δ (hdist.trans_le ((min_le_left _ _).trans (min_le_left _ _)))
  · exact h1 δ (hdist.trans_le ((min_le_left _ _).trans (min_le_right _ _)))
  · exact h2 δ (hdist.trans_le ((min_le_right _ _).trans (min_le_left _ _)))

#check @prime_integral_bounds
#check @theta_exact
#check @theta_integral_error
#check @prime_integral_literal
#check @prime_integral_zero
#check @prime_integral_continuous
#check @common_delta_radius
#print axioms prime_integral_bounds
#print axioms theta_exact
#print axioms theta_integral_error
#print axioms prime_integral_literal
#print axioms prime_integral_zero
#print axioms prime_integral_continuous
#print axioms common_delta_radius
end WuPaper.R2GammaHigh
