import R2XiSecondDefinitions

noncomputable section
namespace WuPaper.R2Xi
open Real Set MeasureTheory NodeExtension Wu2008DoubleSieve
open WuPaper.RMapMMatrix WuPaper.RMapMSigma
open scoped Interval

theorem closed_indicator_split {a b c t : ℝ} (hab : a ≤ b) (hbc : b ≤ c)
    (ht : t ≠ b) :
    (Icc a c).indicator (fun _ => (1 : ℝ)) t =
      (Icc a b).indicator (fun _ => (1 : ℝ)) t +
      (Icc b c).indicator (fun _ => (1 : ℝ)) t := by
  by_cases hm : t ∈ Icc a c
  · by_cases htb : t < b
    · have hleft : t ∈ Icc a b := ⟨hm.1, htb.le⟩
      have hright : t ∉ Icc b c := fun h => (not_le.mpr htb) h.1
      simp only [indicator_of_mem hm, indicator_of_mem hleft, indicator_of_notMem hright, add_zero]
    · have hbt : b < t := lt_of_le_of_ne (le_of_not_gt htb) (Ne.symm ht)
      have hright : t ∈ Icc b c := ⟨hbt.le, hm.2⟩
      have hleft : t ∉ Icc a b := fun h => (not_le.mpr hbt) h.2
      simp only [indicator_of_mem hm, indicator_of_mem hright, indicator_of_notMem hleft, zero_add]
  · have hleft : t ∉ Icc a b := fun h => hm ⟨h.1, h.2.trans hbc⟩
    have hright : t ∉ Icc b c := fun h => hm ⟨hab.trans h.1, h.2⟩
    simp only [indicator_of_notMem hm, indicator_of_notMem hleft, indicator_of_notMem hright, add_zero]

theorem K65_kernel_identity {p : SecondFunctionalParameters} (hp : PropositionFourGeometry p)
    {t : ℝ} (ht : t ∈ Icc 1 3) (hne : t ≠ alpha2 p) :
    K65 p t = JKernel p.s p.S t + JKernel p.kappa2 p.S t +
      JKernel p.kappa3 p.S t + 4 * upperKernel p.S t + upperKernel p.kappa1 t := by
  rcases second_parameter_bounds hp with ⟨hs, hS, _, hk1, hk2, hk3, _⟩
  have ha := second_alpha_bounds hp
  have hb : alpha2 p ≤ 3 := (ha.1 1).2
  have hsplit := closed_indicator_split ha.2.2.2.1 hb hne
  have hs1 : p.s - 1 ≠ 0 := by linarith
  have hS1 : p.S - 1 ≠ 0 := by linarith
  have hk11 : p.kappa1 - 1 ≠ 0 := by linarith
  have hk21 : p.kappa2 - 1 ≠ 0 := by linarith
  have hk31 : p.kappa3 - 1 ≠ 0 := by linarith
  have ht1 : t + 1 ≠ 0 := by linarith [ht.1]
  have h1024 : log (1024 : ℝ) = 5 * log 4 := by
    rw [show (1024 : ℝ) = 4 ^ 5 by norm_num, log_pow]
    norm_num
  dsimp only [K65, JKernel, upperKernel]
  change (Icc (p.kappa1 - 2) 3).indicator (fun _ => (1 : ℝ)) t =
    (Icc (alpha1 p) (alpha2 p)).indicator (fun _ => (1 : ℝ)) t +
    (Icc (p.S - 2) 3).indicator (fun _ => (1 : ℝ)) t at hsplit
  rw [hsplit]
  simp only [alpha1, alpha2, alpha3, alpha4, alpha5,
    log_div (by norm_num : (1024 : ℝ) ≠ 0)
      (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hs1 hS1) hk11) hk21) hk31),
    log_div (pow_ne_zero 5 ht1)
      (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hs1 hS1) hk11) hk21) hk31),
    log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero hs1 hS1) hk11) hk21) hk31,
    log_mul (mul_ne_zero (mul_ne_zero hs1 hS1) hk11) hk21,
    log_mul (mul_ne_zero hs1 hS1) hk11, log_mul hs1 hS1,
    log_div hS1 hs1, log_div hS1 hk21, log_div hS1 hk31,
    log_div (by norm_num : (4 : ℝ) ≠ 0) hS1,
    log_div (by norm_num : (4 : ℝ) ≠ 0) hk11,
    log_div ht1 hS1, log_div ht1 hk11, log_pow, h1024]
  push_cast
  ring

theorem K65_integral_identity {f : ℝ → ℝ} (hf : IntervalIntegrable f volume 1 3)
    {p : SecondFunctionalParameters} (hp : PropositionFourGeometry p) :
    IntervalIntegrable (fun t => f t * K65 p t) volume 1 3 ∧
    (∫ t in (1 : ℝ)..3, f t * K65 p t) =
      source63RHS f (1 - 1 / p.s) (1 - 1 / p.S) p.S +
      source63RHS f (1 - 1 / p.kappa2) (1 - 1 / p.S) p.S +
      source63RHS f (1 - 1 / p.kappa3) (1 - 1 / p.S) p.S +
      4 * eProfile f p.S + eProfile f p.kappa1 := by
  rcases second_parameter_bounds hp with ⟨hs, hS, hS5, hk1, hk2, hk3, hsS, h2S, h3S, hr2, hr3⟩
  rcases hp with ⟨_, hs3, _, _, hsK, h32, h21, h1S, hr, hrest⟩
  have hp : PropositionFourGeometry p :=
    ⟨hs, hs3, hS, hS5, hsK, h32, h21, h1S, hr, hrest⟩
  have hj := J_source_identity hf hs hS hS5 hsS hr
  have hj2 := J_source_identity hf hk2 hS hS5 h2S hr2
  have hj3 := J_source_identity hf hk3 hS hS5 h3S hr3
  have hu := upperKernel_integrable hf ⟨hS, hS5⟩
  have hu1 := upperKernel_integrable hf ⟨hk1, h1S.trans hS5⟩
  have he : ∀ᵐ t ∂volume, t ∈ uIoc (1 : ℝ) 3 →
      f t * K65 p t = f t * JKernel p.s p.S t + f t * JKernel p.kappa2 p.S t +
        f t * JKernel p.kappa3 p.S t + 4 * (f t * upperKernel p.S t) +
        f t * upperKernel p.kappa1 t := by
    filter_upwards [ae_neq volume (alpha2 p)] with t ht hmem
    have hm := uIoc_subset_uIcc hmem
    rw [uIcc_of_le (by norm_num : (1 : ℝ) ≤ 3)] at hm
    rw [K65_kernel_identity hp hm ht]
    ring
  have hi := (((hj.1.add hj2.1).add hj3.1).add (hu.const_mul 4)).add hu1
  refine ⟨hi.congr_ae ?_, ?_⟩
  · rw [ae_restrict_iff' measurableSet_uIoc]
    filter_upwards [he] with t ht
    exact fun hm => (ht hm).symm
  ·
    rw [intervalIntegral.integral_congr_ae he,
    intervalIntegral.integral_add (((hj.1.add hj2.1).add hj3.1).add (hu.const_mul 4)) hu1,
    intervalIntegral.integral_add ((hj.1.add hj2.1).add hj3.1) (hu.const_mul 4),
    intervalIntegral.integral_add (hj.1.add hj2.1) hj3.1,
    intervalIntegral.integral_add hj.1 hj2.1, intervalIntegral.integral_const_mul,
    hj.2, hj2.2, hj3.2, upperKernel_identity hf ⟨hS, hS5⟩,
    upperKernel_identity hf ⟨hk1, h1S.trans hS5⟩]

theorem equation65_actual {δ : ℝ} (hd : 0 < δ) (hdhi : δ ≤ 1 / 10)
    {p : SecondFunctionalParameters} (hp : PropositionFourGeometry p) :
    (∫ t in (1 : ℝ)..3, wuImprovementLimit true δ t * K65 p t) ≤
      (∫ u in (1 - 1 / p.s)..(1 - 1 / p.S),
        wuImprovementLimit false δ (p.S * u) / (u * (1 - u))) +
      (∫ u in (1 - 1 / p.kappa2)..(1 - 1 / p.S),
        wuImprovementLimit false δ (p.S * u) / (u * (1 - u))) +
      (∫ u in (1 - 1 / p.kappa3)..(1 - 1 / p.S),
        wuImprovementLimit false δ (p.S * u) / (u * (1 - u))) +
      4 * wuImprovementLimit true δ p.S + wuImprovementLimit true δ p.kappa1 := by
  have hf := wuImprovementLimit_intervalIntegrable true hd (by linarith : δ < 1 / 2)
    (a := 1) (b := 3) (by norm_num) (by norm_num) (by norm_num)
  rw [(K65_integral_identity hf hp).2]
  rcases second_parameter_bounds hp with ⟨hs, hS, hS5, hk1, hk2, hk3, hsS, h2S, h3S, hr2, hr3⟩
  rcases hp with ⟨_, _, _, _, _, _, _, h1S, hr, _⟩
  have hj (r : ℝ) (hr0 : 2 ≤ r) (hrS : r < p.S) (hrr : 2 ≤ p.S - p.S / r) :=
    let hg := J_endpoints hr0 hS hS5 hrS hrr
    (original_lemma61 hd hdhi).2.2 (1 - 1 / r) (1 - 1 / p.S) p.S
      hg.1 hg.2.1 hg.2.2.1 hg.2.2.2.1 hg.2.2.2.2
  have h0 := hj p.s hs hsS hr
  have h2 := hj p.kappa2 hk2 h2S hr2
  have h3 := hj p.kappa3 hk3 h3S hr3
  have hu := (actual_continuous_extension hd hdhi).2.2 p.S ⟨hS, hS5⟩
  have hu1 := (actual_continuous_extension hd hdhi).2.2 p.kappa1 ⟨hk1, h1S.trans hS5⟩
  linarith

end WuPaper.R2Xi

run_cmd do
  for (name, _) in (← Lean.getEnv).constants.toList do
    if name.getPrefix == `WuPaper.R2Xi then
      Lean.Elab.Command.elabCommand (← `(#check @$(Lean.mkIdent name)))
      Lean.Elab.Command.elabCommand (← `(#print axioms $(Lean.mkIdent name)))
