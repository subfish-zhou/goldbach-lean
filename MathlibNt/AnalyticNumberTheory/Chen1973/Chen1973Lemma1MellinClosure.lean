import MathlibNt.AnalyticNumberTheory.Chen1973.Chen1973Lemma1PerronKernelCore

noncomputable section
open MeasureTheory Filter Set
open scoped Interval Topology
namespace AnalyticNumberTheory.LargeSieve

lemma test_int_gamma {q : ℂ} (hq : 0 < q.re) (n : ℕ) :
    IntegrableOn (fun u : ℝ => Complex.exp (-q * u) * (chenGammaCDF n u : ℂ)) (Ioi 0) := by
  classical
  have hq1 : 0 < (q + 1).re := by simpa using (show 0 < q.re + 1 by linarith)
  have hsum : ∀ S : Finset ℕ, IntegrableOn
      (fun u : ℝ => ∑ ν ∈ S, chenLaplaceMoment (q + 1) ν u / (ν.factorial : ℂ))
      (Ioi 0) := by
    intro S
    induction S using Finset.induction with
    | empty => simp
    | @insert a S ha ih =>
        simp_rw [Finset.sum_insert ha]
        exact ((integrableOn_chenLaplaceMoment hq1 a).div_const _).add ih
  have hmain := (integrableOn_chenLaplaceMoment hq 0).sub
    (hsum (Finset.range (n + 1)))
  apply hmain.congr
  filter_upwards with u
  simp only [Pi.sub_apply, chenLaplaceMoment, pow_zero, mul_one, chenGammaCDF,
    chenExpPartial, Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_mul,
    Complex.ofReal_exp, Complex.ofReal_neg]
  rw [mul_sub, mul_one]
  congr 1
  push_cast
  rw [← mul_assoc, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ν hν
  rw [← Complex.exp_add]
  congr 1
  ring

/-- The Gamma tail is a shifted Laplace moment, including its factorial normalization. -/
private lemma gammaTail_eq_laplaceMoment (q : ℂ) (n : ℕ) (u : ℝ) :
    Complex.exp (-q * u) *
        ((Real.exp (-u) * u ^ n / (n.factorial : ℝ) : ℝ) : ℂ) =
      chenLaplaceMoment (q + 1) n u / (n.factorial : ℂ) := by
  simp only [chenLaplaceMoment, Complex.ofReal_div, Complex.ofReal_mul,
    Complex.ofReal_exp, Complex.ofReal_neg, Complex.ofReal_pow,
    Complex.ofReal_natCast]
  have hexp : Complex.exp (-(q + 1) * (u : ℂ)) =
      Complex.exp (-q * (u : ℂ)) * Complex.exp (-(u : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  rw [hexp]
  ring

lemma test_int_gamma_value {q : ℂ} (hq : 0 < q.re) (n : ℕ) :
    ∫ u : ℝ in Ioi 0, Complex.exp (-q * u) * (chenGammaCDF n u : ℂ) =
      1 / (q * (1 + q) ^ (n + 1)) := by
  have hq1 : 0 < (q + 1).re := by simpa using (show 0 < q.re + 1 by linarith)
  induction n with
  | zero =>
      have h0 := integral_chenLaplaceMoment hq 0
      have h1 := integral_chenLaplaceMoment hq1 0
      have hi0 := integrableOn_chenLaplaceMoment hq 0
      have hi1 := integrableOn_chenLaplaceMoment hq1 0
      rw [show (∫ u : ℝ in Ioi 0,
          Complex.exp (-q * u) * (chenGammaCDF 0 u : ℂ)) =
          (∫ u : ℝ in Ioi 0, chenLaplaceMoment q 0 u) -
            ∫ u : ℝ in Ioi 0, chenLaplaceMoment (q + 1) 0 u by
        rw [← integral_sub hi0 hi1]
        apply setIntegral_congr_fun measurableSet_Ioi
        intro u hu
        simp only [chenGammaCDF, chenExpPartial, chenLaplaceMoment, pow_zero,
          Finset.sum_range_succ, Finset.sum_range_zero, Finset.sum_empty,
          Finset.sum_insert, Nat.factorial_zero, Nat.cast_one, div_one,
          Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_mul,
          Complex.ofReal_exp, Complex.ofReal_neg, mul_one, zero_add]
        rw [mul_sub, mul_one]
        congr 1
        rw [← Complex.exp_add]
        congr 1
        ring, h0, h1]
      have hq0 : q ≠ 0 := by intro h; simpa [h] using hq
      have hq10 : q + 1 ≠ 0 := by intro h; simpa [h] using hq1
      rw [add_comm 1 q]
      field_simp [hq0, hq10]
      ring
  | succ n ih =>
      have hitail : IntegrableOn (fun u : ℝ =>
          Complex.exp (-q * u) *
            ((Real.exp (-u) * u ^ (n + 1) / ((n + 1).factorial : ℝ) : ℝ) : ℂ))
          (Ioi 0) := by
        simp_rw [gammaTail_eq_laplaceMoment]
        exact (integrableOn_chenLaplaceMoment hq1 (n + 1)).div_const
          ((n + 1).factorial : ℂ)
      rw [show (∫ u : ℝ in Ioi 0,
          Complex.exp (-q * u) * (chenGammaCDF (n + 1) u : ℂ)) =
          (∫ u : ℝ in Ioi 0,
            Complex.exp (-q * u) * (chenGammaCDF n u : ℂ)) -
          ∫ u : ℝ in Ioi 0, Complex.exp (-q * u) *
            ((Real.exp (-u) * u ^ (n + 1) / ((n + 1).factorial : ℝ) : ℝ) : ℂ) by
        rw [← integral_sub (test_int_gamma hq n) hitail]
        apply setIntegral_congr_fun measurableSet_Ioi
        intro u hu
        dsimp only
        rw [chenGammaCDF_succ]
        push_cast
        ring, ih]
      rw [show (∫ u : ℝ in Ioi 0, Complex.exp (-q * u) *
          ((Real.exp (-u) * u ^ (n + 1) / ((n + 1).factorial : ℝ) : ℝ) : ℂ)) =
          1 / (q + 1) ^ (n + 2) by
        simp_rw [gammaTail_eq_laplaceMoment]
        rw [integral_div, integral_chenLaplaceMoment hq1]
        have hf : ((n + 1).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (n + 1)
        field_simp]
      have hq0 : q ≠ 0 := by intro h; simpa [h] using hq
      have hq10 : q + 1 ≠ 0 := by intro h; simpa [h] using hq1
      rw [add_comm 1 q]
      field_simp [hq0, hq10]
      ring

lemma test_scaled_integrable {q : ℂ} (hq : 0 < q.re) {A : ℝ} (hA : 0 < A) (n : ℕ) :
    IntegrableOn (fun u : ℝ => Complex.exp (-q * u) *
      (chenGammaCDF n (A * u) : ℂ)) (Ioi 0) := by
  let g : ℝ → ℂ := fun v => Complex.exp (-(q / A) * v) * (chenGammaCDF n v : ℂ)
  have hqA : 0 < (q / A).re := by
    simpa [Complex.div_re, hA.ne'] using mul_pos hq hA
  have hg : IntegrableOn g (Ioi 0) := test_int_gamma hqA n
  have hgcomp : IntegrableOn (fun u => g (A * u)) (Ioi 0) :=
    (integrableOn_Ioi_comp_mul_left_iff g 0 hA).2 (by simpa using hg)
  apply hgcomp.congr
  filter_upwards with u
  dsimp [g]
  congr 1
  congr 1
  push_cast
  field_simp [hA.ne']

lemma test_scaled_value {q : ℂ} (hq : 0 < q.re) {A : ℝ} (hA : 0 < A) (n : ℕ) :
    ∫ u : ℝ in Ioi 0, Complex.exp (-q * u) *
      (chenGammaCDF n (A * u) : ℂ) =
      1 / (q * (1 + q / A) ^ (n + 1)) := by
  let g : ℝ → ℂ := fun v => Complex.exp (-(q / A) * v) * (chenGammaCDF n v : ℂ)
  have hqA : 0 < (q / A).re := by
    simpa [Complex.div_re, hA.ne'] using mul_pos hq hA
  have heq : (∫ u : ℝ in Ioi 0, Complex.exp (-q * u) *
      (chenGammaCDF n (A * u) : ℂ)) = ∫ u : ℝ in Ioi 0, g (A * u) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u hu
    dsimp [g]
    congr 1
    congr 1
    push_cast
    field_simp [hA.ne']
  rw [heq, integral_comp_mul_left_Ioi g 0 hA, mul_zero, test_int_gamma_value hqA]
  rw [Complex.real_smul]
  push_cast
  field_simp [hA.ne']

lemma chen_cpow_exp_neg (s : ℂ) (u : ℝ) :
    ((Real.exp (-u) : ℝ) : ℂ) ^ (s - 1) * (Real.exp (-u) : ℂ) =
      Complex.exp (-s * u) := by
  have he : ((Real.exp (-u) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)
  rw [Complex.cpow_def_of_ne_zero he]
  rw [← Complex.ofReal_log (Real.exp_pos _).le, Real.log_exp]
  rw [Complex.ofReal_exp]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private lemma exp_neg_hasDerivWithinAt (u : ℝ) :
    HasDerivWithinAt (fun u : ℝ => Real.exp (-u))
      (-Real.exp (-u)) Set.univ u := by
  exact mul_neg_one (Real.exp (-u)) ▸
    ((Real.hasDerivAt_exp (-u)).comp u (hasDerivAt_neg u)).hasDerivWithinAt

private lemma exp_neg_image_univ :
    (fun u : ℝ => Real.exp (-u)) '' Set.univ = Set.Ioi 0 := by
  rw [show (fun u : ℝ => Real.exp (-u)) = Real.exp ∘ Neg.neg by rfl,
    Set.image_comp, Set.image_univ_of_surjective neg_surjective,
    Set.image_univ, Real.range_exp]

private lemma exp_neg_injOn :
    Set.univ.InjOn (fun u : ℝ => Real.exp (-u)) := by
  intro a _ b _ hab
  exact neg_injective (Real.exp_injective hab)

lemma mellin_eq_integral_exp_neg (f : ℝ → ℂ) (s : ℂ) :
    mellin f s = ∫ u : ℝ, Complex.exp (-s * u) * f (Real.exp (-u)) := by
  let φ : ℝ → ℝ := fun u => Real.exp (-u)
  have hderiv : ∀ u ∈ (Set.univ : Set ℝ),
      HasDerivWithinAt φ (-Real.exp (-u)) Set.univ u := by
    intro u _
    exact exp_neg_hasDerivWithinAt u
  have himage : φ '' Set.univ = Set.Ioi 0 := exp_neg_image_univ
  have hinj : Set.univ.InjOn φ := exp_neg_injOn
  unfold mellin
  rw [← himage]
  rw [integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ hderiv hinj]
  rw [setIntegral_univ]
  apply integral_congr_ae
  filter_upwards with u
  dsimp [φ]
  rw [abs_neg, abs_of_pos (Real.exp_pos _)]
  rw [← mul_assoc, mul_comm (Real.exp (-u) : ℂ), chen_cpow_exp_neg]

lemma chen1973GammaDensityPrimitive_exp_neg {x : ℝ} (hx : 1 < x) (u : ℝ) :
    chen1973GammaDensityPrimitive x (Real.exp (-u)) =
      if u ≤ 0 then 0 else
        (chenGammaCDF (chen1973PerronOrder x) (chen1973PerronScale x * u) : ℂ) := by
  by_cases hu : u ≤ 0
  · have he : 1 ≤ Real.exp (-u) := (Real.one_le_exp_iff).2 (by linarith)
    simp [chen1973GammaDensityPrimitive, hu, he]
  · have hu' : 0 < u := lt_of_not_ge hu
    have he0 : 0 < Real.exp (-u) := Real.exp_pos _
    have he1 : Real.exp (-u) < 1 := (Real.exp_lt_one_iff).2 (by linarith)
    have hlog : Real.log (1 / Real.exp (-u)) = u := by
      rw [one_div, ← Real.exp_neg, neg_neg, Real.log_exp]
    simp [chen1973GammaDensityPrimitive, hu, not_le_of_gt he0,
      not_le_of_gt he1, hlog]

lemma mellin_chen1973GammaDensityPrimitive {x : ℝ} (hx : 1 < x)
    {s : ℂ} (hs : 0 < s.re) :
    mellin (chen1973GammaDensityPrimitive x) s = chen1973MellinKernel x s := by
  have hA : 0 < chen1973PerronScale x := by
    exact Real.rpow_pos_of_pos (Real.log_pos hx) _
  rw [mellin_eq_integral_exp_neg]
  have hfun : (fun u : ℝ => Complex.exp (-s * u) *
      chen1973GammaDensityPrimitive x (Real.exp (-u))) =
      (Set.Ioi (0 : ℝ)).indicator (fun u : ℝ => Complex.exp (-s * u) *
        (chenGammaCDF (chen1973PerronOrder x) (chen1973PerronScale x * u) : ℂ)) := by
    funext u
    rw [chen1973GammaDensityPrimitive_exp_neg hx]
    by_cases hu : 0 < u
    · simp [hu, not_le_of_gt hu]
    · have hu' : u ≤ 0 := le_of_not_gt hu
      simp [hu, hu']
  rw [hfun, integral_indicator measurableSet_Ioi]
  rw [test_scaled_value hs hA]
  rfl

lemma mellinConvergent_chen1973GammaDensityPrimitive {x : ℝ} (hx : 1 < x)
    {s : ℂ} (hs : 0 < s.re) :
    MellinConvergent (chen1973GammaDensityPrimitive x) s := by
  let φ : ℝ → ℝ := fun u => Real.exp (-u)
  have hderiv : ∀ u ∈ (Set.univ : Set ℝ),
      HasDerivWithinAt φ (-Real.exp (-u)) Set.univ u := by
    intro u _
    exact exp_neg_hasDerivWithinAt u
  have himage : φ '' Set.univ = Set.Ioi 0 := exp_neg_image_univ
  have hinj : Set.univ.InjOn φ := exp_neg_injOn
  have hA : 0 < chen1973PerronScale x :=
    Real.rpow_pos_of_pos (Real.log_pos hx) _
  let g : ℝ → ℂ := fun u => Complex.exp (-s * u) *
    (chenGammaCDF (chen1973PerronOrder x) (chen1973PerronScale x * u) : ℂ)
  have hgOn : IntegrableOn g (Ioi 0) := test_scaled_integrable hs hA _
  have hg : Integrable ((Ioi (0 : ℝ)).indicator g) :=
    hgOn.integrable_indicator measurableSet_Ioi
  rw [MellinConvergent, ← himage,
    integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ hderiv hinj]
  rw [integrableOn_univ]
  apply hg.congr
  filter_upwards with u
  dsimp [φ, g]
  rw [abs_neg, abs_of_pos (Real.exp_pos _)]
  rw [chen1973GammaDensityPrimitive_exp_neg hx]
  by_cases hu : 0 < u
  · rw [if_neg (not_le_of_gt hu)]
    rw [Set.indicator_of_mem (show u ∈ Ioi (0 : ℝ) from hu)]
    symm
    rw [← mul_assoc,
      mul_comm (Real.exp (-u) : ℂ), chen_cpow_exp_neg]
  · have hu' : u ≤ 0 := le_of_not_gt hu
    simp [hu, hu']

/-- The Gamma primitive is continuous throughout the positive half-line,
including the glued endpoint `r = 1`. -/
theorem continuousOn_chen1973GammaDensityPrimitive (x : ℝ) :
    ContinuousOn (chen1973GammaDensityPrimitive x) (Ioi 0) := by
  let g : ℝ → ℂ := fun r =>
    (chenGammaCDF (chen1973PerronOrder x)
      (chen1973PerronScale x * Real.log (1 / r)) : ℂ)
  have hg : ContinuousOn g (Ioi 0) := by
    intro r hr
    apply ContinuousAt.continuousWithinAt
    have hrec : ContinuousAt (fun z : ℝ => 1 / z) r :=
      continuousAt_const.div continuousAt_id (ne_of_gt hr)
    have hlog : ContinuousAt (fun z : ℝ => Real.log (1 / z)) r :=
      (Real.continuousAt_log (one_div_ne_zero (ne_of_gt hr))).comp hrec
    have harg : ContinuousAt
        (fun z : ℝ => chen1973PerronScale x * Real.log (1 / z)) r :=
      hlog.const_mul _
    have hcdf : ContinuousAt (chenGammaCDF (chen1973PerronOrder x))
        (chen1973PerronScale x * Real.log (1 / r)) :=
      (hasDerivAt_chenGammaCDF (chen1973PerronOrder x)
        (chen1973PerronScale x * Real.log (1 / r))).continuousAt
    have hcomp : ContinuousAt
        (chenGammaCDF (chen1973PerronOrder x) ∘
          (fun z : ℝ => chen1973PerronScale x * Real.log (1 / z))) r :=
      ContinuousAt.comp
        (f := fun z : ℝ => chen1973PerronScale x * Real.log (1 / z))
        (g := chenGammaCDF (chen1973PerronOrder x)) hcdf harg
    exact Complex.continuous_ofReal.continuousAt.comp hcomp
  have hpiece : ContinuousOn
      (fun r : ℝ => if 1 ≤ r then (0 : ℂ) else g r) (Ioi 0) := by
    apply ContinuousOn.if
    · intro r hr
      simp only [Set.mem_inter_iff, Set.mem_Ioi] at hr
      have hfr : r ∈ frontier (Ici (1 : ℝ)) := hr.2
      have hr1 : r = 1 := by
        simpa only [frontier_Ici, Set.mem_singleton_iff] using hfr
      subst r
      simp [g]
    · exact continuousOn_const
    · exact hg.mono (by intro r hr; exact hr.1)
  apply hpiece.congr
  intro r hr
  simp only [chen1973GammaDensityPrimitive]
  have hr0 : ¬ r ≤ 0 := not_le_of_gt hr
  by_cases hr1 : 1 ≤ r <;> simp [hr0, hr1, g]

/-- Pointwise positive-argument continuity required by Mellin inversion. -/
theorem continuousAt_chen1973GammaDensityPrimitive (x r : ℝ) (hr : 0 < r) :
    ContinuousAt (chen1973GammaDensityPrimitive x) r :=
  (continuousOn_chen1973GammaDensityPrimitive x).continuousAt (Ioi_mem_nhds hr)

/-- Chen's unconditional Bromwich identity.  The Mellin transform formula,
convergence on `re s = 2`, and positive-argument continuity are all proved in
this module rather than supplied by callers. -/
theorem Chen1973BromwichIdentity (x : ℝ) (hx : 1 < x) :
    ∀ y : ℝ, 0 < y →
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
          (∫ t : ℝ, chen1973BromwichIntegrand x y t) =
        (chen1973PerronKernelFinite x y : ℂ) := by
  apply chen1973BromwichIdentity_of_mellin x hx
  · intro s hs
    exact mellin_chen1973GammaDensityPrimitive hx (by rw [hs]; norm_num)
  · exact mellinConvergent_chen1973GammaDensityPrimitive hx (by norm_num)
  · exact continuousAt_chen1973GammaDensityPrimitive x

end AnalyticNumberTheory.LargeSieve
