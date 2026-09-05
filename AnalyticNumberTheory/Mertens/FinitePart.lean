import AnalyticNumberTheory.Mertens.AbelianRemainder
import AnalyticNumberTheory.Mertens.LogChange
import AnalyticNumberTheory.Mertens.ConstantIdentity
import AnalyticNumberTheory.Mertens.GammaKernel

/-!
# The prime Dirichlet finite part

This module applies Mertens' second theorem to the exponential Abel kernel.
It identifies the finite part of the prime Dirichlet series at `s = 1` and
thereby identifies the canonical product constant with Euler's constant.
-/

namespace AnalyticNumberTheory.Mertens

open Filter Topology Real Set MeasureTheory

/-- The Mertens-II error after the logarithmic substitution `x = exp u`. -/
noncomputable def primeAbelRemainder (u : ℝ) : ℂ :=
  (primeReciprocalSum ⌊Real.exp u⌋₊ : ℂ) -
    ((Real.log u + mertensSecondConstant : ℝ) : ℂ)

theorem stronglyMeasurable_primeAbelRemainder :
    StronglyMeasurable primeAbelRemainder := by
  have hfloor : Measurable (fun u : ℝ => ⌊Real.exp u⌋₊) :=
    Real.continuous_exp.measurable.nat_floor
  have hP : Measurable (fun u : ℝ => primeReciprocalSum ⌊Real.exp u⌋₊) :=
    (measurable_of_countable primeReciprocalSum).comp hfloor
  unfold primeAbelRemainder
  fun_prop

/-- Mertens II becomes an `O(1/u)` bound after `x = exp u`. -/
theorem primeAbelRemainder_eventually_inv_bound :
    ∃ C > 0, ∀ᶠ u : ℝ in atTop, ‖primeAbelRemainder u‖ ≤ C / u := by
  obtain ⟨C, hC, hbound⟩ := mertensSecond_eventually
  refine ⟨C, hC, ?_⟩
  have hexp : Tendsto Real.exp atTop atTop := Real.tendsto_exp_atTop
  filter_upwards [hexp.eventually hbound, eventually_gt_atTop (0 : ℝ)] with u hu hu0
  rw [primeAbelRemainder, ← Complex.ofReal_sub, Complex.norm_real]
  simpa [Real.log_exp, abs_of_pos hu0] using hu

theorem integrableOn_primeAbelRemainder_norm_div_Ioc {A : ℝ} (hA : 1 ≤ A) :
    IntegrableOn (fun u : ℝ => ‖primeAbelRemainder u‖ / u) (Ioc 1 A) := by
  have hmeas : AEStronglyMeasurable
      (fun u : ℝ => ‖primeAbelRemainder u‖ / u) volume := by
    exact (stronglyMeasurable_primeAbelRemainder.norm.measurable.div
      measurable_id).aestronglyMeasurable
  apply Measure.integrableOn_of_bounded measure_Ioc_lt_top.ne hmeas
    (M := primeReciprocalSum ⌊Real.exp A⌋₊ + Real.log A +
      |mertensSecondConstant|)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
  have hu1 : 1 < u := hu.1
  have hu0 : 0 < u := zero_lt_one.trans hu1
  have huA : u ≤ A := hu.2
  have hPA : primeReciprocalSum ⌊Real.exp u⌋₊ ≤
      primeReciprocalSum ⌊Real.exp A⌋₊ :=
    primeReciprocalSum_mono (Nat.floor_mono (Real.exp_le_exp.mpr huA))
  have hlogu0 : 0 ≤ Real.log u := Real.log_nonneg hu1.le
  have hloguA : Real.log u ≤ Real.log A :=
    Real.strictMonoOn_log.monotoneOn hu0
      (lt_of_lt_of_le zero_lt_one hA) huA
  have hlogA0 : 0 ≤ Real.log A := Real.log_nonneg hA
  have hM0 : 0 ≤ primeReciprocalSum ⌊Real.exp A⌋₊ + Real.log A +
      |mertensSecondConstant| :=
    add_nonneg (add_nonneg (primeReciprocalSum_nonneg _) hlogA0) (abs_nonneg _)
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (norm_nonneg _) hu0.le)]
  calc
    ‖primeAbelRemainder u‖ / u ≤
        (primeReciprocalSum ⌊Real.exp u⌋₊ +
          |Real.log u + mertensSecondConstant|) / u := by
      apply div_le_div_of_nonneg_right _ hu0.le
      rw [primeAbelRemainder, ← Complex.ofReal_sub, Complex.norm_real]
      calc
        |primeReciprocalSum ⌊Real.exp u⌋₊ -
            (Real.log u + mertensSecondConstant)| ≤
            |primeReciprocalSum ⌊Real.exp u⌋₊| +
              |Real.log u + mertensSecondConstant| := abs_sub _ _
        _ = _ := by rw [abs_of_nonneg (primeReciprocalSum_nonneg _)]
    _ ≤ (primeReciprocalSum ⌊Real.exp A⌋₊ + Real.log A +
          |mertensSecondConstant|) / u := by
      apply div_le_div_of_nonneg_right _ hu0.le
      calc
        primeReciprocalSum ⌊Real.exp u⌋₊ +
            |Real.log u + mertensSecondConstant| ≤
            primeReciprocalSum ⌊Real.exp u⌋₊ +
              (Real.log u + |mertensSecondConstant|) := by
          gcongr
          exact (abs_add_le _ _).trans (by rw [abs_of_nonneg hlogu0])
        _ ≤ _ := by linarith
    _ ≤ primeReciprocalSum ⌊Real.exp A⌋₊ + Real.log A +
          |mertensSecondConstant| := div_le_self hM0 hu1.le

/-- The tail of the concrete Mertens-II remainder vanishes under Abel damping. -/
theorem tendsto_primeAbelRemainder_tail :
    Tendsto
      (fun ε : ℝ =>
        (ε : ℂ) * ∫ u : ℝ in Ioi 1,
          primeAbelRemainder u * (Real.exp (-(ε * u)) : ℂ))
      (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨C, _hC, hbound⟩ := primeAbelRemainder_eventually_inv_bound
  obtain ⟨A, hA⟩ := (eventually_atTop.1 hbound)
  let A' := max 1 A
  apply tendsto_mul_integral_exp_remainder_of_inv_tail
    (E := primeAbelRemainder) (a := 1) (A := A') (C := C)
  · norm_num
  · exact le_max_left _ _
  · exact stronglyMeasurable_primeAbelRemainder.aestronglyMeasurable.restrict
  · exact integrableOn_primeAbelRemainder_norm_div_Ioc (le_max_left _ _)
  · exact (stronglyMeasurable_primeAbelRemainder.norm.measurable.div
      measurable_id).aestronglyMeasurable.restrict
  · intro u hu
    exact hA u ((le_max_right 1 A).trans hu.le)

theorem integrableOn_primeAbelRemainder_norm_div_Ioi_one :
    IntegrableOn (fun u : ℝ => ‖primeAbelRemainder u‖ / u) (Ioi 1) := by
  obtain ⟨C, _hC, hbound⟩ := primeAbelRemainder_eventually_inv_bound
  obtain ⟨A, hA⟩ := (eventually_atTop.1 hbound)
  let A' := max 1 A
  apply integrableOn_norm_div_of_compact_of_inv_tail
    (E := primeAbelRemainder) (a := 1) (A := A') (C := C)
  · norm_num
  · exact le_max_left _ _
  · exact integrableOn_primeAbelRemainder_norm_div_Ioc (le_max_left _ _)
  · exact (stronglyMeasurable_primeAbelRemainder.norm.measurable.div
      measurable_id).aestronglyMeasurable.restrict
  · intro u hu
    exact hA u ((le_max_right 1 A).trans hu.le)

theorem integrableOn_primeAbelRemainder_mul_exp_tail
    (ε : ℝ) (hε : 0 < ε) :
    IntegrableOn
      (fun u : ℝ => primeAbelRemainder u *
        (Real.exp (-(ε * u)) : ℂ)) (Ioi 1) := by
  have hmajor : IntegrableOn
      (fun u : ℝ => (ε⁻¹ : ℝ) * (‖primeAbelRemainder u‖ / u)) (Ioi 1) :=
    integrableOn_primeAbelRemainder_norm_div_Ioi_one.const_mul ε⁻¹
  apply Integrable.mono' hmajor
  · exact (stronglyMeasurable_primeAbelRemainder.mul
      (Complex.continuous_ofReal.comp
        (Real.continuous_exp.comp
          (continuous_const.mul continuous_id).neg)).stronglyMeasurable)
      |>.aestronglyMeasurable.restrict
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : 0 < u := zero_lt_one.trans hu
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    have hk := mul_exp_neg_mul_le_inv hε hu0
    calc
      ‖primeAbelRemainder u‖ * Real.exp (-(ε * u)) =
          ε⁻¹ * (‖primeAbelRemainder u‖ *
            (ε * Real.exp (-(ε * u)))) := by field_simp
      _ ≤ ε⁻¹ * (‖primeAbelRemainder u‖ * u⁻¹) := by gcongr
      _ = ε⁻¹ * (‖primeAbelRemainder u‖ / u) := by rw [div_eq_mul_inv]

/-- The logarithmic singularity of the remainder is integrable near zero. -/
theorem integrableOn_primeAbelRemainder_Ioc_zero_one :
    IntegrableOn primeAbelRemainder (Ioc 0 1) := by
  have hPmeas : AEStronglyMeasurable
      (fun u : ℝ => (primeReciprocalSum ⌊Real.exp u⌋₊ : ℂ)) volume := by
    have hfloor : Measurable (fun u : ℝ => ⌊Real.exp u⌋₊) :=
      Real.continuous_exp.measurable.nat_floor
    exact (Complex.continuous_ofReal.measurable.comp
      ((measurable_of_countable primeReciprocalSum).comp hfloor)).aestronglyMeasurable
  have hP : IntegrableOn
      (fun u : ℝ => (primeReciprocalSum ⌊Real.exp u⌋₊ : ℂ)) (Ioc 0 1) := by
    apply Measure.integrableOn_of_bounded measure_Ioc_lt_top.ne hPmeas
      (M := primeReciprocalSum ⌊Real.exp 1⌋₊)
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (primeReciprocalSum_nonneg _)]
    exact primeReciprocalSum_mono
      (Nat.floor_mono (Real.exp_le_exp.mpr hu.2))
  have hlogWeighted : IntegrableOn
      (fun u : ℝ => (Real.log u : ℂ) * (Real.exp (-u) : ℂ)) (Ioc 0 1) :=
    integrableOn_complex_log_mul_exp_neg.mono_set Ioc_subset_Ioi_self
  have hlog : IntegrableOn (fun u : ℝ => (Real.log u : ℂ)) (Ioc 0 1) := by
    have hmul := hlogWeighted.mul_continuousOn_of_subset
      (Complex.continuous_ofReal.comp Real.continuous_exp).continuousOn
      measurableSet_Ioc isCompact_Icc Ioc_subset_Icc_self
    refine hmul.congr_fun ?_ measurableSet_Ioc
    intro u hu
    change (Real.log u : ℂ) * (Real.exp (-u) : ℂ) *
      (Real.exp u : ℂ) = (Real.log u : ℂ)
    rw [mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
    simp
  have hconst : IntegrableOn
      (fun _ : ℝ => (mertensSecondConstant : ℂ)) (Ioc 0 1) :=
    integrableOn_const measure_Ioc_lt_top.ne
  have ht := hP.sub (hlog.add hconst)
  refine ht.congr_fun ?_ measurableSet_Ioc
  intro u hu
  unfold primeAbelRemainder
  simp only [Pi.sub_apply, Pi.add_apply]
  push_cast
  ring

theorem tendsto_primeAbelRemainder_initial :
    Tendsto
      (fun ε : ℝ =>
        (ε : ℂ) * ∫ u : ℝ in Ioc 0 1,
          primeAbelRemainder u * (Real.exp (-(ε * u)) : ℂ))
      (𝓝[>] 0) (𝓝 0) := by
  let μ := volume.restrict (Ioc (0 : ℝ) 1)
  let F : ℝ → ℝ → ℂ := fun ε u =>
    primeAbelRemainder u * (Real.exp (-(ε * u)) : ℂ)
  have hlim : ∀ᵐ u ∂μ, Tendsto (fun ε => F ε u)
      (𝓝[>] 0) (𝓝 (primeAbelRemainder u)) := by
    refine ae_of_all _ fun u => ?_
    have hcont : ContinuousAt (fun ε : ℝ => F ε u) 0 := by
      dsimp only [F]
      fun_prop
    simpa [F] using hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hmeas : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      AEStronglyMeasurable (F ε) μ := by
    filter_upwards with ε
    exact (stronglyMeasurable_primeAbelRemainder.mul
      (Complex.continuous_ofReal.comp
        (Real.continuous_exp.comp
          (continuous_const.mul continuous_id).neg)).stronglyMeasurable)
      |>.aestronglyMeasurable
  have hbound : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ∀ᵐ u ∂μ, ‖F ε u‖ ≤ ‖primeAbelRemainder u‖ := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    have hε0 : 0 < ε := hε
    have hu0 : 0 < u := hu.1
    dsimp only [F]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    exact mul_le_of_le_one_right (norm_nonneg _)
      (Real.exp_le_one_iff.mpr
        (neg_nonpos.mpr (mul_nonneg hε0.le hu0.le)))
  have hint : Integrable (fun u => ‖primeAbelRemainder u‖) μ :=
    integrableOn_primeAbelRemainder_Ioc_zero_one.norm
  have ht : Tendsto (fun ε => ∫ u, F ε u ∂μ) (𝓝[>] 0)
      (𝓝 (∫ u, primeAbelRemainder u ∂μ)) :=
    tendsto_integral_filter_of_dominated_convergence
      (F := F) (f := primeAbelRemainder) _ hmeas hbound hint hlim
  have hε : Tendsto (fun ε : ℝ => (ε : ℂ)) (𝓝[>] 0) (𝓝 0) := by
    exact Complex.continuous_ofReal.continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
  simpa [μ, F] using hε.mul ht

theorem integrableOn_primeAbelRemainder_mul_exp_initial
    (ε : ℝ) :
    IntegrableOn
      (fun u : ℝ => primeAbelRemainder u *
        (Real.exp (-(ε * u)) : ℂ)) (Ioc 0 1) := by
  exact integrableOn_primeAbelRemainder_Ioc_zero_one.mul_continuousOn_of_subset
    (Complex.continuous_ofReal.comp
      (Real.continuous_exp.comp
        (continuous_const.mul continuous_id).neg)).continuousOn
    measurableSet_Ioc isCompact_Icc Ioc_subset_Icc_self

/-- The full Mertens-II remainder vanishes under Abel damping. -/
theorem tendsto_primeAbelRemainder_full :
    Tendsto
      (fun ε : ℝ =>
        (ε : ℂ) * ∫ u : ℝ in Ioi 0,
          primeAbelRemainder u * (Real.exp (-(ε * u)) : ℂ))
      (𝓝[>] 0) (𝓝 0) := by
  have hsum := tendsto_primeAbelRemainder_initial.add
    tendsto_primeAbelRemainder_tail
  have hsum' : Tendsto
      (fun ε : ℝ =>
        ((ε : ℂ) * ∫ u : ℝ in Ioc 0 1,
          primeAbelRemainder u * (Real.exp (-(ε * u)) : ℂ)) +
        ((ε : ℂ) * ∫ u : ℝ in Ioi 1,
          primeAbelRemainder u * (Real.exp (-(ε * u)) : ℂ)))
      (𝓝[>] 0) (𝓝 0) := by simpa using hsum
  apply (tendsto_congr' ?_).mpr hsum'
  filter_upwards [eventually_mem_nhdsWithin] with ε hε
  have hε0 : 0 < ε := hε
  rw [← mul_add]
  congr 1
  rw [← setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
    (integrableOn_primeAbelRemainder_mul_exp_initial ε)
    (integrableOn_primeAbelRemainder_mul_exp_tail ε hε0)]
  rw [Ioc_union_Ioi_eq_Ioi zero_le_one]

theorem integrableOn_primeAbelRemainder_mul_exp_full
    (ε : ℝ) (hε : 0 < ε) :
    IntegrableOn
      (fun u : ℝ => primeAbelRemainder u *
        (Real.exp (-(ε * u)) : ℂ)) (Ioi 0) := by
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
  exact (integrableOn_primeAbelRemainder_mul_exp_initial ε).union
    (integrableOn_primeAbelRemainder_mul_exp_tail ε hε)

/-- Exact decomposition of the prime Abel integral into Gamma, constant, and
vanishing-remainder terms. -/
theorem primeAbel_integral_finitePart_identity
    (ε : ℝ) (hε : 0 < ε) :
    (ε : ℂ) *
          (∫ u : ℝ in Ioi 0,
            (primeReciprocalSum ⌊Real.exp u⌋₊ : ℂ) *
              (Real.exp (-(ε * u)) : ℂ)) +
        (Real.log ε : ℂ) =
      (-Real.eulerMascheroniConstant : ℂ) +
        (mertensSecondConstant : ℂ) +
          (ε : ℂ) * ∫ u : ℝ in Ioi 0,
            primeAbelRemainder u * (Real.exp (-(ε * u)) : ℂ) := by
  let K : ℝ → ℂ := fun u => (Real.exp (-(ε * u)) : ℂ)
  have hlog : IntegrableOn
      (fun u : ℝ => (Real.log u : ℂ) * K u) (Ioi 0) := by
    simpa [K] using integrableOn_complex_log_mul_exp_neg_mul ε hε
  have hexp : IntegrableOn K (Ioi 0) := by
    simpa [K] using integrableOn_complex_exp_neg_mul ε hε
  have hconst : IntegrableOn
      (fun u : ℝ => (mertensSecondConstant : ℂ) * K u) (Ioi 0) :=
    hexp.const_mul (mertensSecondConstant : ℂ)
  have hrem : IntegrableOn
      (fun u : ℝ => primeAbelRemainder u * K u) (Ioi 0) := by
    simpa [K] using integrableOn_primeAbelRemainder_mul_exp_full ε hε
  have hdecomp :
      (∫ u : ℝ in Ioi 0,
        (primeReciprocalSum ⌊Real.exp u⌋₊ : ℂ) * K u) =
        (∫ u : ℝ in Ioi 0, (Real.log u : ℂ) * K u) +
          (∫ u : ℝ in Ioi 0, (mertensSecondConstant : ℂ) * K u) +
            ∫ u : ℝ in Ioi 0, primeAbelRemainder u * K u := by
    have hfun : (fun u : ℝ =>
        (primeReciprocalSum ⌊Real.exp u⌋₊ : ℂ) * K u) =
        (fun u : ℝ =>
          ((Real.log u : ℂ) * K u +
            (mertensSecondConstant : ℂ) * K u) +
              primeAbelRemainder u * K u) := by
      funext u
      unfold primeAbelRemainder
      push_cast
      ring
    rw [hfun]
    change (∫ u : ℝ in Ioi 0,
        ((Real.log u : ℂ) * K u +
          (mertensSecondConstant : ℂ) * K u) +
            primeAbelRemainder u * K u) = _
    have hadd₁ : (∫ u : ℝ in Ioi 0,
        ((Real.log u : ℂ) * K u +
          (mertensSecondConstant : ℂ) * K u) +
            primeAbelRemainder u * K u) =
        (∫ u : ℝ in Ioi 0,
          (Real.log u : ℂ) * K u +
            (mertensSecondConstant : ℂ) * K u) +
          ∫ u : ℝ in Ioi 0, primeAbelRemainder u * K u := by
      exact integral_add (hlog.add hconst) hrem
    have hadd₂ : (∫ u : ℝ in Ioi 0,
        (Real.log u : ℂ) * K u +
          (mertensSecondConstant : ℂ) * K u) =
        (∫ u : ℝ in Ioi 0, (Real.log u : ℂ) * K u) +
          ∫ u : ℝ in Ioi 0, (mertensSecondConstant : ℂ) * K u := by
      exact integral_add hlog hconst
    rw [hadd₁, hadd₂]
  rw [hdecomp, mul_add, mul_add]
  rw [show (∫ u : ℝ in Ioi 0, (mertensSecondConstant : ℂ) * K u) =
      (mertensSecondConstant : ℂ) * ∫ u : ℝ in Ioi 0, K u by
        rw [← integral_const_mul]]
  have hmass : (ε : ℂ) * (∫ u : ℝ in Ioi 0, K u) = 1 := by
    simpa [K] using complex_scaled_integral_exp_eq_one ε hε
  have hgamma : (ε : ℂ) *
        (∫ u : ℝ in Ioi 0, (Real.log u : ℂ) * K u) +
      (Real.log ε : ℂ) = (-Real.eulerMascheroniConstant : ℂ) := by
    simpa [K] using
      complex_scaled_integral_log_exp_eq_neg_eulerMascheroni ε hε
  have hB : (ε : ℂ) * (mertensSecondConstant : ℂ) *
      (∫ u : ℝ in Ioi 0, K u) = (mertensSecondConstant : ℂ) := by
    calc
      _ = (mertensSecondConstant : ℂ) *
          ((ε : ℂ) * ∫ u : ℝ in Ioi 0, K u) := by ring
      _ = _ := by rw [hmass, mul_one]
  have hB' : (ε : ℂ) * ((mertensSecondConstant : ℂ) *
      (∫ u : ℝ in Ioi 0, K u)) = (mertensSecondConstant : ℂ) := by
    rw [← mul_assoc, hB]
  rw [hB']
  calc
    ((ε : ℂ) * (∫ u : ℝ in Ioi 0, (Real.log u : ℂ) * K u) +
          (mertensSecondConstant : ℂ) +
            (ε : ℂ) * ∫ u : ℝ in Ioi 0,
              primeAbelRemainder u * K u) + (Real.log ε : ℂ) =
        ((ε : ℂ) * (∫ u : ℝ in Ioi 0, (Real.log u : ℂ) * K u) +
          (Real.log ε : ℂ)) + (mertensSecondConstant : ℂ) +
            (ε : ℂ) * ∫ u : ℝ in Ioi 0,
              primeAbelRemainder u * K u := by ring
    _ = _ := by rw [hgamma]

/-- Abelian finite part of the prime Dirichlet series at `s = 1`. -/
theorem tendsto_primeDirichlet_finitePart :
    Tendsto
      (fun ε : ℝ =>
        (∑' p : Nat.Primes, (p : ℝ) ^ (-(1 + ε))) + Real.log ε)
      (𝓝[>] 0)
      (𝓝 (mertensSecondConstant - Real.eulerMascheroniConstant)) := by
  have hrem := tendsto_primeAbelRemainder_full
  have hrhs : Tendsto
      (fun ε : ℝ =>
        (-Real.eulerMascheroniConstant : ℂ) +
          (mertensSecondConstant : ℂ) +
            (ε : ℂ) * ∫ u : ℝ in Ioi 0,
              primeAbelRemainder u * (Real.exp (-(ε * u)) : ℂ))
      (𝓝[>] 0)
      (𝓝 ((mertensSecondConstant - Real.eulerMascheroniConstant : ℝ) : ℂ)) := by
    convert (tendsto_const_nhds.add hrem) using 1 <;> push_cast <;> ring
  have heq : (fun ε : ℝ =>
      (↑((∑' p : Nat.Primes, (p : ℝ) ^ (-(1 + ε))) + Real.log ε) : ℂ))
      =ᶠ[𝓝[>] 0]
      (fun ε : ℝ =>
        (-Real.eulerMascheroniConstant : ℂ) +
          (mertensSecondConstant : ℂ) +
            (ε : ℂ) * ∫ u : ℝ in Ioi 0,
              primeAbelRemainder u * (Real.exp (-(ε * u)) : ℂ)) := by
    filter_upwards [eventually_mem_nhdsWithin] with ε hε
    have hε0 : 0 < ε := hε
    rw [Complex.ofReal_add,
      realPrimeDirichletSum_eq_mul_integral_of_pos ε hε0,
      primeAbel_integral_log_change ε hε0]
    exact primeAbel_integral_finitePart_identity ε hε0
  have hcomplex : Tendsto
      (fun ε : ℝ =>
        (↑((∑' p : Nat.Primes, (p : ℝ) ^ (-(1 + ε))) + Real.log ε) : ℂ))
      (𝓝[>] 0)
      (𝓝 ((mertensSecondConstant - Real.eulerMascheroniConstant : ℝ) : ℂ)) :=
    (tendsto_congr' heq).mpr hrhs
  have hre := Complex.continuous_re.continuousAt.tendsto.comp hcomplex
  apply (tendsto_congr' ?_).mpr hre
  filter_upwards with ε
  exact (Complex.ofReal_re
    ((∑' p : Nat.Primes, (p : ℝ) ^ (-(1 + ε))) + Real.log ε)).symm

/-- The canonical Mertens product constant is the Euler--Mascheroni constant. -/
theorem mertensConstant_eq_eulerMascheroni :
    mertensSecondConstant + logarithmicCorrectionLimit =
      Real.eulerMascheroniConstant :=
  mertensConstant_eq_eulerMascheroni_of_primeFinitePart
    tendsto_primeDirichlet_finitePart

end AnalyticNumberTheory.Mertens
