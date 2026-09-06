import MathlibNt.SieveTheory.Selberg.Liu.LiuSelbergOptimalWeights
import MathlibNt.SieveTheory.Selberg.Liu.LiuSelbergPrimeDivisorGrowth

/-!
# Liu's Selberg denominator asymptotic

The moving source cutoff has the expected logarithmic scale.  Combining this
with the uniform harmonic remainder and the triangular Euler error gives the
sharp normalized asymptotic for Liu's finite Selberg denominator, and hence the
optimized coefficient input.
-/

open scoped BigOperators Topology

namespace MathlibNt.SieveTheory.LiuWeight

open Filter Finset

/-- Flooring a positive real power does not change its logarithmic scale. -/
theorem tendsto_log_floor_rpow_div_log (beta : ℝ) (hbeta : 0 < beta) :
    Tendsto (fun N : ℕ =>
      Real.log (Nat.floor ((N : ℝ) ^ beta)) / Real.log (N : ℝ))
      atTop (𝓝 beta) := by
  have hpow : Tendsto (fun N : ℕ => (N : ℝ) ^ beta) atTop atTop :=
    (tendsto_rpow_atTop hbeta).comp tendsto_natCast_atTop_atTop
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlower :
      Tendsto (fun N : ℕ => beta - Real.log 2 / Real.log (N : ℝ))
        atTop (𝓝 beta) := by
    simpa using tendsto_const_nhds.sub (tendsto_const_nhds.div_atTop hlog)
  -- Use the same floor bounds and positivity facts for both sides of the squeeze.
  have hbounds : ∀ᶠ N : ℕ in atTop,
      beta - Real.log 2 / Real.log (N : ℝ) ≤
          Real.log (Nat.floor ((N : ℝ) ^ beta)) / Real.log (N : ℝ) ∧
        Real.log (Nat.floor ((N : ℝ) ^ beta)) / Real.log (N : ℝ) ≤ beta := by
    filter_upwards [hpow.eventually (eventually_ge_atTop (2 : ℝ)),
      hlog.eventually (eventually_gt_atTop (0 : ℝ))] with N hNpow hlogN
    have hNne : N ≠ 0 := by
      intro h
      simp [h, Real.zero_rpow hbeta.ne'] at hNpow
      norm_num at hNpow
    have hNpos : (0 : ℝ) < N := by
      exact_mod_cast Nat.pos_of_ne_zero hNne
    have hfloor :
        (N : ℝ) ^ beta / 2 ≤ (Nat.floor ((N : ℝ) ^ beta) : ℝ) := by
      have hhalf : (N : ℝ) ^ beta / 2 ≤ (N : ℝ) ^ beta - 1 := by
        linarith
      exact hhalf.trans (Nat.sub_one_lt_floor ((N : ℝ) ^ beta)).le
    have hfloorpos : (0 : ℝ) < Nat.floor ((N : ℝ) ^ beta) :=
      lt_of_lt_of_le
        (div_pos (lt_of_lt_of_le (by norm_num) hNpow) (by norm_num)) hfloor
    constructor
    · have hloglower := Real.strictMonoOn_log.monotoneOn
        (div_pos (Real.rpow_pos_of_pos hNpos beta) (by norm_num))
        hfloorpos hfloor
      rw [Real.log_div (Real.rpow_pos_of_pos hNpos beta).ne' (by norm_num),
        Real.log_rpow hNpos] at hloglower
      apply (le_div_iff₀ hlogN).2
      calc
        (beta - Real.log 2 / Real.log (N : ℝ)) * Real.log (N : ℝ) =
            beta * Real.log (N : ℝ) - Real.log 2 := by
              field_simp [hlogN.ne']
        _ ≤ Real.log (Nat.floor ((N : ℝ) ^ beta)) := hloglower
    · have hlogupper := Real.strictMonoOn_log.monotoneOn hfloorpos
        (Real.rpow_pos_of_pos hNpos beta)
        (Nat.floor_le (Real.rpow_nonneg hNpos.le beta))
      rw [Real.log_rpow hNpos] at hlogupper
      exact (div_le_iff₀ hlogN).2 hlogupper
  exact hlower.squeeze' tendsto_const_nhds
    (hbounds.mono fun _ h => h.1) (hbounds.mono fun _ h => h.2)

/-- The paper's moving cutoff has logarithmic scale `1/4 - epsilon/2`. -/
theorem tendsto_log_paperQSourceCutoff_div_log (epsilon : ℝ)
    (hbeta : 0 < 1 / 4 - epsilon / 2) :
    Tendsto (fun N : ℕ =>
      Real.log (paperQSourceCutoff N epsilon) / Real.log (N : ℝ))
      atTop (𝓝 (1 / 4 - epsilon / 2)) := by
  simpa [paperQSourceCutoff] using
    tendsto_log_floor_rpow_div_log (1 / 4 - epsilon / 2) hbeta

/-- Along the even integers, Liu's denominator has the sharp normalized limit. -/
theorem tendsto_liuSelbergDenominator_normalized_even (epsilon : ℝ)
    (hbeta : 0 < 1 / 4 - epsilon / 2) :
    Tendsto (fun N : ℕ =>
      liuSelbergDenominator N epsilon *
          SingularSeries.liuSingularSeries N / Real.log (N : ℝ))
      (atTop ⊓ 𝓟 {N : ℕ | Even N}) (𝓝 ((1 / 4 - epsilon / 2) / 2)) := by
  have hcut := tendsto_log_paperQSourceCutoff_div_log epsilon hbeta
  have hmain :
      Tendsto (fun N : ℕ =>
        (Real.log (paperQSourceCutoff N epsilon) / Real.log (N : ℝ)) / 2)
        (atTop ⊓ 𝓟 {N : ℕ | Even N}) (𝓝 ((1 / 4 - epsilon / 2) / 2)) :=
    (hcut.div_const 2).mono_left inf_le_left
  have hpow :
      Tendsto (fun N : ℕ => (N : ℝ) ^ (1 / 4 - epsilon / 2)) atTop atTop :=
    (tendsto_rpow_atTop hbeta).comp tendsto_natCast_atTop_atTop
  have hdiff :
      Tendsto (fun N : ℕ =>
        (liuSelbergDenominator N epsilon -
            Real.log (paperQSourceCutoff N epsilon) /
              (2 * SingularSeries.liuSingularSeries N)) *
          SingularSeries.liuSingularSeries N / Real.log (N : ℝ))
        (atTop ⊓ 𝓟 {N : ℕ | Even N}) (𝓝 0) := by
    apply squeeze_zero_norm' _ tendsto_liuSelbergEulerError_even
    rw [eventually_inf_principal]
    filter_upwards [eventually_ge_atTop (2 : ℕ),
      hpow.eventually (eventually_ge_atTop (2 : ℝ))] with N hN hNpow
    intro hNeven
    have hR : 2 ≤ paperQSourceCutoff N epsilon := by
      unfold paperQSourceCutoff
      simpa using Nat.floor_mono hNpow
    have hseries : 0 < SingularSeries.liuSingularSeries N :=
      SingularSeries.liuSingularSeries_pos N
    have hlog : 0 < Real.log (N : ℝ) :=
      Real.log_pos (by exact_mod_cast hN)
    have habs :
        |liuSelbergDenominator N epsilon -
            Real.log (paperQSourceCutoff N epsilon) /
              (2 * SingularSeries.liuSingularSeries N)| ≤
          2 * liuSelbergAbsoluteLogMoment N + liuSelbergAbsoluteMass N := by
      rw [liuSelbergDenominator_eq_sum_Icc hNeven (by omega)]
      exact
        abs_liuSelbergArithmetic_sum_Icc_sub_log_main_le_uniform_reduction
          hNeven (by omega) hR
    rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos hseries,
      abs_of_pos hlog]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right habs hseries.le) hlog.le
  have hsum := hmain.add hdiff
  simpa only [add_zero] using hsum.congr' (by
    filter_upwards [(eventually_ge_atTop (2 : ℕ)).filter_mono inf_le_left]
      with N hN
    have hseries : SingularSeries.liuSingularSeries N ≠ 0 :=
      (SingularSeries.liuSingularSeries_pos N).ne'
    have hlog : Real.log (N : ℝ) ≠ 0 :=
      (Real.log_pos (by exact_mod_cast hN)).ne'
    field_simp
    ring)

/-- A strict epsilon margin converts the normalized limit into the required
eventual lower bound. -/
theorem liuSelbergDenominatorLowerBound_of_lt_margin
    {delta epsilon : ℝ} (hdelta : 0 < delta)
    (hmargin : epsilon < delta / (2 * (8 + delta))) :
    LiuSelbergDenominatorLowerBound delta epsilon := by
  have hscale : 0 < 8 + delta := by
    linarith
  have hdenom : 0 < 2 * (8 + delta) :=
    mul_pos (by norm_num) hscale
  have hmargin' : epsilon * (2 * (8 + delta)) < delta :=
    (lt_div_iff₀ hdenom).mp hmargin
  have hfrac : delta / (2 * (8 + delta)) < (1 / 2 : ℝ) := by
    apply (div_lt_iff₀ hdenom).2
    nlinarith
  have hbeta : 0 < 1 / 4 - epsilon / 2 := by
    nlinarith [hmargin.trans hfrac]
  have hlimit : 1 / (8 + delta) < (1 / 4 - epsilon / 2) / 2 := by
    field_simp [hscale.ne']
    nlinarith [hmargin']
  have hasym :=
    (tendsto_liuSelbergDenominator_normalized_even epsilon hbeta).eventually
      (Ioi_mem_nhds hlimit)
  rw [eventually_inf_principal] at hasym
  filter_upwards [hasym] with N hN
  intro hNtwo hNeven _hR
  have hA := hN hNeven
  have hlog : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast hNtwo)
  have hseries : 0 < SingularSeries.liuSingularSeries N :=
    SingularSeries.liuSingularSeries_pos N
  calc
    Real.log (N : ℝ) /
          ((8 + delta) * SingularSeries.liuSingularSeries N) =
        (1 / (8 + delta)) * Real.log (N : ℝ) /
          SingularSeries.liuSingularSeries N := by
            field_simp
    _ ≤ (liuSelbergDenominator N epsilon *
          SingularSeries.liuSingularSeries N / Real.log (N : ℝ)) *
            Real.log (N : ℝ) / SingularSeries.liuSingularSeries N := by
      gcongr
    _ = liuSelbergDenominator N epsilon := by
      field_simp

/-- Every positive loss admits a positive epsilon interval on which the sharp
Selberg denominator lower bound holds. -/
theorem exists_liuSelbergDenominatorLowerBound :
    ∀ delta > 0, ∃ epsilon0 > 0,
      ∀ epsilon, 0 < epsilon → epsilon ≤ epsilon0 →
        LiuSelbergDenominatorLowerBound delta epsilon := by
  intro delta hdelta
  let epsilon0 := delta / (4 * (8 + delta))
  have hscale : 0 < 8 + delta := by
    linarith
  have hepsilon0 : 0 < epsilon0 := by
    dsimp [epsilon0]
    positivity
  refine ⟨epsilon0, hepsilon0, ?_⟩
  intro epsilon _hepsilon hepsilon_le
  apply liuSelbergDenominatorLowerBound_of_lt_margin hdelta
  exact hepsilon_le.trans_lt (by
    dsimp [epsilon0]
    apply
      (div_lt_div_iff_of_pos_left hdelta (by positivity) (by positivity)).2
    nlinarith)

/-- Liu's optimized Selberg coefficient input follows from the proved
denominator lower bound; the definition itself remains unchanged. -/
theorem liuOptimizedSelbergCoefficientInput :
    LegacySelberg.LiuOptimizedSelbergCoefficientInput :=
  LegacySelberg.LiuOptimizedSelbergCoefficientInput.of_denominatorLowerBound
    exists_liuSelbergDenominatorLowerBound

end MathlibNt.SieveTheory.LiuWeight
