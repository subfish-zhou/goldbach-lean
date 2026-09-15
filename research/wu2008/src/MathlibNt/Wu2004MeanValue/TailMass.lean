import MathlibNt.Wu2004MeanValue.TailMassModel

/-!
# Sharp one-sided normalization of the manuscript tail mass

Source: frozen manuscript, equation (tail-mass), lines 199--209.
The conclusion is the requested epsilon form, not an asserted second-order
expansion. All parameters, including `c` and `eta`, are fixed before the
threshold. The continuous-test Mertens limit is used only on a compact
subinterval of `(0,1)`.
-/

namespace Wu2004MeanValue

open Filter
open scoped Topology

theorem tailKernel_continuousOn {α β : ℝ} (hα : 0 < α) (hβ : β < 1) :
    ContinuousOn (fun u : ℝ => 1 / (u * (1 - u))) (Set.Icc α β) := by
  apply continuousOn_const.div
    (continuousOn_id.mul (continuousOn_const.sub continuousOn_id))
  intro u hu
  change u * (1 - u) ≠ 0
  exact mul_ne_zero (ne_of_gt (hα.trans_le hu.1)) (by linarith [hu.2])

theorem tailIntegral_nonneg {α : ℝ} (hα : 0 < α) (hαh : α ≤ 1 / 2) :
    0 ≤ tailIntegral α := by
  apply intervalIntegral.integral_nonneg hαh
  intro u hu
  exact one_div_nonneg.mpr
    (mul_nonneg (hα.le.trans hu.1) (by linarith [hu.2]))

/-- Moving the lower exponent a short distance left changes the integral
by at most the length times `4/tau`, provided it stays above `tau/2`. -/
theorem tailIntegral_lower_shift {α τ : ℝ} (hτ : 0 < τ)
    (hτh : τ < 1 / 2) (hα : τ / 2 ≤ α) (hατ : α ≤ τ) :
    tailIntegral α ≤ tailIntegral τ + (4 / τ) * (τ - α) := by
  have hα0 : 0 < α := by linarith
  have hi := (tailKernel_continuousOn hα0 (by linarith : τ < 1)).intervalIntegrable_of_Icc
    (μ := MeasureTheory.volume) hατ
  have hj := (tailKernel_continuousOn hτ (by norm_num : (1 / 2 : ℝ) < 1)).intervalIntegrable_of_Icc
    (μ := MeasureTheory.volume) hτh.le
  have heq := intervalIntegral.integral_add_adjacent_intervals hi hj
  have hbound : (∫ u in α..τ, 1 / (u * (1 - u))) ≤ (4 / τ) * (τ - α) := by
    calc
      (∫ u in α..τ, 1 / (u * (1 - u))) ≤ ∫ _u in α..τ, 4 / τ := by
        apply intervalIntegral.integral_mono_on hατ hi intervalIntegrable_const
        intro u hu
        have hu0 : 0 < u := hα0.trans_le hu.1
        have hu1 : 0 < 1 - u := by linarith [hu.2]
        have hp : τ / 4 ≤ u * (1 - u) := by
          nlinarith [mul_le_mul (show τ / 2 ≤ u by linarith [hu.1])
            (show (1 / 2 : ℝ) ≤ 1 - u by linarith [hu.2])
            (by norm_num : (0 : ℝ) ≤ 1 / 2) hu0.le]
        apply (div_le_div_iff₀ (mul_pos hu0 hu1) hτ).mpr
        nlinarith
      _ = (4 / τ) * (τ - α) := by
        simp only [intervalIntegral.integral_const, smul_eq_mul]
        ring
  unfold tailIntegral
  linarith

theorem exists_tailIntegral_lower_approx {τ : ℝ} (hτ : 0 < τ)
    (hτh : τ < 1 / 2) (ε : ℝ) (hε : 0 < ε) :
    ∃ α : ℝ, 0 < α ∧ α < τ ∧ tailIntegral α < tailIntegral τ + ε := by
  let d := min (τ / 2) (ε * τ / 8)
  have hd : 0 < d := lt_min (by positivity) (by positivity)
  have hdτ : d ≤ τ / 2 := min_le_left _ _
  have hdε : d ≤ ε * τ / 8 := min_le_right _ _
  refine ⟨τ - d, by linarith, by linarith, ?_⟩
  have hb := tailIntegral_lower_shift hτ hτh
    (show τ / 2 ≤ τ - d by linarith) (show τ - d ≤ τ by linarith)
  have hpay : (4 / τ) * (τ - (τ - d)) ≤ ε / 2 := by
    have heq : (4 / τ) * (τ - (τ - d)) = (4 * d) / τ := by ring
    rw [heq, div_le_iff₀ hτ]
    linarith
  linarith

/-- The literal tail mass, with its coprimality filter, fixed multiplicative
lower cutoff, and both true-li endpoints, has the manuscript's sharp
one-sided leading constant. -/
theorem tailMass_sharp_upper (c τ η : ℝ) (hc : 0 < c)
    (hτ : 1 / 3 < τ) (hτh : τ < 1 / 2)
    (hη : 0 < η) (hη1 : η < 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      0 ≤ tailMass N c τ η ∧
      tailMass N c τ η ≤
        ((∫ u in τ..(1 / 2 : ℝ), 1 / (u * (1 - u))) + ε) *
          ((N : ℝ) / Real.log N) := by
  have hτ0 : 0 < τ := by linarith
  obtain ⟨α, hα0, hατ, hclose⟩ := exists_tailIntegral_lower_approx hτ0 hτh ε hε
  let J := tailIntegral α
  let K := tailIntegral τ + ε
  have hJ : 0 ≤ J := tailIntegral_nonneg hα0 (hατ.trans hτh).le
  have hJK : J < K := hclose
  let δ := min 1 ((K - J) / (2 * (J + 2)))
  have hδ : 0 < δ := lt_min zero_lt_one (by positivity)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδp : δ * (2 * (J + 2)) ≤ K - J :=
    (le_div_iff₀ (by positivity : 0 < 2 * (J + 2))).mp (min_le_right _ _)
  have hproduct : (1 + δ) * (J + δ) ≤ K := by
    nlinarith [mul_nonneg hδ.le (sub_nonneg.mpr hδ1)]
  have hmodel : ∀ᶠ N : ℕ in atTop, tailPrimeModel N α ≤ J + δ :=
    ((tendsto_tailPrimeModel hα0 (hατ.trans hτh)).eventually
      (eventually_lt_nhds (show tailIntegral α < J + δ by dsimp [J]; linarith))).mono
      (fun _ h => h.le)
  have hmass := eventually_tailMass_le_model c τ η α δ hc hη hη1.le hατ hδ
  have hdom : ∀ᶠ N : ℕ in atTop, (2 / η) ^ 2 ≤ (N : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop _)
  apply eventually_atTop.mp
  filter_upwards [hmodel, hmass, hdom, eventually_ge_atTop (2 : ℕ)]
    with N hNm hNb hNd hN2
  have hN1 : 1 < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
  have hscale : 0 ≤ (N : ℝ) / Real.log N :=
    div_nonneg (Nat.cast_nonneg N) (Real.log_pos hN1).le
  refine ⟨tailMass_nonneg hη hη1.le hNd, ?_⟩
  calc
    tailMass N c τ η ≤ (1 + δ) * ((N : ℝ) / Real.log N) * tailPrimeModel N α := hNb
    _ ≤ (1 + δ) * ((N : ℝ) / Real.log N) * (J + δ) :=
      mul_le_mul_of_nonneg_left hNm (mul_nonneg (by linarith) hscale)
    _ = ((1 + δ) * (J + δ)) * ((N : ℝ) / Real.log N) := by ring
    _ ≤ K * ((N : ℝ) / Real.log N) := mul_le_mul_of_nonneg_right hproduct hscale
    _ = _ := rfl

end Wu2004MeanValue
