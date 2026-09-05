import MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLTwistedSmoothedPerron

open Set Function Filter Complex Real MeasureTheory
open ArithmeticFunction (vonMangoldt)

namespace DirichletCharacter

variable {q : ℕ} [NeZero q]

local notation "𝓜" => mellin
local notation "Λ" => ArithmeticFunction.vonMangoldt

set_option backward.isDefEq.respectTransparency false in
/-- On every standard right Perron line, the twisted smoothed Perron integrand
is integrable.  The proof uses the absolutely convergent von Mangoldt
Dirichlet-series majorant and the integrability of the Mellin smoothing factor. -/
theorem twistedSmoothedPerronIntegrand_integrable_right
    (χ : DirichletCharacter ℂ q) {ν : ℝ → ℝ}
    (diffν : ContDiff ℝ 1 ν)
    (νpos : ∀ x > 0, 0 ≤ ν x)
    (suppν : support ν ⊆ Icc (1 / 2) 2)
    (mass_one : ∫ x in Ioi (0 : ℝ), ν x / x = 1)
    {X : ℝ} (X_pos : 0 < X) {ε : ℝ} (εpos : 0 < ε) (ε_lt_one : ε < 1)
    {σ : ℝ} (σ_gt : 1 < σ) (σ_le : σ ≤ 2) :
    Integrable (fun t : ℝ =>
      twistedSmoothedPerronIntegrand χ ν ε X (σ + t * I)) := by
  let term : ℕ → ℝ → ℂ := fun n t =>
    twistedVonMangoldtCoeff χ n / (n : ℂ) ^ (σ + t * I) *
      𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) (σ + t * I) *
        (X : ℂ) ^ (σ + t * I)
  have abs_two : ∀ t : ℝ, ∀ n : ℕ,
      ‖(n : ℂ) ^ ((σ : ℂ) + t * I)‖₊ = n ^ σ := by
    intro t n
    simp_rw [← norm_toNNReal]
    rw [norm_natCast_cpow_of_re_ne_zero _ (by
      simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im,
        mul_one, sub_self, add_zero, ne_eq]
      linarith)]
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im,
      mul_one, sub_self, add_zero,
      Real.toNNReal_of_nonneg <| rpow_nonneg (y := σ) (x := n) (by linarith)]
    norm_cast
  have cont_mellin_smooth : Continuous fun a : ℝ ↦
      𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) (σ + a * I) := by
    rw [← continuousOn_univ]
    refine ContinuousOn.comp' ?_ ?_ ?_ (t := {z : ℂ | 0 < z.re})
    · refine continuousOn_of_forall_continuousAt ?_
      intro z hz
      exact (Smooth1MellinDifferentiable diffν suppν ⟨εpos, ε_lt_one⟩
        νpos mass_one hz).continuousAt
    · fun_prop
    · simp only [mapsTo_univ_iff, mem_ofPred_eq, add_re, ofReal_re, mul_re, I_re,
        mul_zero, ofReal_im, I_im, mul_one, sub_self, add_zero, forall_const]
      linarith
  have X_ne : X ≠ 0 := ne_of_gt X_pos
  have hmeas : AEStronglyMeasurable (fun t : ℝ => ∑' n : ℕ, term n t) := by
    apply AEStronglyMeasurable.tsum
    intro n
    by_cases hn : n = 0
    · simpa [term, hn, twistedVonMangoldtCoeff] using aestronglyMeasurable_const
    · apply Continuous.aestronglyMeasurable
      dsimp [term]
      fun_prop (disch := simp [hn, X_ne])
  have hmajor :
      ∫⁻ t : ℝ, ∑' n : ℕ, ‖term n t‖ₑ < ⊤ := by
    simp_rw [term, enorm_mul, enorm_eq_nnnorm, nnnorm_div, ← norm_toNNReal,
      Complex.norm_cpow_eq_rpow_re_of_pos X_pos, norm_toNNReal, abs_two]
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im,
      I_im, mul_one, sub_self, add_zero]
    simp_rw [ENNReal.tsum_mul_right]
    rw [MeasureTheory.lintegral_mul_const'
      (r := ↑(X ^ σ).toNNReal) (hr := ENNReal.coe_ne_top)]
    apply WithTop.mul_lt_top ?_ ENNReal.coe_lt_top
    have hCne :
        (∑' n : ℕ, (↑(‖twistedVonMangoldtCoeff χ n‖₊ /
          (n : NNReal) ^ σ) : ENNReal)) ≠ ⊤ := by
      rw [ENNReal.tsum_coe_ne_top_iff_summable_coe]
      push_cast
      refine Summable.of_nonneg_of_le (fun _ ↦ div_nonneg (norm_nonneg _) (by positivity))
        (fun n ↦ ?_)
        (ArithmeticFunction.LSeriesSummable_vonMangoldt (s := σ)
          (by simp only [ofReal_re]; linarith)).norm
      rw [LSeries.term_def]
      split_ifs with hn
      · simp [hn, twistedVonMangoldtCoeff]
      · dsimp [twistedVonMangoldtCoeff]
        rw [norm_div, norm_mul]
        calc
          ‖(Λ n : ℂ)‖ * ‖χ n‖ / (n : ℝ) ^ σ ≤
              ‖(Λ n : ℂ)‖ / (n : ℝ) ^ σ :=
            div_le_div_of_nonneg_right
              (mul_le_of_le_one_right (norm_nonneg _) (norm_le_one χ n)) (by positivity)
          _ = ‖(Λ n : ℂ)‖ / ‖(n : ℂ) ^ (σ : ℂ)‖ := by
            rw [Complex.norm_natCast_cpow_of_re_ne_zero n]
            · simp
            · simp only [ofReal_re]
              linarith
    rw [MeasureTheory.lintegral_const_mul' (hr := hCne)]
    apply WithTop.mul_lt_top (lt_top_iff_ne_top.mpr hCne)
    simp_rw [← enorm_eq_nnnorm]
    rw [← MeasureTheory.hasFiniteIntegral_iff_enorm]
    exact SmoothedChebyshevDirichlet_aux_integrable diffν νpos suppν mass_one
      εpos ε_lt_one σ_gt σ_le |>.hasFiniteIntegral
  have hseries : Integrable (fun t : ℝ => ∑' n : ℕ, term n t) := by
    refine ⟨hmeas, ?_⟩
    rw [MeasureTheory.hasFiniteIntegral_iff_enorm]
    exact lt_of_le_of_lt
      (MeasureTheory.lintegral_mono fun t => enorm_tsum_le_tsum_enorm) hmajor
  convert hseries using 1
  funext t
  dsimp [twistedSmoothedPerronIntegrand, term]
  rw [neg_logDeriv_LFunction_eq_tsum_twistedVonMangoldtCoeff χ]
  · rw [← tsum_mul_right, ← tsum_mul_right]
  · simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im,
      mul_one, sub_self, add_zero]
    exact σ_gt

/-- The right vertical integral is the sum of its lower tail, the finite
vertical segment from `-T` to `T`, and its upper tail. -/
theorem twistedSmoothedPerron_verticalIntegral_split_three
    (χ : DirichletCharacter ℂ q) {ν : ℝ → ℝ}
    (diffν : ContDiff ℝ 1 ν)
    (νpos : ∀ x > 0, 0 ≤ ν x)
    (suppν : support ν ⊆ Icc (1 / 2) 2)
    (mass_one : ∫ x in Ioi (0 : ℝ), ν x / x = 1)
    {X : ℝ} (X_pos : 0 < X) {ε : ℝ} (εpos : 0 < ε) (ε_lt_one : ε < 1)
    {σ : ℝ} (σ_gt : 1 < σ) (σ_le : σ ≤ 2) (T : ℝ) :
    VerticalIntegral (twistedSmoothedPerronIntegrand χ ν ε X) σ =
      I • (∫ t in Iic (-T), twistedSmoothedPerronIntegrand χ ν ε X (σ + t * I)) +
      VIntegral (twistedSmoothedPerronIntegrand χ ν ε X) σ (-T) T +
      I • ∫ t in Ici T, twistedSmoothedPerronIntegrand χ ν ε X (σ + t * I) := by
  exact verticalIntegral_split_three (-T) T
    (twistedSmoothedPerronIntegrand_integrable_right χ diffν νpos suppν mass_one
      X_pos εpos ε_lt_one σ_gt σ_le)

end DirichletCharacter