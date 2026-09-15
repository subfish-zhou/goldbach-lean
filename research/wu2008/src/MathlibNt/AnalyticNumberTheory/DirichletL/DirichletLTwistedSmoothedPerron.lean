import MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLFoundation
import PrimeNumberTheoremAnd.MediumPNT

open Set Function Filter Complex Real MeasureTheory
open ArithmeticFunction (vonMangoldt)
open scoped LSeries.notation

namespace DirichletCharacter

variable {q : ℕ} [NeZero q]

local notation "𝓜" => mellin
local notation "Λ" => ArithmeticFunction.vonMangoldt

/-- The coefficients of the negative logarithmic derivative of a Dirichlet
L-function, in the order used by the smoothed prime sum. -/
noncomputable def twistedVonMangoldtCoeff (χ : DirichletCharacter ℂ q) (n : ℕ) : ℂ :=
  (Λ n : ℂ) * χ n

/-- The genuinely infinite smoothed twisted Chebyshev sum. -/
noncomputable def twistedSmoothedPsi (χ : DirichletCharacter ℂ q)
    (ν : ℝ → ℝ) (ε X : ℝ) : ℂ :=
  ∑' n : ℕ, twistedVonMangoldtCoeff χ n * Smooth1 ν ε (n / X)

/-- The integrand in the twisted smoothed Perron formula. -/
noncomputable def twistedSmoothedPerronIntegrand (χ : DirichletCharacter ℂ q)
    (ν : ℝ → ℝ) (ε X : ℝ) (s : ℂ) : ℂ :=
  (-deriv (LFunction χ) s / LFunction χ s) *
    𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) s * (X : ℂ) ^ s

lemma neg_logDeriv_LFunction_eq_tsum_twistedVonMangoldtCoeff
    (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re) :
    -deriv (LFunction χ) s / LFunction χ s =
      ∑' n : ℕ, twistedVonMangoldtCoeff χ n / (n : ℂ) ^ s := by
  rw [← LSeries_twist_vonMangoldt_eq_neg_logDeriv_LFunction χ hs]
  dsimp [LSeries, LSeries.term]
  nth_rewrite 2 [Summable.tsum_eq_add_tsum_ite (b := 0) ?_]
  · simp [twistedVonMangoldtCoeff, mul_comm]
  · have h := LSeriesSummable_twist_vonMangoldt χ hs
    dsimp [LSeriesSummable] at h
    convert! h
    rename ℕ => n
    by_cases hn : n = 0 <;> simp [LSeries.term, twistedVonMangoldtCoeff, hn, mul_comm]

set_option backward.isDefEq.respectTransparency false in
omit [NeZero q] in
lemma twistedSmoothedPerron_aux_tsum_integral
    (χ : DirichletCharacter ℂ q) {ν : ℝ → ℝ}
    (diffν : ContDiff ℝ 1 ν)
    (νpos : ∀ x > 0, 0 ≤ ν x)
    (suppν : support ν ⊆ Icc (1 / 2) 2)
    (mass_one : ∫ x in Ioi (0 : ℝ), ν x / x = 1)
    {X : ℝ} (X_pos : 0 < X) {ε : ℝ} (εpos : 0 < ε) (ε_lt_one : ε < 1)
    {σ : ℝ} (σ_gt : 1 < σ) (σ_le : σ ≤ 2) :
    ∫ t : ℝ, ∑' n : ℕ,
      twistedVonMangoldtCoeff χ n / (n : ℂ) ^ (σ + t * I) *
        𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) (σ + t * I) *
          (X : ℂ) ^ (σ + t * I) =
    ∑' n : ℕ, ∫ t : ℝ,
      twistedVonMangoldtCoeff χ n / (n : ℂ) ^ (σ + t * I) *
        𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) (σ + t * I) *
          (X : ℂ) ^ (σ + t * I) := by
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
  have norm_nat_cpow_vertical : ∀ a : ℝ, ∀ n : ℕ,
      ‖(n : ℂ) ^ ((σ : ℂ) + a * I)‖₊ = n ^ σ := by
    intro a n
    simp_rw [← norm_toNNReal]
    rw [norm_natCast_cpow_of_re_ne_zero _ (by
      simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im,
        mul_one, sub_self, add_zero, ne_eq]
      linarith)]
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im,
      mul_one, sub_self, add_zero,
      Real.toNNReal_of_nonneg <| rpow_nonneg (y := σ) (x := n) (by linarith)]
    norm_cast
  -- Absolute integrability separates into the coefficient series and Mellin decay.
  rw [MeasureTheory.integral_tsum]
  · have X_ne : X ≠ 0 := ne_of_gt X_pos
    intro n
    by_cases hn : n = 0
    · simpa [hn, twistedVonMangoldtCoeff] using aestronglyMeasurable_const
    · apply Continuous.aestronglyMeasurable
      fun_prop (disch := simp [hn, X_ne])
  · rw [← lt_top_iff_ne_top]
    simp_rw [enorm_mul, enorm_eq_nnnorm, nnnorm_div, ← norm_toNNReal,
      Complex.norm_cpow_eq_rpow_re_of_pos X_pos, norm_toNNReal, norm_nat_cpow_vertical]
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im,
      I_im, mul_one, sub_self, add_zero]
    simp_rw [MeasureTheory.lintegral_mul_const' (r := ↑(X ^ σ).toNNReal) (hr := by simp),
      ENNReal.tsum_mul_right]
    apply WithTop.mul_lt_top ?_ ENNReal.coe_lt_top
    conv =>
      arg 1
      arg 1
      intro n
      rw [MeasureTheory.lintegral_const_mul' (hr := by simp)]
    rw [ENNReal.tsum_mul_right]
    apply WithTop.mul_lt_top
    · rw [WithTop.lt_top_iff_ne_top, ENNReal.tsum_coe_ne_top_iff_summable_coe]
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
    · simp_rw [← enorm_eq_nnnorm]
      rw [← MeasureTheory.hasFiniteIntegral_iff_enorm]
      exact SmoothedChebyshevDirichlet_aux_integrable diffν νpos suppν mass_one
        εpos ε_lt_one σ_gt σ_le |>.hasFiniteIntegral

set_option backward.isDefEq.respectTransparency false in
/-- Smoothed Perron inversion for the von Mangoldt coefficients twisted by an
arbitrary Dirichlet character.  No nonprincipality assumption and no contour
shift are used. -/
theorem twistedSmoothedPerron
    (χ : DirichletCharacter ℂ q) {ν : ℝ → ℝ}
    (diffν : ContDiff ℝ 1 ν)
    (νpos : ∀ x > 0, 0 ≤ ν x)
    (suppν : support ν ⊆ Icc (1 / 2) 2)
    (mass_one : ∫ x in Ioi (0 : ℝ), ν x / x = 1)
    {X : ℝ} (X_pos : 0 < X) {ε : ℝ} (εpos : 0 < ε) (ε_lt_one : ε < 1)
    {σ : ℝ} (σ_gt : 1 < σ) (σ_le : σ ≤ 2) :
    twistedSmoothedPsi χ ν ε X =
      VerticalIntegral' (twistedSmoothedPerronIntegrand χ ν ε X) σ := by
  symm
  dsimp [twistedSmoothedPsi, twistedSmoothedPerronIntegrand,
    VerticalIntegral', VerticalIntegral]
  calc
    _ = 1 / (2 * π * I) * (I * ∫ t : ℝ, ∑' n : ℕ,
        twistedVonMangoldtCoeff χ n / (n : ℂ) ^ (σ + t * I) *
          𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) (σ + t * I) *
            (X : ℂ) ^ (σ + t * I)) := by
      congr
      ext t
      rw [neg_logDeriv_LFunction_eq_tsum_twistedVonMangoldtCoeff χ]
      · rw [← tsum_mul_right, ← tsum_mul_right]
      · simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im,
          mul_one, sub_self, add_zero]
        exact σ_gt
    _ = 1 / (2 * π * I) * (I * ∑' n : ℕ, ∫ t : ℝ,
        twistedVonMangoldtCoeff χ n / (n : ℂ) ^ (σ + t * I) *
          𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) (σ + t * I) *
            (X : ℂ) ^ (σ + t * I)) := by
      congr 2
      exact twistedSmoothedPerron_aux_tsum_integral χ diffν νpos suppν mass_one
        X_pos εpos ε_lt_one σ_gt σ_le
    _ = 1 / (2 * π * I) * (I * ∑' n : ℕ, twistedVonMangoldtCoeff χ n *
        ∫ t : ℝ, 𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) (σ + t * I) *
          (X / (n : ℂ)) ^ (σ + t * I)) := by
      field_simp
      congr 1
      ext n
      rw [← MeasureTheory.integral_const_mul]
      congr 1
      ext t
      by_cases hn : n = 0
      · simp [hn, twistedVonMangoldtCoeff]
      rw [mul_div_assoc, mul_assoc]
      congr 1
      rw [(div_eq_iff (by simp [hn])).mpr]
      · have hmul := @mul_cpow_ofReal_nonneg (a := X / (n : ℝ)) (b := (n : ℝ))
          (r := σ + I * t) (div_nonneg X_pos.le (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
        push_cast at hmul ⊢
        rw [← hmul, div_mul_cancel₀]
        simp [hn]
    _ = 1 / (2 * π) * (∑' n : ℕ, twistedVonMangoldtCoeff χ n *
        ∫ t : ℝ, 𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) (σ + t * I) *
          (X / (n : ℂ)) ^ (σ + t * I)) := by
      rw [← mul_assoc]
      congr 1
      field_simp
    _ = ∑' n : ℕ, twistedVonMangoldtCoeff χ n *
        (1 / (2 * π) * ∫ t : ℝ,
          𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) (σ + t * I) *
            (X / (n : ℂ)) ^ (σ + t * I)) := by
      simp_rw [← tsum_mul_left, ← mul_assoc, mul_comm]
    _ = ∑' n : ℕ, twistedVonMangoldtCoeff χ n *
        (1 / (2 * π) * ∫ t : ℝ,
          𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) (σ + t * I) *
            ((n : ℂ) / X) ^ (-(σ + t * I))) := by
      have ht (t : ℝ) : -(σ + t * I) = (-1) * (σ + t * I) := by simp
      have hninv (n : ℂ) : (n / X) ^ (-1 : ℂ) = X / n := by simp [cpow_neg_one]
      have him (n : ℕ) : (log ((n : ℂ) / (X : ℂ)) * -1).im = 0 := by
        simp [Complex.log_im, arg_eq_zero_iff,
          div_nonneg (Nat.cast_nonneg _) X_pos.le]
      have hpow (n : ℕ) (t : ℝ) :
          ((n : ℂ) / X) ^ ((-1 : ℂ) * (σ + t * I)) =
            (((n : ℂ) / X) ^ (-1 : ℂ)) ^ (σ + t * I) := by
        rw [cpow_mul] <;> rw [him n] <;> simp [Real.pi_pos, Real.pi_nonneg]
      simp_rw [ht, hpow, hninv]
    _ = _ := by
      congr 1
      ext n
      by_cases hn : n = 0
      · simp [hn, twistedVonMangoldtCoeff]
      have n_pos : 0 < n := Nat.pos_of_ne_zero hn
      congr 1
      have h := mellinInv_mellin_eq σ
        (f := fun x ↦ (Smooth1 ν ε x : ℂ)) (x := n / X) ?_ ?_ ?_ ?_
      · beta_reduce at h
        dsimp [mellinInv, VerticalIntegral] at h
        convert! h using 4
        · norm_cast
        · rw [mul_comm]
          norm_cast
      · exact div_pos (by exact_mod_cast n_pos) X_pos
      · apply Smooth1MellinConvergent diffν suppν ⟨εpos, ε_lt_one⟩ νpos mass_one
        simp only [ofReal_re]
        linarith
      · dsimp [VerticalIntegrable]
        exact SmoothedChebyshevDirichlet_aux_integrable diffν νpos suppν mass_one
          εpos ε_lt_one σ_gt σ_le
      · refine ContinuousAt.comp (g := ofReal) RCLike.continuous_ofReal.continuousAt ?_
        exact Smooth1ContinuousAt diffν νpos suppν εpos (by positivity)

end DirichletCharacter