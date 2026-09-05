import MathlibNt.AnalyticNumberTheory.LargeSieve.DirichLTwistedPerronRightVerticalIntegrable
import MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLRightHalfPlaneBounds

open Set Function Filter Complex Real MeasureTheory
open ArithmeticFunction (vonMangoldt)

namespace DirichletCharacter

variable {q : ℕ} [NeZero q]

local notation "𝓜" => mellin
local notation "Λ" => ArithmeticFunction.vonMangoldt

/-- The natural absolute Dirichlet-series majorant on the line `re s = 1 + δ`. -/
noncomputable def twistedVonMangoldtRightMajorant
    (χ : DirichletCharacter ℂ q) (δ t : ℝ) : ℝ :=
  ∑' n : ℕ,
    ‖twistedVonMangoldtCoeff χ n /
      (n : ℂ) ^ ((1 + δ : ℝ) + t * I)‖

/-- A completely explicit character- and height-independent estimate for the
absolute von Mangoldt Dirichlet series. -/
theorem twistedVonMangoldtRightMajorant_le
    (χ : DirichletCharacter ℂ q) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (t : ℝ) :
    twistedVonMangoldtRightMajorant χ δ t ≤ 6 * (1 + δ⁻¹ ^ 2) := by
  let s : ℂ := (1 + δ : ℝ) + t * I
  have hs : 1 < s.re := by simp [s]; linarith
  have hright : Summable (fun n : ℕ =>
      (2 / δ) * (n : ℝ) ^ (-(1 + δ / 2))) := by
    apply Summable.mul_left
    exact Real.summable_nat_rpow.mpr (by linarith)
  have hterm (n : ℕ) :
      ‖twistedVonMangoldtCoeff χ n / (n : ℂ) ^ s‖ ≤
        (2 / δ) * (n : ℝ) ^ (-(1 + δ / 2)) := by
    by_cases hn : n = 0
    · subst n
      rw [show twistedVonMangoldtCoeff χ 0 = 0 by
        simp [twistedVonMangoldtCoeff]]
      simp only [zero_div, norm_zero]
      exact mul_nonneg (by positivity) (Real.rpow_nonneg (by norm_num) _)
    have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hlog := Real.log_natCast_le_rpow_div n (show 0 < δ / 2 by positivity)
    have hΛlog : Λ n ≤ Real.log n := ArithmeticFunction.vonMangoldt_le_log
    have hpow :
        (n : ℝ) ^ (δ / 2) / (δ / 2) / (n : ℝ) ^ (1 + δ) =
          (2 / δ) * (n : ℝ) ^ (-(1 + δ / 2)) := by
      calc
        (n : ℝ) ^ (δ / 2) / (δ / 2) / (n : ℝ) ^ (1 + δ) =
            (2 / δ) * ((n : ℝ) ^ (δ / 2) / (n : ℝ) ^ (1 + δ)) := by
              field_simp [hδ.ne']
        _ = (2 / δ) * (n : ℝ) ^ (δ / 2 - (1 + δ)) := by
              rw [Real.rpow_sub hnpos]
        _ = _ := by congr 2 <;> ring
    rw [norm_div, twistedVonMangoldtCoeff, norm_mul,
      Complex.norm_real, Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
      Complex.norm_natCast_cpow_of_re_ne_zero n]
    · simp only [s, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im,
        mul_one, sub_self, add_zero]
      calc
        Λ n * ‖χ n‖ / (n : ℝ) ^ (1 + δ) ≤
            Λ n / (n : ℝ) ^ (1 + δ) := by
              exact div_le_div_of_nonneg_right
                (mul_le_of_le_one_right ArithmeticFunction.vonMangoldt_nonneg
                  (norm_le_one χ n)) (Real.rpow_nonneg hnpos.le _)
        _ ≤ Real.log n / (n : ℝ) ^ (1 + δ) := by gcongr
        _ ≤ ((n : ℝ) ^ (δ / 2) / (δ / 2)) / (n : ℝ) ^ (1 + δ) := by
              gcongr
        _ = _ := hpow
    · simp [s]
      linarith
  have hleft : Summable (fun n : ℕ =>
      ‖twistedVonMangoldtCoeff χ n / (n : ℂ) ^ s‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm hright
  have hseries : twistedVonMangoldtRightMajorant χ δ t ≤
      (2 / δ) * (1 + 1 / ((1 + δ / 2) - 1)) := by
    unfold twistedVonMangoldtRightMajorant
    change (∑' n : ℕ, ‖twistedVonMangoldtCoeff χ n / (n : ℂ) ^ s‖) ≤ _
    calc
      _ ≤ ∑' n : ℕ, (2 / δ) * (n : ℝ) ^ (-(1 + δ / 2)) :=
        hleft.tsum_le_tsum hterm hright
      _ = (2 / δ) * ∑' n : ℕ, (n : ℝ) ^ (-(1 + δ / 2)) :=
        tsum_mul_left
      _ ≤ (2 / δ) * (1 + 1 / ((1 + δ / 2) - 1)) := by
        gcongr
        exact AnalyticNumberTheory.LargeSieve.tsum_nat_rpow_neg_le
          (1 + δ / 2) (by linarith)
  calc
    twistedVonMangoldtRightMajorant χ δ t
        ≤ (2 / δ) * (1 + 1 / ((1 + δ / 2) - 1)) := hseries
    _ = 2 / δ + 4 / δ ^ 2 := by field_simp [hδ.ne']; ring
    _ ≤ 6 * (1 + δ⁻¹ ^ 2) := by
      have hinv : 1 ≤ δ⁻¹ := by
        rw [inv_eq_one_div, le_div_iff₀ hδ]
        simpa using hδ1
      have hinv0 : 0 ≤ δ⁻¹ := le_of_lt (inv_pos.mpr hδ)
      have hdivsq : 4 / δ ^ 2 = 4 * δ⁻¹ ^ 2 := by
        field_simp [hδ.ne']
      rw [div_eq_mul_inv, hdivsq]
      nlinarith [sq_nonneg (δ⁻¹ - 1)]

private theorem integral_right_inv_one_add_sq_le_inv
    {T : ℝ} (hT : 1 ≤ T) :
    ∫ t in Ici T, (1 + t ^ 2)⁻¹ ≤ T⁻¹ := by
  rw [integral_Ici_eq_integral_Ioi]
  have hmono : ∀ᵐ t ∂volume.restrict (Ioi T),
      (1 + t ^ 2)⁻¹ ≤ t ^ (-2 : ℝ) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := (lt_of_lt_of_le zero_lt_one hT).trans ht
    rw [Real.rpow_neg (le_of_lt ht0), Real.rpow_two]
    exact inv_anti₀ (sq_pos_of_pos ht0) (by nlinarith)
  calc
    ∫ t in Ioi T, (1 + t ^ 2)⁻¹ ≤ ∫ t in Ioi T, t ^ (-2 : ℝ) := by
      refine integral_mono_ae integrable_inv_one_add_sq.integrableOn
        (integrableOn_Ioi_rpow_of_lt (by norm_num) (lt_of_lt_of_le zero_lt_one hT)) hmono
    _ = T⁻¹ := by
      rw [integral_Ioi_rpow_of_lt (by norm_num) (lt_of_lt_of_le zero_lt_one hT)]
      norm_num [Real.rpow_neg_one]

private theorem integral_left_inv_one_add_sq_le_inv
    {T : ℝ} (hT : 1 ≤ T) :
    ∫ t in Iic (-T), (1 + t ^ 2)⁻¹ ≤ T⁻¹ := by
  calc
    ∫ t in Iic (-T), (1 + t ^ 2)⁻¹ =
        ∫ t in Ioi T, (1 + t ^ 2)⁻¹ := by
          rw [integral_Iic_inv_one_add_sq, integral_Ioi_inv_one_add_sq,
            Real.arctan_neg]
          ring
    _ ≤ T⁻¹ := by
      simpa [integral_Ici_eq_integral_Ioi] using
        integral_right_inv_one_add_sq_le_inv hT

set_option maxHeartbeats 3000000 in
set_option backward.isDefEq.respectTransparency false in
/-- Quantitative lower and upper tails on the standard right line `σ = 1 + δ`.
The constant is selected before `q, χ, δ, ε, X, T`, hence depends only on the
smoothing function. -/
theorem twistedSmoothedPerron_right_tails_quantitative
    {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν)
    (νpos : ∀ x > 0, 0 ≤ ν x)
    (suppν : support ν ⊆ Icc (1 / 2) 2)
    (mass_one : ∫ x in Ioi (0 : ℝ), ν x / x = 1) :
    ∃ c > 0, ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
      {δ ε X T : ℝ}, 0 < δ → δ ≤ 1 → 0 < ε → ε < 1 → 0 < X → 1 ≤ T →
      ‖∫ t in Iic (-T),
          twistedSmoothedPerronIntegrand χ ν ε X (((1 + δ : ℝ) : ℂ) + t * I)‖ ≤
          c * X ^ (1 + δ) * (1 + δ⁻¹ ^ 2) / (ε * T) ∧
      ‖∫ t in Ici T,
          twistedSmoothedPerronIntegrand χ ν ε X (((1 + δ : ℝ) : ℂ) + t * I)‖ ≤
          c * X ^ (1 + δ) * (1 + δ⁻¹ ^ 2) / (ε * T) := by
  obtain ⟨C, Cpos, hC⟩ := MellinOfSmooth1b diffν suppν
  refine ⟨6 * C, by positivity, ?_⟩
  intro q _ χ δ ε X T hδ hδ1 hε hε1 hX hT
  have hσ : 1 < 1 + δ := by linarith
  have hσ2 : 1 + δ ≤ 2 := by linarith
  let f : ℝ → ℂ := fun t =>
    twistedSmoothedPerronIntegrand χ ν ε X (((1 + δ : ℝ) : ℂ) + t * I)
  let g : ℝ → ℝ := fun t =>
    6 * (1 + δ⁻¹ ^ 2) * C / ε * X ^ (1 + δ) * (1 + t ^ 2)⁻¹
  have hf : Integrable f := by
    simpa only [f] using
      (twistedSmoothedPerronIntegrand_integrable_right (q := q) (σ := 1 + δ)
        (X := X) (ε := ε) χ diffν νpos suppν mass_one hX hε hε1 hσ hσ2)
  have hg : Integrable g := by
    dsimp [g]
    exact integrable_inv_one_add_sq.const_mul _
  have hpoint (t : ℝ) : ‖f t‖ ≤ g t := by
    have hsre : 1 < (((1 + δ : ℝ) : ℂ) + t * I).re := by simp; linarith
    have hsum : Summable (fun n : ℕ =>
        twistedVonMangoldtCoeff χ n /
          (n : ℂ) ^ (((1 + δ : ℝ) : ℂ) + t * I)) := by
      have h := DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ hsre
      rw [LSeriesSummable] at h
      convert h using 1
      ext n
      by_cases hn : n = 0
      · simp [LSeries.term, twistedVonMangoldtCoeff, hn]
      · simp [LSeries.term, twistedVonMangoldtCoeff, hn, mul_comm]
    have hseries := norm_tsum_le_tsum_norm hsum.norm
    have hmellin := hC ((1 + δ) / 2) (by positivity)
      (((1 + δ : ℝ) : ℂ) + t * I) (by simp; linarith) (by simp; linarith)
      ε hε hε1
    have hmaj := twistedVonMangoldtRightMajorant_le χ hδ hδ1 t
    dsimp [f, g, twistedSmoothedPerronIntegrand]
    rw [neg_logDeriv_LFunction_eq_tsum_twistedVonMangoldtCoeff χ hsre,
      norm_mul, norm_mul]
    have hseries' :
        ‖∑' n : ℕ, twistedVonMangoldtCoeff χ n /
          (n : ℂ) ^ (((1 + δ : ℝ) : ℂ) + t * I)‖ ≤
          twistedVonMangoldtRightMajorant χ δ t := by
      simpa [twistedVonMangoldtRightMajorant] using hseries
    have hmajor0 : 0 ≤ twistedVonMangoldtRightMajorant χ δ t :=
      tsum_nonneg fun _ => norm_nonneg _
    have hmellinR0 :
        0 ≤ C * (ε * ‖(((1 + δ : ℝ) : ℂ) + t * I)‖ ^ 2)⁻¹ := by positivity
    have hXnorm :
        ‖(X : ℂ) ^ (((1 + δ : ℝ) : ℂ) + t * I)‖ = X ^ (1 + δ) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hX]
      simp
    have hXpow0 : 0 ≤ X ^ (1 + δ) := Real.rpow_nonneg hX.le _
    have hfirst :
        ‖∑' n : ℕ, twistedVonMangoldtCoeff χ n /
          (n : ℂ) ^ (((1 + δ : ℝ) : ℂ) + t * I)‖ *
            ‖𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) (((1 + δ : ℝ) : ℂ) + t * I)‖ ≤
          twistedVonMangoldtRightMajorant χ δ t *
            (C * (ε * ‖(((1 + δ : ℝ) : ℂ) + t * I)‖ ^ 2)⁻¹) := by
      calc
        _ ≤ twistedVonMangoldtRightMajorant χ δ t *
            ‖𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) (((1 + δ : ℝ) : ℂ) + t * I)‖ :=
          mul_le_mul_of_nonneg_right hseries' (norm_nonneg _)
        _ ≤ _ := mul_le_mul_of_nonneg_left hmellin hmajor0
    have hnormsq : 1 + t ^ 2 ≤ ‖(((1 + δ : ℝ) : ℂ) + t * I)‖ ^ 2 := by
      rw [Complex.sq_norm]
      simp [Complex.normSq_apply]
      nlinarith
    have hinvnorm :
        (ε * ‖(((1 + δ : ℝ) : ℂ) + t * I)‖ ^ 2)⁻¹ ≤
          ε⁻¹ * (1 + t ^ 2)⁻¹ := by
      rw [mul_inv_rev]
      simpa only [mul_comm] using mul_le_mul_of_nonneg_right
        (inv_anti₀ (by nlinarith [sq_nonneg t]) hnormsq) (inv_nonneg.mpr hε.le)
    calc
      ‖∑' n : ℕ, twistedVonMangoldtCoeff χ n /
          (n : ℂ) ^ (((1 + δ : ℝ) : ℂ) + t * I)‖ *
            ‖𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) (((1 + δ : ℝ) : ℂ) + t * I)‖ *
              ‖(X : ℂ) ^ (((1 + δ : ℝ) : ℂ) + t * I)‖
          ≤ (twistedVonMangoldtRightMajorant χ δ t *
            (C * (ε * ‖(((1 + δ : ℝ) : ℂ) + t * I)‖ ^ 2)⁻¹)) *
              X ^ (1 + δ) := by rw [← hXnorm]; gcongr
      _ ≤ (6 * (1 + δ⁻¹ ^ 2) *
            (C * (ε * ‖(((1 + δ : ℝ) : ℂ) + t * I)‖ ^ 2)⁻¹)) *
              X ^ (1 + δ) := by
                gcongr
      _ ≤ (6 * (1 + δ⁻¹ ^ 2) * (C * (ε⁻¹ * (1 + t ^ 2)⁻¹))) *
              X ^ (1 + δ) := by
                gcongr
      _ = 6 * (1 + δ⁻¹ ^ 2) * C / ε * X ^ (1 + δ) * (1 + t ^ 2)⁻¹ := by
        ring
  constructor
  · calc
      ‖∫ t in Iic (-T), f t‖ ≤ ∫ t in Iic (-T), ‖f t‖ :=
        norm_integral_le_integral_norm _
      _ ≤ ∫ t in Iic (-T), g t := by
        exact integral_mono_ae hf.norm.integrableOn hg.integrableOn
          (ae_restrict_of_forall_mem measurableSet_Iic fun t _ => hpoint t)
      _ ≤ 6 * C * X ^ (1 + δ) * (1 + δ⁻¹ ^ 2) / (ε * T) := by
        dsimp [g]
        rw [integral_const_mul]
        have htail := integral_left_inv_one_add_sq_le_inv hT
        calc
          (6 * (1 + δ⁻¹ ^ 2) * C / ε * X ^ (1 + δ)) *
              ∫ t in Iic (-T), (1 + t ^ 2)⁻¹
              ≤ (6 * (1 + δ⁻¹ ^ 2) * C / ε * X ^ (1 + δ)) * T⁻¹ := by
                gcongr
          _ = _ := by field_simp [hε.ne', (lt_of_lt_of_le zero_lt_one hT).ne']
  · calc
      ‖∫ t in Ici T, f t‖ ≤ ∫ t in Ici T, ‖f t‖ :=
        norm_integral_le_integral_norm _
      _ ≤ ∫ t in Ici T, g t := by
        exact integral_mono_ae hf.norm.integrableOn hg.integrableOn
          (ae_restrict_of_forall_mem measurableSet_Ici fun t _ => hpoint t)
      _ ≤ 6 * C * X ^ (1 + δ) * (1 + δ⁻¹ ^ 2) / (ε * T) := by
        dsimp [g]
        rw [integral_const_mul]
        have htail := integral_right_inv_one_add_sq_le_inv hT
        calc
          (6 * (1 + δ⁻¹ ^ 2) * C / ε * X ^ (1 + δ)) *
              ∫ t in Ici T, (1 + t ^ 2)⁻¹
              ≤ (6 * (1 + δ⁻¹ ^ 2) * C / ε * X ^ (1 + δ)) * T⁻¹ := by
                gcongr
          _ = _ := by field_simp [hε.ne', (lt_of_lt_of_le zero_lt_one hT).ne']

end DirichletCharacter