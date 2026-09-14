import MathlibNt.AnalyticNumberTheory.LargeSieve.DirichLTwistedSmoothedConductorLogEdges

open Set Function Filter Complex Real MeasureTheory

namespace AnalyticNumberTheory.LargeSieve

local notation "𝓜" => mellin

/-- Positivity of the logarithmic parameter and its associated edge width. -/
private theorem conductorLog_parameters_pos
    {q : ℕ} [NeZero q] {T : ℝ} (hT : 3 ≤ T) :
    0 < dirichletLTwistedSmoothedConductorLogLM q T ∧
      0 < dirichletLTwistedSmoothedConductorLogEdgeWidth q T := by
  have hM : 4 ≤ dirichletLTwistedSmoothedConductorLogCutoff q T := by
    simpa only [dirichletLTwistedSmoothedConductorLogCutoff] using
      four_le_dirichletLNonquadraticConductorLogCutoff hT
  have hlog : 0 < Real.log (dirichletLTwistedSmoothedConductorLogCutoff q T : ℝ) :=
    Real.log_pos (by exact_mod_cast
      (show 1 < dirichletLTwistedSmoothedConductorLogCutoff q T by omega))
  have hLM : 0 < dirichletLTwistedSmoothedConductorLogLM q T := by
    dsimp only [dirichletLTwistedSmoothedConductorLogLM]
    linarith
  refine ⟨hLM, ?_⟩
  dsimp only [dirichletLTwistedSmoothedConductorLogEdgeWidth]
  positivity

/-- The final left edge is still strictly to the right of `1/2`. -/
private theorem one_half_lt_conductorLogFinalLeft
    {q : ℕ} [NeZero q] {T : ℝ} (hT : 3 ≤ T) :
    (1 / 2 : ℝ) < dirichletLTwistedSmoothedConductorLogFinalLeft q T := by
  have hold := one_half_lt_dirichletLTwistedSmoothedConductorLogLeftEdge
    (q := q) (T := T) hT
  have hw := (conductorLog_parameters_pos (q := q) hT).2
  have hle : dirichletLTwistedSmoothedConductorLogLeftEdge q T ≤
      dirichletLTwistedSmoothedConductorLogFinalLeft q T := by
    change 1 - dirichletLTwistedSmoothedConductorLogEdgeWidth q T ≤
      1 - dirichletLTwistedSmoothedConductorLogEdgeWidth q T / 4
    linarith
  exact hold.trans_le hle

/-- A horizontal Mellin--Bochner estimate, independent of the character's
zero-free region.  The caller supplies the Mellin decay and the log-derivative
bound; the proof pays for the height, complex power, and interval length. -/
theorem norm_twistedSmoothedPerron_horizontal_le_of_logDeriv_bound
    {ν : ℝ → ℝ} {M ε : ℝ} (hM : 0 ≤ M) (hε : 0 < ε)
    (hMellin : ∀ s : ℂ, (1 / 2 : ℝ) ≤ s.re → s.re ≤ 2 →
      ‖mellin (fun x ↦ (Smooth1 ν ε x : ℂ)) s‖ ≤ M * (ε * ‖s‖ ^ 2)⁻¹)
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {a b T t X J : ℝ} (ha : (1 / 2 : ℝ) ≤ a) (hab : a ≤ b)
    (hb : b ≤ 2) (hT : 1 ≤ T) (ht : |t| = T) (hX : 1 ≤ X) (hJ : 0 ≤ J)
    (hlog : ∀ σ : ℝ, a ≤ σ → σ ≤ b →
      ‖deriv χ.LFunction (σ + t * I) / χ.LFunction (σ + t * I)‖ ≤ J) :
    ‖HIntegral (DirichletCharacter.twistedSmoothedPerronIntegrand χ ν ε X) a b t‖ ≤
      4 * M * J * X ^ b / (ε * (1 + T ^ 2)) := by
  have hX0 : 0 < X := lt_of_lt_of_le zero_lt_one hX
  have hT0 : 0 < T := by linarith
  have hpoint (σ : ℝ) (hσa : a ≤ σ) (hσb : σ ≤ b) :
      ‖DirichletCharacter.twistedSmoothedPerronIntegrand χ ν ε X (σ + t * I)‖ ≤
        J * (2 * M / (ε * (1 + T ^ 2))) * X ^ b := by
    have hm := hMellin (σ + t * I) (by simp; linarith) (by simp; exact hσb.trans hb)
    have hnormsq : T ^ 2 ≤ ‖(σ : ℂ) + t * I‖ ^ 2 := by
      rw [Complex.sq_norm]
      simp [Complex.normSq_apply]
      have ht2 := congrArg (fun u : ℝ => u ^ 2) ht
      rw [sq_abs] at ht2
      nlinarith [sq_nonneg σ]
    have hinvDen : (T ^ 2)⁻¹ ≤ 2 * (1 + T ^ 2)⁻¹ := by
      rw [show (T ^ 2)⁻¹ = 1 / T ^ 2 by rw [one_div],
        show 2 * (1 + T ^ 2)⁻¹ = 2 / (1 + T ^ 2) by rw [div_eq_mul_inv]]
      rw [div_le_div_iff₀ (sq_pos_of_pos hT0) (by positivity)]
      nlinarith [sq_nonneg T]
    have hm' : ‖mellin (fun x ↦ (Smooth1 ν ε x : ℂ)) (σ + t * I)‖ ≤
        2 * M / (ε * (1 + T ^ 2)) := by
      calc
        _ ≤ M * (ε * ‖(σ : ℂ) + t * I‖ ^ 2)⁻¹ := hm
        _ ≤ M * (2 / (ε * (1 + T ^ 2))) := by
          gcongr
          rw [mul_inv_rev]
          calc
            (‖(σ : ℂ) + t * I‖ ^ 2)⁻¹ * ε⁻¹ ≤
                (2 * (1 + T ^ 2)⁻¹) * ε⁻¹ := by
              gcongr
              exact (inv_anti₀ (sq_pos_of_pos hT0) hnormsq).trans hinvDen
            _ = 2 / (ε * (1 + T ^ 2)) := by field_simp [hε.ne']
        _ = 2 * M / (ε * (1 + T ^ 2)) := by ring
    have hXnorm : ‖(X : ℂ) ^ ((σ : ℂ) + t * I)‖ = X ^ σ := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hX0]
      simp
    have hXpow : X ^ σ ≤ X ^ b := Real.rpow_le_rpow_of_exponent_le hX hσb
    have hlog' : ‖-deriv χ.LFunction (σ + t * I) / χ.LFunction (σ + t * I)‖ ≤ J := by
      simpa only [neg_div, norm_neg] using hlog σ hσa hσb
    dsimp only [DirichletCharacter.twistedSmoothedPerronIntegrand]
    rw [norm_mul, norm_mul, hXnorm]
    calc
      _ ≤ J * (2 * M / (ε * (1 + T ^ 2))) * X ^ σ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul hlog' hm' (norm_nonneg _) hJ) (Real.rpow_nonneg hX0.le _)
      _ ≤ _ := by gcongr
  rw [HIntegral]
  calc
    _ ≤ (J * (2 * M / (ε * (1 + T ^ 2))) * X ^ b) * |b - a| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro σ hσ
      rw [uIoc_of_le hab] at hσ
      exact hpoint σ hσ.1.le hσ.2
    _ ≤ (J * (2 * M / (ε * (1 + T ^ 2))) * X ^ b) * 2 := by
      have hlen : |b - a| ≤ 2 := by
        rw [abs_of_nonneg (sub_nonneg.mpr hab)]
        linarith
      gcongr
    _ = _ := by ring

/-- Genuine Bochner interval estimates for all three non-right edges of the
final conductor-logarithmic rectangle.  The constant is selected before every
arithmetic and contour parameter, so it depends only on the fixed smoothing
function `ν` (through `MellinOfSmooth1b`). -/
theorem exists_dirichletLTwistedSmoothedContourNormBounds
    {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν)
    (suppν : support ν ⊆ Icc (1 / 2) 2) :
    ∃ C > 0, ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
      {T d ε X : ℝ}, χ ^ 2 ≠ 1 → 3 ≤ T → 0 < d → d ≤ 1 →
      0 < ε → ε < 1 → 1 ≤ X →
      ‖VIntegral (DirichletCharacter.twistedSmoothedPerronIntegrand χ ν ε X)
          (dirichletLTwistedSmoothedConductorLogFinalLeft q T) (-T) T‖ ≤
        C * T * (dirichletLTwistedSmoothedConductorLogLM q T) ^ 11 *
          X ^ (dirichletLTwistedSmoothedConductorLogFinalLeft q T) / ε ∧
      ‖HIntegral (DirichletCharacter.twistedSmoothedPerronIntegrand χ ν ε X)
          (dirichletLTwistedSmoothedConductorLogFinalLeft q T)
          (dirichletLTwistedSmoothedConductorLogRight d) T‖ ≤
        C * (dirichletLTwistedSmoothedConductorLogLM q T) ^ 11 * X ^ (1 + d) /
          (ε * (1 + T ^ 2)) ∧
      ‖HIntegral (DirichletCharacter.twistedSmoothedPerronIntegrand χ ν ε X)
          (dirichletLTwistedSmoothedConductorLogFinalLeft q T)
          (dirichletLTwistedSmoothedConductorLogRight d) (-T)‖ ≤
        C * (dirichletLTwistedSmoothedConductorLogLM q T) ^ 11 * X ^ (1 + d) /
          (ε * (1 + T ^ 2)) := by
  obtain ⟨A, hA, hMellin⟩ := MellinOfSmooth1b diffν suppν
  refine ⟨36028797018963968 * A, by positivity, ?_⟩
  intro q _ χ T d ε X hχsq hT hd hd1 hε hε1 hX
  let LM := dirichletLTwistedSmoothedConductorLogLM q T
  let a := dirichletLTwistedSmoothedConductorLogFinalLeft q T
  let b := dirichletLTwistedSmoothedConductorLogRight d
  obtain ⟨hLM, hwidth⟩ := conductorLog_parameters_pos (q := q) hT
  change 0 < LM at hLM
  have ha : (1 / 2 : ℝ) < a := by
    simpa only [a] using one_half_lt_conductorLogFinalLeft (q := q) hT
  have hab : a ≤ b := by
    dsimp only [a, b, dirichletLTwistedSmoothedConductorLogFinalLeft,
      dirichletLTwistedSmoothedConductorLogRight]
    linarith
  have hb2 : b ≤ 2 := by
    simp only [b, dirichletLTwistedSmoothedConductorLogRight]
    linarith
  have hX0 : 0 < X := lt_of_lt_of_le zero_lt_one hX
  have hT0 : 0 < T := lt_of_lt_of_le (by norm_num) hT
  have verticalPoint (t : ℝ) (ht : |t| ≤ T) :
      ‖DirichletCharacter.twistedSmoothedPerronIntegrand χ ν ε X (a + t * I)‖ ≤
        2251799813685248 * LM ^ 11 * (4 * A / ε) * X ^ a := by
    have hlog := norm_logDeriv_LFunction_le_on_conductorLogEdgeRectangle
      χ hχsq hT hd hd1 ht (le_refl a) hab
    have hm := hMellin (1 / 2) (by norm_num) (a + t * I)
      (by simp; norm_num at ha ⊢; exact ha.le)
      (by simp; exact (hab.trans hb2)) ε hε hε1
    have hnormsq : (1 / 4 : ℝ) ≤ ‖(a : ℂ) + t * I‖ ^ 2 := by
      rw [Complex.sq_norm]
      simp [Complex.normSq_apply]
      nlinarith [sq_nonneg t]
    have hinv : (ε * ‖(a : ℂ) + t * I‖ ^ 2)⁻¹ ≤ 4 / ε := by
      rw [mul_inv_rev]
      have hi : (‖(a : ℂ) + t * I‖ ^ 2)⁻¹ ≤ (4 : ℝ) := by
        have := inv_anti₀ (by norm_num : (0 : ℝ) < 1 / 4) hnormsq
        norm_num at this ⊢
        exact this
      calc
        (‖(a : ℂ) + t * I‖ ^ 2)⁻¹ * ε⁻¹ ≤ 4 * ε⁻¹ :=
          mul_le_mul_of_nonneg_right hi (inv_nonneg.mpr hε.le)
        _ = 4 / ε := by rw [div_eq_mul_inv]
    have hm' : ‖𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) (a + t * I)‖ ≤ 4 * A / ε := by
      calc
        _ ≤ A * (ε * ‖(a : ℂ) + t * I‖ ^ 2)⁻¹ := hm
        _ ≤ A * (4 / ε) := mul_le_mul_of_nonneg_left hinv hA.le
        _ = 4 * A / ε := by ring
    have hXnorm : ‖(X : ℂ) ^ ((a : ℂ) + t * I)‖ = X ^ a := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hX0]
      simp
    have hlog' :
        ‖-deriv χ.LFunction (a + t * I) / χ.LFunction (a + t * I)‖ ≤
          2251799813685248 * LM ^ 11 := by
      simpa only [neg_div, norm_neg, LM, mul_comm] using hlog
    dsimp only [DirichletCharacter.twistedSmoothedPerronIntegrand]
    rw [norm_mul, norm_mul, hXnorm]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul hlog' hm' (norm_nonneg _) (by positivity)) (Real.rpow_nonneg hX0.le _)
  have hvertical :
      ‖VIntegral (DirichletCharacter.twistedSmoothedPerronIntegrand χ ν ε X)
          a (-T) T‖ ≤
        (36028797018963968 * A) * T * LM ^ 11 * X ^ a / ε := by
    rw [VIntegral, norm_smul, norm_I, one_mul]
    calc
      ‖∫ t in -T..T,
          DirichletCharacter.twistedSmoothedPerronIntegrand χ ν ε X (a + t * I)‖
          ≤ (2251799813685248 * LM ^ 11 * (4 * A / ε) * X ^ a) *
              |T - (-T)| := by
            apply intervalIntegral.norm_integral_le_of_norm_le_const
            intro t ht
            rw [uIoc_of_le (by linarith)] at ht
            apply verticalPoint t
            rw [abs_le]
            exact ⟨ht.1.le, ht.2⟩
      _ ≤ (36028797018963968 * A) * T * LM ^ 11 * X ^ a / ε := by
        rw [abs_of_nonneg (by linarith)]
        field_simp [hε.ne']
        nlinarith [Real.rpow_nonneg hX0.le a, pow_pos hLM 11]
  have horizontalBound (η : ℝ) (hη : |η| ≤ T) (hηsq : η ^ 2 = T ^ 2) :
      ‖HIntegral (DirichletCharacter.twistedSmoothedPerronIntegrand χ ν ε X)
          a b η‖ ≤
        (36028797018963968 * A) * LM ^ 11 * X ^ (1 + d) /
          (ε * (1 + T ^ 2)) := by
    have ht : |η| = T := by
      nlinarith [sq_abs η, abs_nonneg η]
    have hbound := norm_twistedSmoothedPerron_horizontal_le_of_logDeriv_bound hA.le hε
      (fun s hs hs2 => hMellin (1 / 2) (by norm_num) s hs hs2 ε hε hε1)
      χ ha.le hab hb2 (by linarith) ht hX
      (show 0 ≤ 2251799813685248 * LM ^ 11 by positivity)
      (fun σ hσa hσb => by
        simpa only [LM, mul_comm] using
          norm_logDeriv_LFunction_le_on_conductorLogEdgeRectangle
            χ hχsq hT hd hd1 hη hσa hσb)
    calc
      _ ≤ 4 * A * (2251799813685248 * LM ^ 11) * X ^ b /
          (ε * (1 + T ^ 2)) := hbound
      _ ≤ _ := by
        dsimp only [b, dirichletLTwistedSmoothedConductorLogRight]
        apply div_le_div_of_nonneg_right _ (by positivity)
        nlinarith [mul_nonneg (mul_nonneg hA.le (pow_nonneg hLM.le 11))
          (Real.rpow_nonneg hX0.le (1 + d))]
  simpa only [a, b, LM] using
    ⟨hvertical, horizontalBound T (by simp [abs_of_nonneg hT0.le]) (by rfl),
      horizontalBound (-T) (by rw [abs_neg, abs_of_nonneg hT0.le]) (by ring)⟩

end AnalyticNumberTheory.LargeSieve