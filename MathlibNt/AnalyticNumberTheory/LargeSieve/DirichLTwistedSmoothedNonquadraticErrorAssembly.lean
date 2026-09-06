import MathlibNt.AnalyticNumberTheory.LargeSieve.DirichLTwistedSmoothedRightTailQuantitative
import MathlibNt.AnalyticNumberTheory.LargeSieve.DirichLTwistedSmoothedContourNormBounds

open Set Function Filter Complex Real MeasureTheory

namespace AnalyticNumberTheory.LargeSieve

theorem integral_lower_middle_upper
    (f : ℝ → ℂ) {T : ℝ} (hf : Integrable f) (hT : 0 ≤ T) :
    (∫ t in Iic (-T), f t) + (∫ t in Ioc (-T) T, f t) +
        (∫ t in Ici T, f t) = ∫ t, f t := by
  have h₁ := integral_add_compl (μ := volume) (s := Iic (-T)) measurableSet_Iic hf
  have h₂ := integral_add_compl (μ := volume.restrict (Ioi (-T)))
    (s := Iic T) measurableSet_Iic hf.integrableOn
  rw [integral_Ici_eq_integral_Ioi]
  simp only [compl_Iic] at h₁ h₂
  have hi : Iic T ∩ Ioi (-T) = Ioc (-T) T := by
    ext x
    simp only [mem_inter_iff, mem_Iic, mem_Ioi, mem_Ioc]
    tauto
  have hc : Ioi T ∩ Ioi (-T) = Ioi T := by
    ext x
    simp only [mem_inter_iff, mem_Ioi]
    constructor
    · exact fun hx => hx.1
    · intro hx
      exact ⟨hx, by linarith⟩
  rw [Measure.restrict_restrict measurableSet_Iic,
    Measure.restrict_restrict measurableSet_Ioi] at h₂
  rw [hi, hc] at h₂
  linear_combination h₁ + h₂

/-- Premise-free assembly of the nonquadratic smoothed Perron error.  The three
terms are respectively the final left edge, the two horizontal edges, and the
two tails of the full right vertical line. -/
theorem exists_dirichletLTwistedSmoothedNonquadraticErrorAssembly
    {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν)
    (νpos : ∀ x > 0, 0 ≤ ν x)
    (suppν : support ν ⊆ Icc (1 / 2) 2)
    (mass_one : ∫ x in Ioi (0 : ℝ), ν x / x = 1) :
    ∃ K > 0, ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
      {T d ε X : ℝ}, χ ^ 2 ≠ 1 → 3 ≤ T → 0 < d → d ≤ 1 →
      0 < ε → ε < 1 → 1 ≤ X →
      ‖DirichletCharacter.twistedSmoothedPsi χ ν ε X‖ ≤
        K * (T * (dirichletLTwistedSmoothedConductorLogLM q T) ^ 11 *
              X ^ (dirichletLTwistedSmoothedConductorLogFinalLeft q T) / ε +
          (dirichletLTwistedSmoothedConductorLogLM q T) ^ 11 * X ^ (1 + d) /
              (ε * (1 + T ^ 2)) +
          X ^ (1 + d) * (1 + d⁻¹ ^ 2) / (ε * T)) := by
  obtain ⟨C, hC, hcontour⟩ :=
    exists_dirichletLTwistedSmoothedContourNormBounds diffν suppν
  obtain ⟨c, hc, htails⟩ :=
    DirichletCharacter.twistedSmoothedPerron_right_tails_quantitative
      diffν νpos suppν mass_one
  refine ⟨2 * (C + c), by positivity, ?_⟩
  intro q _ χ T d ε X hχsq hT hd hd1 hε hε1 hX
  let F := DirichletCharacter.twistedSmoothedPerronIntegrand χ ν ε X
  let a := dirichletLTwistedSmoothedConductorLogFinalLeft q T
  let b := dirichletLTwistedSmoothedConductorLogRight d
  let LM := dirichletLTwistedSmoothedConductorLogLM q T
  let A := T * LM ^ 11 * X ^ a / ε
  let B := LM ^ 11 * X ^ (1 + d) / (ε * (1 + T ^ 2))
  let D := X ^ (1 + d) * (1 + d⁻¹ ^ 2) / (ε * T)
  have hX0 : 0 < X := lt_of_lt_of_le zero_lt_one hX
  have hT0 : 0 < T := lt_of_lt_of_le (by norm_num) hT
  have hT1 : 1 ≤ T := by linarith

  have hf : Integrable (fun t : ℝ => F ((b : ℂ) + t * I)) := by
    simpa only [F, b, dirichletLTwistedSmoothedConductorLogRight] using
      (DirichletCharacter.twistedSmoothedPerronIntegrand_integrable_right
        (q := q) (σ := 1 + d) (X := X) (ε := ε) χ diffν νpos suppν mass_one
        hX0 hε hε1 (by linarith) (by linarith))
  have hp := DirichletCharacter.twistedSmoothedPerron χ diffν νpos suppν mass_one
    hX0 hε hε1 (σ := 1 + d) (by linarith) (by linarith)
  have ht := htails χ hd hd1 hε hε1 hX0 hT1
  have hct := hcontour χ hχsq hT hd hd1 hε hε1 hX
  have hshift := dirichletLTwistedSmoothedPerron_conductorLogEdgeFiniteContourIdentity
    χ hχsq hT hd hd1 diffν νpos suppν mass_one hX0 hε hε1
  have hsplit := integral_lower_middle_upper
    (fun t : ℝ => F ((b : ℂ) + t * I)) hf hT0.le
  have htlow : ‖∫ t in Iic (-T), F ((b : ℂ) + t * I)‖ ≤ c * D := by
    dsimp only [F, b, D, dirichletLTwistedSmoothedConductorLogRight]
    convert ht.1 using 1 <;> (try ring)
  have htupper : ‖∫ t in Ici T, F ((b : ℂ) + t * I)‖ ≤ c * D := by
    dsimp only [F, b, D, dirichletLTwistedSmoothedConductorLogRight]
    convert ht.2 using 1 <;> (try ring)
  have hmid :
      ‖∫ t in Ioc (-T) T, F ((b : ℂ) + t * I)‖ =
        ‖VIntegral F b (-T) T‖ := by
    rw [VIntegral, norm_smul, norm_I, one_mul,
      intervalIntegral.integral_of_le (by linarith : -T ≤ T)]
  have hv : ‖VIntegral F b (-T) T‖ ≤ C * A + C * B + C * B := by
    have heq : VIntegral F b (-T) T =
        VIntegral F a (-T) T + HIntegral F a b T - HIntegral F a b (-T) := by
      simpa only [F, a, b] using (by
        linear_combination hshift)
    have hleft : ‖VIntegral F a (-T) T‖ ≤ C * A := by
      dsimp only [F, a, A, LM]
      convert hct.1 using 1 <;> (try ring)
    have htop : ‖HIntegral F a b T‖ ≤ C * B := by
      dsimp only [F, a, b, B, LM]
      convert hct.2.1 using 1 <;> (try ring)
    have hbottom : ‖HIntegral F a b (-T)‖ ≤ C * B := by
      dsimp only [F, a, b, B, LM]
      convert hct.2.2 using 1 <;> (try ring)
    rw [heq]
    calc
      ‖VIntegral F a (-T) T + HIntegral F a b T - HIntegral F a b (-T)‖
          ≤ ‖VIntegral F a (-T) T‖ + ‖HIntegral F a b T‖ +
              ‖HIntegral F a b (-T)‖ := by
            exact (norm_sub_le _ _).trans
              (add_le_add (norm_add_le _ _) (le_refl _))
      _ ≤ C * A + C * B + C * B := by
        exact add_le_add (add_le_add hleft htop) hbottom
  have hfull : ‖∫ t : ℝ, F ((b : ℂ) + t * I)‖ ≤
      c * D + (C * A + C * B + C * B) + c * D := by
    rw [← hsplit]
    calc
      ‖(∫ t in Iic (-T), F ((b : ℂ) + t * I)) +
          (∫ t in Ioc (-T) T, F ((b : ℂ) + t * I)) +
          ∫ t in Ici T, F ((b : ℂ) + t * I)‖
          ≤ ‖∫ t in Iic (-T), F ((b : ℂ) + t * I)‖ +
              ‖∫ t in Ioc (-T) T, F ((b : ℂ) + t * I)‖ +
              ‖∫ t in Ici T, F ((b : ℂ) + t * I)‖ := by
            exact (norm_add_le _ _).trans
              (add_le_add (norm_add_le _ _) (le_refl _))
      _ ≤ c * D + (C * A + C * B + C * B) + c * D := by
        rw [hmid]
        exact add_le_add (add_le_add htlow hv) htupper
  have hnorm : ‖(1 / (2 * (Real.pi : ℂ) * I) : ℂ)‖ ≤ 1 := by
    rw [norm_div, norm_one, norm_mul, norm_mul, Complex.norm_ofNat,
      Complex.norm_real, norm_I]
    norm_num
    rw [abs_of_pos Real.pi_pos]
    have hinv : Real.pi⁻¹ ≤ 1 :=
      (inv_le_one₀ Real.pi_pos).2 (by linarith [Real.pi_gt_three])
    nlinarith [inv_nonneg.mpr Real.pi_pos.le]
  have hnormalized : ‖VerticalIntegral' F b‖ ≤
      ‖∫ t : ℝ, F ((b : ℂ) + t * I)‖ := by
    rw [VerticalIntegral', VerticalIntegral, norm_smul, norm_smul, norm_I, one_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) hnorm
  have hLM0 : 0 < LM := by
    have hM : 4 ≤ dirichletLTwistedSmoothedConductorLogCutoff q T := by
      simpa only [dirichletLTwistedSmoothedConductorLogCutoff] using
        four_le_dirichletLNonquadraticConductorLogCutoff hT
    have hlog : 0 < Real.log (dirichletLTwistedSmoothedConductorLogCutoff q T : ℝ) :=
      Real.log_pos (by exact_mod_cast
        (show 1 < dirichletLTwistedSmoothedConductorLogCutoff q T by omega))
    dsimp only [LM, dirichletLTwistedSmoothedConductorLogLM]
    positivity
  have hA0 : 0 ≤ A := by
    dsimp only [A]
    positivity
  have hB0 : 0 ≤ B := by
    dsimp only [B]
    positivity
  have hD0 : 0 ≤ D := by
    dsimp only [D]
    positivity
  rw [hp]
  change ‖VerticalIntegral' F b‖ ≤ _
  calc
    ‖VerticalIntegral' F b‖ ≤ ‖∫ t : ℝ, F ((b : ℂ) + t * I)‖ := hnormalized
    _ ≤ c * D + (C * A + C * B + C * B) + c * D := hfull
    _ ≤ 2 * (C + c) * (A + B + D) := by
      nlinarith [mul_nonneg hC.le hA0, mul_nonneg hC.le hB0,
        mul_nonneg hC.le hD0, mul_nonneg hc.le hA0,
        mul_nonneg hc.le hB0, mul_nonneg hc.le hD0]
    _ = _ := by rfl

end AnalyticNumberTheory.LargeSieve