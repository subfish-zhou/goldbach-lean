import MathlibNt.AnalyticNumberTheory.LargeSieve.DirichLTwistedSmoothedConductorLogContour

open Set Function Filter Complex Real MeasureTheory
open scoped ArithmeticFunction.Moebius LSeries.notation

namespace AnalyticNumberTheory.LargeSieve

open DirichletLGlobalConductorLogValueBound
open DirichletLGlobalConductorLogDerivativeBound

/-- The final edge width, one quarter of the accepted `2^42` width. -/
noncomputable def dirichletLTwistedSmoothedConductorLogEdgeWidth
    (q : ℕ) (T : ℝ) : ℝ :=
  1 / (4398046511104 * (dirichletLTwistedSmoothedConductorLogLM q T) ^ 9)

/-- The final left edge `1 - w/4`. -/
noncomputable def dirichletLTwistedSmoothedConductorLogFinalLeft
    (q : ℕ) (T : ℝ) : ℝ :=
  1 - dirichletLTwistedSmoothedConductorLogEdgeWidth q T / 4

/-- The variable right edge `1 + d`. -/
def dirichletLTwistedSmoothedConductorLogRight (d : ℝ) : ℝ := 1 + d

/-- The final variable-right rectangle. -/
def dirichletLTwistedSmoothedConductorLogEdgeRectangle
    (q : ℕ) (T d : ℝ) : Set ℂ :=
  ((dirichletLTwistedSmoothedConductorLogFinalLeft q T : ℂ) - I * T).Rectangle
    (dirichletLTwistedSmoothedConductorLogRight d + I * T)

private theorem edge_parameters
    {q : ℕ} [NeZero q] {T : ℝ} (hT : 3 ≤ T) :
    let LM := dirichletLTwistedSmoothedConductorLogLM q T
    let w := dirichletLTwistedSmoothedConductorLogEdgeWidth q T
    1 < LM ∧ 0 < w ∧ w ≤ 1 / 2 := by
  let M := dirichletLTwistedSmoothedConductorLogCutoff q T
  let LM := dirichletLTwistedSmoothedConductorLogLM q T
  let w := dirichletLTwistedSmoothedConductorLogEdgeWidth q T
  have hM : 4 ≤ M := by
    simpa only [M, dirichletLTwistedSmoothedConductorLogCutoff] using
      four_le_dirichletLNonquadraticConductorLogCutoff hT
  have hlogM : 0 < Real.log (M : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < M by omega))
  have hLM : 1 < LM := by
    dsimp only [LM, dirichletLTwistedSmoothedConductorLogLM, M]
    linarith
  have hw : 0 < w := by
    dsimp only [w, dirichletLTwistedSmoothedConductorLogEdgeWidth]
    positivity
  have hw2 : w ≤ 1 / 2 := by
    dsimp only [w, dirichletLTwistedSmoothedConductorLogEdgeWidth]
    rw [div_le_iff₀ (show 0 < 4398046511104 * LM ^ 9 by positivity)]
    have hp : 1 ≤ LM ^ 9 := one_le_pow₀ hLM.le
    nlinarith
  exact ⟨hLM, hw, hw2⟩

/-- The final rectangle is contained in the already accepted quantitative rectangle. -/
theorem dirichletLTwistedSmoothedConductorLogEdgeRectangle_subset
    (q : ℕ) [NeZero q] (T d : ℝ) (hT : 3 ≤ T) (hd0 : 0 < d) (hd1 : d ≤ 1) :
    dirichletLTwistedSmoothedConductorLogEdgeRectangle q T d ⊆
      dirichletLTwistedSmoothedConductorLogRectangle q T := by
  obtain ⟨hLM, hw, hw2⟩ := edge_parameters (q := q) hT
  have hleft : dirichletLTwistedSmoothedConductorLogLeftEdge q T ≤
      dirichletLTwistedSmoothedConductorLogFinalLeft q T := by
    dsimp only [dirichletLTwistedSmoothedConductorLogLeftEdge,
      dirichletLTwistedSmoothedConductorLogLM,
      dirichletLTwistedSmoothedConductorLogFinalLeft]
    change 1 - dirichletLTwistedSmoothedConductorLogEdgeWidth q T ≤
      1 - dirichletLTwistedSmoothedConductorLogEdgeWidth q T / 4
    linarith
  have hfinalright : dirichletLTwistedSmoothedConductorLogFinalLeft q T ≤
      dirichletLTwistedSmoothedConductorLogRight d := by
    dsimp only [dirichletLTwistedSmoothedConductorLogFinalLeft,
      dirichletLTwistedSmoothedConductorLogRight]
    linarith
  have hright : dirichletLTwistedSmoothedConductorLogRight d ≤ 2 := by
    dsimp only [dirichletLTwistedSmoothedConductorLogRight]
    linarith
  have holdright : dirichletLTwistedSmoothedConductorLogLeftEdge q T ≤ 2 :=
    hleft.trans (hfinalright.trans hright)
  intro s hs
  rw [dirichletLTwistedSmoothedConductorLogEdgeRectangle, Complex.Rectangle,
    Complex.mem_reProdIm] at hs
  norm_num at hs
  rw [Set.uIcc_of_le hfinalright] at hs
  rw [dirichletLTwistedSmoothedConductorLogRectangle, Complex.Rectangle,
    Complex.mem_reProdIm]
  norm_num
  rw [Set.uIcc_of_le holdright]
  exact ⟨⟨hleft.trans hs.1.1, hs.1.2.trans hright⟩, hs.2⟩

/-- The complete Perron integrand is holomorphic on every final variable-right rectangle. -/
theorem twistedSmoothedPerronIntegrand_holomorphicOn_conductorLogEdgeRectangle
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {T d : ℝ}
    (hχsq : χ ^ 2 ≠ 1) (hT : 3 ≤ T) (hd0 : 0 < d) (hd1 : d ≤ 1)
    {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν)
    (νpos : ∀ x > 0, 0 ≤ ν x)
    (suppν : support ν ⊆ Icc (1 / 2) 2)
    (mass_one : ∫ x in Ioi (0 : ℝ), ν x / x = 1)
    {X : ℝ} (X_pos : 0 < X) {ε : ℝ} (εpos : 0 < ε) (ε_lt_one : ε < 1) :
    HolomorphicOn (DirichletCharacter.twistedSmoothedPerronIntegrand χ ν ε X)
      (dirichletLTwistedSmoothedConductorLogEdgeRectangle q T d) :=
  (twistedSmoothedPerronIntegrand_holomorphicOn_conductorLogRectangle
    χ hχsq hT diffν νpos suppν mass_one X_pos εpos ε_lt_one).mono
      (dirichletLTwistedSmoothedConductorLogEdgeRectangle_subset
        q T d hT hd0 hd1)

/-- The final variable-right rectangle integral vanishes. -/
theorem dirichletLTwistedSmoothedPerron_conductorLogEdgeRectangleIntegral_eq_zero
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {T d : ℝ}
    (hχsq : χ ^ 2 ≠ 1) (hT : 3 ≤ T) (hd0 : 0 < d) (hd1 : d ≤ 1)
    {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν)
    (νpos : ∀ x > 0, 0 ≤ ν x)
    (suppν : support ν ⊆ Icc (1 / 2) 2)
    (mass_one : ∫ x in Ioi (0 : ℝ), ν x / x = 1)
    {X : ℝ} (X_pos : 0 < X) {ε : ℝ} (εpos : 0 < ε) (ε_lt_one : ε < 1) :
    RectangleIntegral
      (DirichletCharacter.twistedSmoothedPerronIntegrand χ ν ε X)
      ((dirichletLTwistedSmoothedConductorLogFinalLeft q T : ℂ) - I * T)
      (dirichletLTwistedSmoothedConductorLogRight d + I * T) = 0 :=
  (twistedSmoothedPerronIntegrand_holomorphicOn_conductorLogEdgeRectangle
    χ hχsq hT hd0 hd1 diffν νpos suppν mass_one X_pos εpos ε_lt_one).vanishesOnRectangle
      (by rfl)

/-- Finite contour identity with a genuinely variable right edge. -/
theorem dirichletLTwistedSmoothedPerron_conductorLogEdgeFiniteContourIdentity
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {T d : ℝ}
    (hχsq : χ ^ 2 ≠ 1) (hT : 3 ≤ T) (hd0 : 0 < d) (hd1 : d ≤ 1)
    {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν)
    (νpos : ∀ x > 0, 0 ≤ ν x)
    (suppν : support ν ⊆ Icc (1 / 2) 2)
    (mass_one : ∫ x in Ioi (0 : ℝ), ν x / x = 1)
    {X : ℝ} (X_pos : 0 < X) {ε : ℝ} (εpos : 0 < ε) (ε_lt_one : ε < 1) :
    VIntegral (DirichletCharacter.twistedSmoothedPerronIntegrand χ ν ε X)
        (dirichletLTwistedSmoothedConductorLogRight d) (-T) T -
      VIntegral (DirichletCharacter.twistedSmoothedPerronIntegrand χ ν ε X)
        (dirichletLTwistedSmoothedConductorLogFinalLeft q T) (-T) T =
      HIntegral (DirichletCharacter.twistedSmoothedPerronIntegrand χ ν ε X)
        (dirichletLTwistedSmoothedConductorLogFinalLeft q T)
          (dirichletLTwistedSmoothedConductorLogRight d) T -
      HIntegral (DirichletCharacter.twistedSmoothedPerronIntegrand χ ν ε X)
        (dirichletLTwistedSmoothedConductorLogFinalLeft q T)
          (dirichletLTwistedSmoothedConductorLogRight d) (-T) := by
  have hz := dirichletLTwistedSmoothedPerron_conductorLogEdgeRectangleIntegral_eq_zero
    χ hχsq hT hd0 hd1 diffν νpos suppν mass_one X_pos εpos ε_lt_one
  norm_num [RectangleIntegral] at hz
  linear_combination hz

/-- In the absolute-convergence half-plane, the L-value has the elementary
lower bound `(σ - 1) / σ`. -/
theorem norm_dirichletLFunction_ge_sub_one_div
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {σ t : ℝ} (hσ : 1 < σ) :
    (σ - 1) / σ ≤ ‖χ.LFunction (σ + I * t)‖ := by
  let s : ℂ := σ + I * t
  have hs : 1 < s.re := by
    dsimp only [s]
    norm_num
    exact hσ
  have hχsum : LSeriesSummable ↗χ s :=
    DirichletCharacter.LSeriesSummable_of_one_lt_re χ hs
  have hμsum : LSeriesSummable ↗ArithmeticFunction.moebius s :=
    ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs
  have hmul : LSeries ↗χ s *
      LSeries (↗χ * ↗ArithmeticFunction.moebius) s = 1 := by
    rw [← LSeries_convolution' hχsum (DirichletCharacter.LSeriesSummable_mul χ hμsum),
      DirichletCharacter.convolution_mul_moebius, LSeries_delta, Pi.one_apply]
  have hsum : LSeriesSummable (↗χ * ↗ArithmeticFunction.moebius) s :=
    DirichletCharacter.LSeriesSummable_mul χ hμsum
  have hnormsum : ‖LSeries (↗χ * ↗ArithmeticFunction.moebius) s‖ ≤
      1 + 1 / (σ - 1) := by
    have hnorm := norm_tsum_le_tsum_norm hsum.norm
    refine hnorm.trans ((hsum.norm).tsum_le_tsum (fun n => ?_)
      (Real.summable_nat_rpow.mpr (by linarith : -σ < -1)) |>.trans
        (tsum_nat_rpow_neg_le σ hσ))
    by_cases hn : n = 0
    · subst n
      simp [LSeries.term, Real.zero_rpow (by linarith : -σ ≠ 0)]
    · rw [LSeries.term, if_neg hn, norm_div,
        norm_natCast_cpow_of_re_ne_zero n (by
          dsimp only [s]
          norm_num
          linarith)]
      simp only [Pi.mul_apply, norm_mul]
      have hμ : |((ArithmeticFunction.moebius n : ℤ) : ℝ)| ≤ 1 := by
        rcases ArithmeticFunction.moebius_eq_or n with h | h | h <;> simp [h]
      have hχ := χ.norm_le_one n
      norm_num [s]
      calc
        ‖χ n‖ * |((ArithmeticFunction.moebius n : ℤ) : ℝ)| / (n : ℝ) ^ σ
            ≤ 1 / (n : ℝ) ^ σ := by
              apply div_le_div_of_nonneg_right
              · simpa only [one_mul] using
                  (mul_le_mul hχ hμ (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1))
              · positivity
        _ = (n : ℝ) ^ (-σ) := by
          rw [Real.rpow_neg (Nat.cast_nonneg n)]
          simp only [one_div]
  rw [DirichletCharacter.LFunction_eq_LSeries χ hs]
  have hprod : ‖LSeries ↗χ s‖ * ‖LSeries (↗χ * ↗ArithmeticFunction.moebius) s‖ = 1 := by
    rw [← norm_mul, hmul, norm_one]
  have hσ0 : 0 < σ := lt_trans zero_lt_one hσ
  have hd : 0 < σ - 1 := sub_pos.mpr hσ
  have hmajor : 1 + 1 / (σ - 1) = σ / (σ - 1) := by field_simp; ring
  rw [hmajor] at hnormsum
  have hscaled := mul_le_mul_of_nonneg_left hnormsum (norm_nonneg (LSeries ↗χ s))
  rw [hprod] at hscaled
  have hscaled' : 1 ≤ ‖LSeries ↗χ s‖ * σ / (σ - 1) := by
    simpa only [mul_div_assoc] using hscaled
  have hscaled'' : σ - 1 ≤ ‖LSeries ↗χ s‖ * σ := by
    simpa only [one_mul] using (le_div_iff₀ hd).mp hscaled'
  rw [div_le_iff₀ hσ0]
  simpa only [mul_comm] using hscaled''

/-- Uniform `2^51 LM^11` logarithmic-derivative bound on the entire final
rectangle.  The left branch is anchored at `1-w/4` and uses the sharp
derivative estimate over a segment of length at most `w/2`; the right branch
uses the quantitative absolute-convergence lower bound. -/
theorem norm_logDeriv_LFunction_le_on_conductorLogEdgeRectangle
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {T d η σ : ℝ}
    (hχsq : χ ^ 2 ≠ 1) (hT : 3 ≤ T) (hd0 : 0 < d) (hd1 : d ≤ 1)
    (hη : |η| ≤ T)
    (hσleft : dirichletLTwistedSmoothedConductorLogFinalLeft q T ≤ σ)
    (hσright : σ ≤ dirichletLTwistedSmoothedConductorLogRight d) :
    ‖deriv χ.LFunction (σ + I * η) / χ.LFunction (σ + I * η)‖ ≤
      2251799813685248 * (dirichletLTwistedSmoothedConductorLogLM q T) ^ 11 := by
  let m := dirichletLConductorHeightCutoff q η
  let M := dirichletLTwistedSmoothedConductorLogCutoff q T
  let Lm : ℝ := 1 + Real.log m
  let LM : ℝ := 1 + Real.log M
  let w : ℝ := 1 / (4398046511104 * LM ^ 9)
  let a : ℝ := 1 - w / 4
  have hχ : χ ≠ 1 := by
    intro h
    apply hχsq
    rw [h, one_pow]
  have hm : 2 ≤ m := by
    simpa only [m] using two_le_conductorHeightCutoff χ hχ η
  have hM : 4 ≤ M := by
    simpa only [M, dirichletLTwistedSmoothedConductorLogCutoff] using
      four_le_dirichletLNonquadraticConductorLogCutoff hT
  have hmM : m ≤ M := by
    simpa only [m, M, dirichletLTwistedSmoothedConductorLogCutoff] using
      dirichletLConductorHeightCutoff_le_fixedHeightCutoff hη
  have hlogm : 0 < Real.log (m : ℝ) := by
    simpa only [m] using log_conductorHeightCutoff_pos χ hχ η
  have hlogle : Real.log (m : ℝ) ≤ Real.log (M : ℝ) :=
    Real.log_le_log (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hm))
      (by exact_mod_cast hmM)
  have hLm : 1 < Lm := by dsimp only [Lm]; linarith
  have hLM : 1 < LM := by dsimp only [LM]; linarith
  have hLmLM : Lm ≤ LM := by dsimp only [Lm, LM]; linarith
  have hw : 0 < w := by dsimp only [w]; positivity
  have hw2 : w ≤ 1 / 2 := by
    dsimp only [w]
    rw [div_le_iff₀ (show 0 < 4398046511104 * LM ^ 9 by positivity)]
    nlinarith [one_le_pow₀ hLM.le (n := 9)]
  have hxlog : 1 / (4398046511104 * Lm ^ 9) ≤ 1 / Real.log m := by
    have hlogLm : Real.log (m : ℝ) < Lm := by dsimp only [Lm]; linarith
    calc
      1 / (4398046511104 * Lm ^ 9) ≤ 1 / Lm := by
        rw [one_div_le_one_div (by positivity) (by positivity)]
        have hp : Lm ≤ Lm ^ 9 := by
          calc Lm = Lm ^ 1 := by ring
               _ ≤ Lm ^ 9 := pow_le_pow_right₀ hLm.le (by norm_num)
        nlinarith [pow_pos (by linarith : 0 < Lm) 9]
      _ ≤ 1 / Real.log m := one_div_le_one_div_of_le hlogm hlogLm.le
  have hwlocal : w ≤ 1 / (4398046511104 * Lm ^ 9) := by
    dsimp only [w]
    apply one_div_le_one_div_of_le (by positivity)
    gcongr
  have ha_def : a = dirichletLTwistedSmoothedConductorLogFinalLeft q T := by
    rfl
  have ha_half : 1 / 2 ≤ a := by dsimp only [a]; linarith
  have ha_one : a < 1 := by dsimp only [a]; linarith
  have ha_strip : a ∈ Set.Ico
      (1 - 1 / (4398046511104 * Lm ^ 9)) 1 := by
    refine ⟨?_, ha_one⟩
    dsimp only [a]
    linarith
  have hanchorRaw : 128 * Lm ^ 2 *
      (1 / (4398046511104 * Lm ^ 9)) ≤ ‖χ.LFunction (a + I * η)‖ := by
    simpa only [Lm, m] using
      norm_LFunction_lower_of_nonquadratic_conductorLog χ hχsq ha_strip
  have hinv7 : 1 / (4398046511104 * LM ^ 7) ≤
      1 / (4398046511104 * Lm ^ 7) := by
    apply one_div_le_one_div_of_le (by positivity)
    gcongr
  have hanchor : 128 * LM ^ 2 * w ≤ ‖χ.LFunction (a + I * η)‖ := by
    have hlocalId : 128 * Lm ^ 2 *
        (1 / (4398046511104 * Lm ^ 9)) =
        128 * (1 / (4398046511104 * Lm ^ 7)) := by
      field_simp [ne_of_gt hLm]
    have hglobalId : 128 * LM ^ 2 * w =
        128 * (1 / (4398046511104 * LM ^ 7)) := by
      dsimp only [w]
      field_simp [ne_of_gt hLM]
    rw [hglobalId]
    calc
      128 * (1 / (4398046511104 * LM ^ 7)) ≤
          128 * (1 / (4398046511104 * Lm ^ 7)) :=
        mul_le_mul_of_nonneg_left hinv7 (by norm_num)
      _ = 128 * Lm ^ 2 * (1 / (4398046511104 * Lm ^ 9)) := hlocalId.symm
      _ ≤ ‖χ.LFunction (a + I * η)‖ := hanchorRaw
  have hσtwo : σ ≤ 2 := by
    dsimp only [dirichletLTwistedSmoothedConductorLogRight] at hσright
    linarith
  have hnearσ : 1 - 1 / Real.log m ≤ σ := by
    have ha_near : 1 - 1 / Real.log m ≤ a := by
      dsimp only [a]
      linarith
    exact ha_near.trans (ha_def ▸ hσleft)
  have hderiv : ‖deriv χ.LFunction (σ + I * η)‖ ≤ 64 * LM ^ 2 := by
    have hd := norm_deriv_LFunction_le_sixtyfour_mul_one_add_log_sq_conductorHeightCutoff
      χ hχ (σ := σ) (t := η) (ha_half.trans (ha_def ▸ hσleft)) hσtwo
      (by simpa only [m] using hnearσ)
    calc
      _ ≤ 64 * Lm ^ 2 := by simpa only [Lm, m] using hd
      _ ≤ 64 * LM ^ 2 := by gcongr
  by_cases hbranch : σ ≤ 1 + w / 4
  · have haσ : a ≤ σ := by simpa only [ha_def] using hσleft
    have hdist : σ - a ≤ w / 2 := by dsimp only [a] at *; linarith
    have hdiff : ‖χ.LFunction (σ + I * η) - χ.LFunction (a + I * η)‖ ≤
        64 * LM ^ 2 * (σ - a) := by
      have heq := DirichletLWeakStripDifferenceBound.integral_deriv_LFunction_eq_sub
        χ hχ a σ η
      have heq' : (∫ u in a..σ, deriv χ.LFunction (u + I * η)) =
          χ.LFunction (σ + I * η) - χ.LFunction (a + I * η) := by
        simpa only [mul_comm] using heq
      rw [← heq']
      convert intervalIntegral.norm_integral_le_of_norm_le_const ?_ using 1
      · rw [_root_.abs_of_nonneg (sub_nonneg.mpr haσ)]
      · intro u hu
        rw [uIoc_of_le haσ, mem_Ioc] at hu
        have hunear : 1 - 1 / Real.log m ≤ u := by
          have ha_near : 1 - 1 / Real.log m ≤ a := by
            dsimp only [a]
            linarith
          exact ha_near.trans hu.1.le
        have huupper : u ≤ 2 := hu.2.trans hσtwo
        have hd := norm_deriv_LFunction_le_sixtyfour_mul_one_add_log_sq_conductorHeightCutoff
          χ hχ (σ := u) (t := η) (ha_half.trans hu.1.le) huupper
          (by simpa only [m] using hunear)
        calc
          _ ≤ 64 * Lm ^ 2 := by simpa only [Lm, m] using hd
          _ ≤ 64 * LM ^ 2 := by gcongr
    have hdiff' : ‖χ.LFunction (σ + I * η) - χ.LFunction (a + I * η)‖ ≤
        32 * LM ^ 2 * w := by
      calc
        _ ≤ 64 * LM ^ 2 * (σ - a) := hdiff
        _ ≤ 64 * LM ^ 2 * (w / 2) := by gcongr
        _ = 32 * LM ^ 2 * w := by ring
    have hlower : 96 * LM ^ 2 * w ≤ ‖χ.LFunction (σ + I * η)‖ := by
      have htri : ‖χ.LFunction (a + I * η)‖ ≤
          ‖χ.LFunction (σ + I * η) - χ.LFunction (a + I * η)‖ +
            ‖χ.LFunction (σ + I * η)‖ := by
        simpa only [sub_add_cancel, norm_sub_rev] using norm_add_le
          (χ.LFunction (a + I * η) - χ.LFunction (σ + I * η))
          (χ.LFunction (σ + I * η))
      rw [norm_sub_rev] at hdiff'
      nlinarith
    have hden : 0 < 96 * LM ^ 2 * w := by positivity
    rw [norm_div]
    calc
      _ ≤ (64 * LM ^ 2) / (96 * LM ^ 2 * w) :=
        div_le_div₀ (by positivity) hderiv hden hlower
      _ ≤ 2251799813685248 * LM ^ 11 := by
        dsimp only [w]
        field_simp [ne_of_gt hLM]
        nlinarith [one_le_pow₀ hLM.le (n := 11)]
      _ = 2251799813685248 *
          (dirichletLTwistedSmoothedConductorLogLM q T) ^ 11 := by rfl
  · have hσthreshold : 1 + w / 4 < σ := lt_of_not_ge hbranch
    have hrhp := norm_dirichletLFunction_ge_sub_one_div χ (t := η)
      (by linarith : 1 < σ)
    have hlower : w / 8 ≤ ‖χ.LFunction (σ + I * η)‖ := by
      have hσpos : 0 < σ := by linarith
      have hratio : w / 8 ≤ (σ - 1) / σ := by
        rw [div_le_div_iff₀ (by norm_num) hσpos]
        nlinarith
      exact hratio.trans hrhp
    have hden : 0 < w / 8 := by positivity
    rw [norm_div]
    calc
      _ ≤ (64 * LM ^ 2) / (w / 8) :=
        div_le_div₀ (by positivity) hderiv hden hlower
      _ = 2251799813685248 * LM ^ 11 := by
        dsimp only [w]
        field_simp [ne_of_gt hLM]
        ring
      _ = 2251799813685248 *
          (dirichletLTwistedSmoothedConductorLogLM q T) ^ 11 := by rfl

 end AnalyticNumberTheory.LargeSieve
