import MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLTwistedSmoothedPerron
import MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLNonquadraticConductorLogRectangle
import MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLGlobalNonquadraticConductorLogDerivative

open Set Function Filter Complex Real MeasureTheory

namespace AnalyticNumberTheory.LargeSieve

open DirichletLGlobalConductorLogValueBound

/-- The fixed cutoff used by the quantitative conductor-logarithmic contour. -/
noncomputable def dirichletLTwistedSmoothedConductorLogCutoff (q : ℕ) (T : ℝ) : ℕ :=
  dirichletLNonquadraticConductorLogCutoff q T

/-- `1 + log M(q,T)`, kept as a named contour parameter. -/
noncomputable def dirichletLTwistedSmoothedConductorLogLM (q : ℕ) (T : ℝ) : ℝ :=
  1 + Real.log (dirichletLTwistedSmoothedConductorLogCutoff q T)

/-- The quantitative `2^42` left edge. -/
noncomputable def dirichletLTwistedSmoothedConductorLogLeftEdge
    (q : ℕ) (T : ℝ) : ℝ :=
  1 - 1 / (4398046511104 *
    (dirichletLTwistedSmoothedConductorLogLM q T) ^ 9)

/-- The closed quantitative contour rectangle from the `2^42` edge to `2`. -/
def dirichletLTwistedSmoothedConductorLogRectangle (q : ℕ) (T : ℝ) : Set ℂ :=
  ((dirichletLTwistedSmoothedConductorLogLeftEdge q T : ℂ) - I * T).Rectangle
    (2 + I * T)

/-- At height at least three, the quantitative edge lies strictly right of `1/2`. -/
theorem one_half_lt_dirichletLTwistedSmoothedConductorLogLeftEdge
    {q : ℕ} [NeZero q] {T : ℝ} (hT : 3 ≤ T) :
    (1 / 2 : ℝ) < dirichletLTwistedSmoothedConductorLogLeftEdge q T := by
  let M := dirichletLTwistedSmoothedConductorLogCutoff q T
  let LM : ℝ := 1 + Real.log M
  have hM : 4 ≤ M := by
    simpa only [M, dirichletLTwistedSmoothedConductorLogCutoff] using
      four_le_dirichletLNonquadraticConductorLogCutoff hT
  have hlogM : 0 < Real.log (M : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < M by omega))
  have hLM : 1 < LM := by dsimp only [LM]; linarith
  have hLMpow : 1 ≤ LM ^ 9 := one_le_pow₀ hLM.le
  have hden : (2 : ℝ) < 4398046511104 * LM ^ 9 := by nlinarith
  have hwidth : 1 / (4398046511104 * LM ^ 9) < (1 / 2 : ℝ) :=
    one_div_lt_one_div_of_lt (by norm_num) hden
  dsimp only [dirichletLTwistedSmoothedConductorLogLeftEdge,
    dirichletLTwistedSmoothedConductorLogLM, LM, M] at hwidth ⊢
  linarith

/-- The quantitative edge lies strictly left of one. -/
theorem dirichletLTwistedSmoothedConductorLogLeftEdge_lt_one
    {q : ℕ} [NeZero q] {T : ℝ} (hT : 3 ≤ T) :
    dirichletLTwistedSmoothedConductorLogLeftEdge q T < 1 := by
  let M := dirichletLTwistedSmoothedConductorLogCutoff q T
  let LM : ℝ := 1 + Real.log M
  have hM : 4 ≤ M := by
    simpa only [M, dirichletLTwistedSmoothedConductorLogCutoff] using
      four_le_dirichletLNonquadraticConductorLogCutoff hT
  have hlogM : 0 < Real.log (M : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < M by omega))
  have hLM : 0 < LM := by dsimp only [LM]; linarith
  have hwidth : 0 < 1 / (4398046511104 * LM ^ 9) := by positivity
  dsimp only [dirichletLTwistedSmoothedConductorLogLeftEdge,
    dirichletLTwistedSmoothedConductorLogLM, LM, M]
  linarith

/-- The `2^42` contour is contained in the accepted `2^38` zero-free rectangle. -/
theorem dirichletLTwistedSmoothedConductorLogRectangle_subset
    (q : ℕ) [NeZero q] (T : ℝ) (hT : 3 ≤ T) :
    dirichletLTwistedSmoothedConductorLogRectangle q T ⊆
      dirichletLNonquadraticConductorLogRectangle q T := by
  let M := dirichletLTwistedSmoothedConductorLogCutoff q T
  let LM : ℝ := 1 + Real.log M
  have hM : 4 ≤ M := by
    simpa only [M, dirichletLTwistedSmoothedConductorLogCutoff] using
      four_le_dirichletLNonquadraticConductorLogCutoff hT
  have hlogM : 0 < Real.log (M : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < M by omega))
  have hLM : 0 < LM := by dsimp only [LM]; linarith
  have hnewDen : 0 < (4398046511104 : ℝ) * LM ^ 9 := by positivity
  have holdDen : 0 < (274877906944 : ℝ) * LM ^ 9 := by positivity
  have hdenle : (274877906944 : ℝ) * LM ^ 9 ≤ 4398046511104 * LM ^ 9 := by
    nlinarith [pow_pos hLM 9]
  have hwidth : 1 / (4398046511104 * LM ^ 9) ≤
      1 / (274877906944 * LM ^ 9) :=
    one_div_le_one_div_of_le holdDen hdenle
  have hedges : dirichletLNonquadraticConductorLogLeftEdge q T ≤
      dirichletLTwistedSmoothedConductorLogLeftEdge q T := by
    dsimp only [dirichletLNonquadraticConductorLogLeftEdge,
      dirichletLTwistedSmoothedConductorLogLeftEdge,
      dirichletLTwistedSmoothedConductorLogLM, LM, M,
      dirichletLTwistedSmoothedConductorLogCutoff] at hwidth ⊢
    linarith
  have hnewTwo : dirichletLTwistedSmoothedConductorLogLeftEdge q T ≤ 2 := by
    linarith [dirichletLTwistedSmoothedConductorLogLeftEdge_lt_one
      (q := q) (T := T) hT]
  have holdTwo : dirichletLNonquadraticConductorLogLeftEdge q T ≤ 2 :=
    hedges.trans hnewTwo
  intro s hs
  rw [dirichletLTwistedSmoothedConductorLogRectangle, Complex.Rectangle,
    Complex.mem_reProdIm] at hs
  norm_num at hs
  rw [Set.uIcc_of_le hnewTwo] at hs
  rw [dirichletLNonquadraticConductorLogRectangle, Complex.Rectangle,
    Complex.mem_reProdIm]
  norm_num
  rw [Set.uIcc_of_le holdTwo]
  exact ⟨⟨hedges.trans hs.1.1, hs.1.2⟩, hs.2⟩

/-- The logarithmic derivative is holomorphic on the quantitative contour. -/
theorem logDerivative_holomorphicOn_dirichletLTwistedSmoothedConductorLogRectangle
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {T : ℝ}
    (hχsq : χ ^ 2 ≠ 1) (hT : 3 ≤ T) :
    HolomorphicOn (fun s => deriv χ.LFunction s / χ.LFunction s)
      (dirichletLTwistedSmoothedConductorLogRectangle q T) :=
  (logDerivative_holomorphicOn_nonquadratic_conductorLogRectangle χ hχsq hT).mono
    (dirichletLTwistedSmoothedConductorLogRectangle_subset q T hT)

/-- The complete smoothed Perron integrand is holomorphic on the quantitative contour. -/
theorem twistedSmoothedPerronIntegrand_holomorphicOn_conductorLogRectangle
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {T : ℝ}
    (hχsq : χ ^ 2 ≠ 1) (hT : 3 ≤ T)
    {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν)
    (νpos : ∀ x > 0, 0 ≤ ν x)
    (suppν : support ν ⊆ Icc (1 / 2) 2)
    (mass_one : ∫ x in Ioi (0 : ℝ), ν x / x = 1)
    {X : ℝ} (X_pos : 0 < X) {ε : ℝ} (εpos : 0 < ε) (ε_lt_one : ε < 1) :
    HolomorphicOn (DirichletCharacter.twistedSmoothedPerronIntegrand χ ν ε X)
      (dirichletLTwistedSmoothedConductorLogRectangle q T) := by
  have hlog : HolomorphicOn
      (fun s => -deriv χ.LFunction s / χ.LFunction s)
      (dirichletLTwistedSmoothedConductorLogRectangle q T) := by
    rw [(by
      ext s
      simp only [Pi.neg_apply, neg_div] :
      (fun s => -deriv χ.LFunction s / χ.LFunction s) =
        -(fun s => deriv χ.LFunction s / χ.LFunction s))]
    exact (logDerivative_holomorphicOn_dirichletLTwistedSmoothedConductorLogRectangle
      χ hχsq hT).neg
  apply DifferentiableOn.mul
  · apply DifferentiableOn.mul hlog
    intro s hs
    apply DifferentiableAt.differentiableWithinAt
    apply Smooth1MellinDifferentiable diffν suppν ⟨εpos, ε_lt_one⟩ νpos mass_one
    rw [dirichletLTwistedSmoothedConductorLogRectangle, Complex.Rectangle,
      Complex.mem_reProdIm] at hs
    norm_num at hs
    rw [Set.uIcc_of_le (by
      linarith [dirichletLTwistedSmoothedConductorLogLeftEdge_lt_one
        (q := q) (T := T) hT])] at hs
    have hedge : (1 / 2 : ℝ) <
        dirichletLTwistedSmoothedConductorLogLeftEdge q T :=
      one_half_lt_dirichletLTwistedSmoothedConductorLogLeftEdge
        (q := q) (T := T) hT
    exact lt_of_lt_of_le (by linarith : (0 : ℝ) <
      dirichletLTwistedSmoothedConductorLogLeftEdge q T) hs.1.1
  · intro s _
    apply DifferentiableAt.differentiableWithinAt
    apply DifferentiableAt.const_cpow (by fun_prop)
    left
    norm_cast
    exact ne_of_gt X_pos

/-- Along the left edge, the local `2^42` strip estimate is uniform in `|t| ≤ T`. -/
theorem norm_logDeriv_LFunction_le_on_conductorLogLeftEdge
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {T t : ℝ}
    (hχsq : χ ^ 2 ≠ 1) (_hT : 3 ≤ T) (ht : |t| ≤ T) :
    ‖deriv χ.LFunction
        (dirichletLTwistedSmoothedConductorLogLeftEdge q T + I * t) /
      χ.LFunction
        (dirichletLTwistedSmoothedConductorLogLeftEdge q T + I * t)‖ ≤
      2199023255552 *
        (dirichletLTwistedSmoothedConductorLogLM q T) ^ 9 := by
  let m := dirichletLConductorHeightCutoff q t
  let M := dirichletLTwistedSmoothedConductorLogCutoff q T
  let Lm : ℝ := 1 + Real.log m
  let LM : ℝ := 1 + Real.log M
  have hχ : χ ≠ 1 := by
    intro hχ
    apply hχsq
    rw [hχ, one_pow]
  have hm : 2 ≤ m := by
    simpa only [m] using two_le_conductorHeightCutoff χ hχ t
  have hmM : m ≤ M := by
    simpa only [m, M, dirichletLTwistedSmoothedConductorLogCutoff] using
      dirichletLConductorHeightCutoff_le_fixedHeightCutoff ht
  have hlogm : 0 < Real.log (m : ℝ) := by
    simpa only [m] using log_conductorHeightCutoff_pos χ hχ t
  have hlogle : Real.log (m : ℝ) ≤ Real.log (M : ℝ) :=
    Real.log_le_log (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hm))
      (by exact_mod_cast hmM)
  have hLm : 0 < Lm := by dsimp only [Lm]; linarith
  have hLM : 0 < LM := by dsimp only [LM]; linarith
  have hpowle : Lm ^ 9 ≤ LM ^ 9 := by
    apply pow_le_pow_left₀ hLm.le
    · dsimp only [Lm, LM]
      linarith
  have hdenle : 4398046511104 * Lm ^ 9 ≤ 4398046511104 * LM ^ 9 := by
    gcongr
  have hlocalDen : 0 < (4398046511104 : ℝ) * Lm ^ 9 := by positivity
  have hwidth : 1 / (4398046511104 * LM ^ 9) ≤
      1 / (4398046511104 * Lm ^ 9) :=
    one_div_le_one_div_of_le hlocalDen hdenle
  have hleftOne : dirichletLTwistedSmoothedConductorLogLeftEdge q T < 1 := by
    dsimp only [dirichletLTwistedSmoothedConductorLogLeftEdge,
      dirichletLTwistedSmoothedConductorLogLM, LM, M]
    have : 0 < 1 / (4398046511104 * LM ^ 9) := by positivity
    linarith
  have hstrip : dirichletLTwistedSmoothedConductorLogLeftEdge q T ∈ Set.Ico
      (1 - 1 / (4398046511104 *
        (1 + Real.log (dirichletLConductorHeightCutoff q t)) ^ 9)) 1 := by
    refine ⟨?_, hleftOne⟩
    have := sub_le_sub_left hwidth 1
    simpa only [dirichletLTwistedSmoothedConductorLogLeftEdge,
      dirichletLTwistedSmoothedConductorLogLM, LM, Lm, M, m] using this
  have hlocal :=
    norm_logDeriv_LFunction_le_of_nonquadratic_conductorLog χ hχsq hstrip
  calc
    _ ≤ 2199023255552 * Lm ^ 9 := by simpa only [Lm, m] using hlocal
    _ ≤ 2199023255552 * LM ^ 9 := by gcongr
    _ = 2199023255552 *
        (dirichletLTwistedSmoothedConductorLogLM q T) ^ 9 := by
      rfl

/-- The complete integral around the quantitative rectangle vanishes. -/
theorem dirichletLTwistedSmoothedPerron_conductorLogRectangleIntegral_eq_zero
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {T : ℝ}
    (hχsq : χ ^ 2 ≠ 1) (hT : 3 ≤ T)
    {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν)
    (νpos : ∀ x > 0, 0 ≤ ν x)
    (suppν : support ν ⊆ Icc (1 / 2) 2)
    (mass_one : ∫ x in Ioi (0 : ℝ), ν x / x = 1)
    {X : ℝ} (X_pos : 0 < X) {ε : ℝ} (εpos : 0 < ε) (ε_lt_one : ε < 1) :
    RectangleIntegral
      (DirichletCharacter.twistedSmoothedPerronIntegrand χ ν ε X)
      ((dirichletLTwistedSmoothedConductorLogLeftEdge q T : ℂ) - I * T)
      (2 + I * T) = 0 :=
  (twistedSmoothedPerronIntegrand_holomorphicOn_conductorLogRectangle
    χ hχsq hT diffν νpos suppν mass_one X_pos εpos ε_lt_one).vanishesOnRectangle
      (by rfl)

/-- Finite contour identity: `V₂ - V_left = H_top - H_bottom`. -/
theorem dirichletLTwistedSmoothedPerron_conductorLogFiniteContourIdentity
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {T : ℝ}
    (hχsq : χ ^ 2 ≠ 1) (hT : 3 ≤ T)
    {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν)
    (νpos : ∀ x > 0, 0 ≤ ν x)
    (suppν : support ν ⊆ Icc (1 / 2) 2)
    (mass_one : ∫ x in Ioi (0 : ℝ), ν x / x = 1)
    {X : ℝ} (X_pos : 0 < X) {ε : ℝ} (εpos : 0 < ε) (ε_lt_one : ε < 1) :
    VIntegral (DirichletCharacter.twistedSmoothedPerronIntegrand χ ν ε X)
        2 (-T) T -
      VIntegral (DirichletCharacter.twistedSmoothedPerronIntegrand χ ν ε X)
        (dirichletLTwistedSmoothedConductorLogLeftEdge q T) (-T) T =
      HIntegral (DirichletCharacter.twistedSmoothedPerronIntegrand χ ν ε X)
        (dirichletLTwistedSmoothedConductorLogLeftEdge q T) 2 T -
      HIntegral (DirichletCharacter.twistedSmoothedPerronIntegrand χ ν ε X)
        (dirichletLTwistedSmoothedConductorLogLeftEdge q T) 2 (-T) := by
  have hz := dirichletLTwistedSmoothedPerron_conductorLogRectangleIntegral_eq_zero
    χ hχsq hT diffν νpos suppν mass_one X_pos εpos ε_lt_one
  norm_num [RectangleIntegral] at hz
  linear_combination hz

end AnalyticNumberTheory.LargeSieve