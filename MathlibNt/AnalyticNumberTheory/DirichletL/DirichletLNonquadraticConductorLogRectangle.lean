import MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLGlobalNonquadraticConductorLogZeroFree

open Complex Set

namespace AnalyticNumberTheory.LargeSieve

open DirichletLGlobalConductorLogValueBound

/-- The fixed integral height block attached to a height bound `T`. -/
noncomputable def dirichletLNonquadraticConductorLogHeightBlock (T : ℝ) : ℕ :=
  ⌊T⌋₊ + 1

/-- The fixed-height conductor cutoff `M(q,T) = q * (⌊T⌋₊ + 1)`. -/
noncomputable def dirichletLNonquadraticConductorLogCutoff (q : ℕ) (T : ℝ) : ℕ :=
  q * dirichletLNonquadraticConductorLogHeightBlock T

/-- The left edge associated with the fixed conductor-height cutoff. -/
noncomputable def dirichletLNonquadraticConductorLogLeftEdge (q : ℕ) (T : ℝ) : ℝ :=
  1 - 1 / (274877906944 *
    (1 + Real.log (dirichletLNonquadraticConductorLogCutoff q T)) ^ 9)

/-- The closed fixed-height rectangle, extending to real part `2` and heights `±T`. -/
def dirichletLNonquadraticConductorLogRectangle (q : ℕ) (T : ℝ) : Set ℂ :=
  ((dirichletLNonquadraticConductorLogLeftEdge q T : ℂ) - I * T).Rectangle
    (2 + I * T)

lemma dirichletLHeightBlock_le_fixedHeightBlock {t T : ℝ} (ht : |t| ≤ T) :
    dirichletLHeightBlock t ≤ dirichletLNonquadraticConductorLogHeightBlock T := by
  unfold dirichletLHeightBlock dirichletLNonquadraticConductorLogHeightBlock
  exact Nat.add_le_add_right (Nat.floor_mono ht) 1

lemma dirichletLConductorHeightCutoff_le_fixedHeightCutoff
    {q : ℕ} {t T : ℝ} (ht : |t| ≤ T) :
    dirichletLConductorHeightCutoff q t ≤
      dirichletLNonquadraticConductorLogCutoff q T := by
  unfold dirichletLConductorHeightCutoff dirichletLNonquadraticConductorLogCutoff
  exact Nat.mul_le_mul_left q (dirichletLHeightBlock_le_fixedHeightBlock ht)

lemma four_le_dirichletLNonquadraticConductorLogCutoff
    {q : ℕ} [NeZero q] {T : ℝ} (hT : 3 ≤ T) :
    4 ≤ dirichletLNonquadraticConductorLogCutoff q T := by
  have hfloor : 3 ≤ ⌊T⌋₊ := Nat.le_floor hT
  have hq : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  unfold dirichletLNonquadraticConductorLogCutoff
  have hblock : 4 ≤ dirichletLNonquadraticConductorLogHeightBlock T := by
    unfold dirichletLNonquadraticConductorLogHeightBlock
    omega
  nlinarith

/-- The fixed left edge is explicitly to the right of `1/2`. -/
theorem one_half_lt_dirichletLNonquadraticConductorLogLeftEdge
    {q : ℕ} [NeZero q] {T : ℝ} (hT : 3 ≤ T) :
    (1 / 2 : ℝ) < dirichletLNonquadraticConductorLogLeftEdge q T := by
  let M := dirichletLNonquadraticConductorLogCutoff q T
  let L : ℝ := 1 + Real.log M
  have hM : 4 ≤ M := by
    simpa only [M] using four_le_dirichletLNonquadraticConductorLogCutoff hT
  have hlogM : 0 < Real.log (M : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < M by omega))
  have hL : 1 < L := by dsimp only [L]; linarith
  have hLpow : 1 ≤ L ^ 9 := one_le_pow₀ hL.le
  have hden : (2 : ℝ) < 274877906944 * L ^ 9 := by nlinarith
  have hwidth : 1 / (274877906944 * L ^ 9) < (1 / 2 : ℝ) :=
    one_div_lt_one_div_of_lt (by norm_num) hden
  dsimp only [dirichletLNonquadraticConductorLogLeftEdge, L, M] at hwidth ⊢
  linarith

/-- Every nonquadratic Dirichlet L-function is zero-free on the fixed-height
conductor-logarithmic rectangle. -/
theorem LFunction_ne_zero_on_nonquadratic_conductorLogRectangle
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {T : ℝ}
    (hχsq : χ ^ 2 ≠ 1) (hT : 3 ≤ T) :
    ∀ s ∈ dirichletLNonquadraticConductorLogRectangle q T, χ.LFunction s ≠ 0 := by
  intro s hs
  have hχ : χ ≠ 1 := by
    intro hχ
    apply hχsq
    rw [hχ, one_pow]
  have hcoords :
      s.re ∈ Set.uIcc (dirichletLNonquadraticConductorLogLeftEdge q T) 2 ∧
        s.im ∈ Set.uIcc (-T) T := by
    rw [dirichletLNonquadraticConductorLogRectangle, Complex.Rectangle,
      Complex.mem_reProdIm] at hs
    simpa using hs
  have hTnonneg : 0 ≤ T := by linarith
  have hleft : (1 / 2 : ℝ) < dirichletLNonquadraticConductorLogLeftEdge q T :=
    one_half_lt_dirichletLNonquadraticConductorLogLeftEdge hT
  have hM : 4 ≤ dirichletLNonquadraticConductorLogCutoff q T :=
    four_le_dirichletLNonquadraticConductorLogCutoff hT
  have hlogM : 0 < Real.log (dirichletLNonquadraticConductorLogCutoff q T : ℝ) :=
    Real.log_pos (by exact_mod_cast (show
      1 < dirichletLNonquadraticConductorLogCutoff q T by omega))
  have hleftOne : dirichletLNonquadraticConductorLogLeftEdge q T < 1 := by
    unfold dirichletLNonquadraticConductorLogLeftEdge
    have : 0 < 1 / (274877906944 *
        (1 + Real.log (dirichletLNonquadraticConductorLogCutoff q T)) ^ 9) := by
      positivity
    linarith
  rw [Set.uIcc_of_le (by linarith), Set.uIcc_of_le (by linarith)] at hcoords
  by_cases hre : 1 ≤ s.re
  · exact χ.LFunction_ne_zero_of_one_le_re (Or.inl hχ) hre
  · have hrelt : s.re < 1 := lt_of_not_ge hre
    have himabs : |s.im| ≤ T := (abs_le).2 hcoords.2
    let m := dirichletLConductorHeightCutoff q s.im
    let M := dirichletLNonquadraticConductorLogCutoff q T
    let Lm : ℝ := 1 + Real.log m
    let LM : ℝ := 1 + Real.log M
    have hm : 2 ≤ m := by
      simpa only [m] using two_le_conductorHeightCutoff χ hχ s.im
    have hmM : m ≤ M := by
      simpa only [m, M] using
        dirichletLConductorHeightCutoff_le_fixedHeightCutoff himabs
    have hlogm : 0 < Real.log (m : ℝ) := by
      simpa only [m] using log_conductorHeightCutoff_pos χ hχ s.im
    have hlogle : Real.log (m : ℝ) ≤ Real.log (M : ℝ) :=
      Real.log_le_log (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hm))
        (by exact_mod_cast hmM)
    have hLm : 0 < Lm := by dsimp only [Lm]; linarith
    have hLM : 0 < LM := by dsimp only [LM]; linarith
    have hpowle : Lm ^ 9 ≤ LM ^ 9 := by
      apply pow_le_pow_left₀ hLm.le
      · dsimp only [Lm, LM]
        linarith
    have hdenle : 274877906944 * Lm ^ 9 ≤ 274877906944 * LM ^ 9 := by
      gcongr
    have hlocalden : 0 < (274877906944 : ℝ) * Lm ^ 9 := by positivity
    have hwidth : 1 / (274877906944 * LM ^ 9) ≤
        1 / (274877906944 * Lm ^ 9) :=
      one_div_le_one_div_of_le hlocalden hdenle
    have hsre : s.re ∈ Set.Ico
        (1 - 1 / (274877906944 *
          (1 + Real.log (dirichletLConductorHeightCutoff q s.im)) ^ 9)) 1 := by
      refine ⟨?_, hrelt⟩
      have hfixed := (sub_le_sub_left hwidth 1).trans hcoords.1.1
      simpa only [dirichletLNonquadraticConductorLogLeftEdge, LM, Lm, M, m] using hfixed
    have hzero := norm_LFunction_ne_zero_of_nonquadratic_conductorLog χ hχsq hsre
    have hsrepr : ((s.re : ℂ) + I * s.im) = s := by
      apply Complex.ext <;> simp
    simpa only [hsrepr] using hzero

/-- The logarithmic derivative is holomorphic throughout the fixed rectangle. -/
theorem logDerivative_holomorphicOn_nonquadratic_conductorLogRectangle
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {T : ℝ}
    (hχsq : χ ^ 2 ≠ 1) (hT : 3 ≤ T) :
    HolomorphicOn (fun s => deriv χ.LFunction s / χ.LFunction s)
      (dirichletLNonquadraticConductorLogRectangle q T) := by
  have hχ : χ ≠ 1 := by
    intro hχ
    apply hχsq
    rw [hχ, one_pow]
  have hL : Differentiable ℂ χ.LFunction :=
    DirichletCharacter.differentiable_LFunction hχ
  exact hL.deriv.differentiableOn.div hL.differentiableOn
    (LFunction_ne_zero_on_nonquadratic_conductorLogRectangle χ hχsq hT)

end AnalyticNumberTheory.LargeSieve