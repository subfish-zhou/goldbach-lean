import MathlibNt.AnalyticNumberTheory.LargeSieve.DirichLTwistedSmoothedNonquadraticErrorAssembly
import MathlibNt.AnalyticNumberTheory.LargeSieve.DirichLTwistedSmoothedPsiClose
import MathlibNt.AnalyticNumberTheory.LargeSieve.StandardBVLowHighConductor
import MathlibNt.AnalyticNumberTheory.LargeSieve.LogPowerBounds

open Set Function Filter Complex Real MeasureTheory

namespace AnalyticNumberTheory.LargeSieve

noncomputable section

/-- The polylogarithmic height used in the pointwise nonquadratic contour. -/
def nonquadraticPointwiseSWHeightExponent (D : ℕ) : ℕ := 2 * D + 30

def nonquadraticPointwiseSWHeight (D N : ℕ) : ℝ :=
  Real.log (N : ℝ) ^ nonquadraticPointwiseSWHeightExponent D

def nonquadraticPointwiseSWEpsilon (D N : ℕ) : ℝ :=
  (Real.log (N : ℝ) ^ (D + 3))⁻¹

def nonquadraticPointwiseSWDelta (N : ℕ) : ℝ :=
  (Real.log (N : ℝ))⁻¹

/-- Uniform `log log` control of the conductor-height logarithm at the chosen
polylogarithmic height.  This is the arithmetic input needed to make the left
edge exponential dominate every prescribed logarithmic loss. -/
theorem dirichletLTwistedSmoothedConductorLogLM_le_loglog_pointwise
    (C D N q : ℕ) [NeZero q] (hlog : Real.exp 1 ≤ Real.log (N : ℝ))
    (hq : q ≤ logConductorThreshold N C) :
    dirichletLTwistedSmoothedConductorLogLM q
        (nonquadraticPointwiseSWHeight D N) ≤
      (C + nonquadraticPointwiseSWHeightExponent D + 3 : ℕ) *
        Real.log (Real.log (N : ℝ)) := by
  let L := Real.log (N : ℝ)
  let B := nonquadraticPointwiseSWHeightExponent D
  have hLpos : 0 < L := lt_of_lt_of_le (Real.exp_pos 1) hlog
  have hL1 : 1 ≤ L := (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 1)).le.trans hlog
  have hlogL1 : 1 ≤ Real.log L := (Real.le_log_iff_exp_le hLpos).2 hlog
  have hqR : (q : ℝ) ≤ L ^ C := by
    calc
      (q : ℝ) ≤ logConductorThreshold N C := by exact_mod_cast hq
      _ ≤ L ^ C := by
        dsimp only [logConductorThreshold, L]
        simpa only [L] using
          (Nat.floor_le (pow_nonneg hLpos.le C))
  have hfloor :
      (⌊nonquadraticPointwiseSWHeight D N⌋₊ : ℝ) ≤
        nonquadraticPointwiseSWHeight D N := by
    exact Nat.floor_le (by
      dsimp only [nonquadraticPointwiseSWHeight]
      positivity)
  have hheight :
      (dirichletLNonquadraticConductorLogHeightBlock
          (nonquadraticPointwiseSWHeight D N) : ℝ) ≤ 2 * L ^ B := by
    dsimp only [dirichletLNonquadraticConductorLogHeightBlock]
    rw [Nat.cast_add, Nat.cast_one]
    calc
      (⌊nonquadraticPointwiseSWHeight D N⌋₊ : ℝ) + 1 ≤
          nonquadraticPointwiseSWHeight D N + 1 := by linarith
      _ = L ^ B + 1 := by rfl
      _ ≤ 2 * L ^ B := by
        have hpow : 1 ≤ L ^ B := one_le_pow₀ hL1
        linarith
  have hcut :
      (dirichletLTwistedSmoothedConductorLogCutoff q
          (nonquadraticPointwiseSWHeight D N) : ℝ) ≤
        2 * L ^ (C + B) := by
    dsimp only [dirichletLTwistedSmoothedConductorLogCutoff,
      dirichletLNonquadraticConductorLogCutoff]
    rw [Nat.cast_mul]
    calc
      (q : ℝ) * dirichletLNonquadraticConductorLogHeightBlock
          (nonquadraticPointwiseSWHeight D N) ≤ L ^ C * (2 * L ^ B) :=
        mul_le_mul hqR hheight (by positivity) (by positivity)
      _ = 2 * L ^ (C + B) := by rw [pow_add]; ring
  have hcutpos :
      0 < (dirichletLTwistedSmoothedConductorLogCutoff q
          (nonquadraticPointwiseSWHeight D N) : ℝ) := by
    have hq0 : 0 < q := NeZero.pos q
    have hh0 : 0 < dirichletLNonquadraticConductorLogHeightBlock
        (nonquadraticPointwiseSWHeight D N) := by
      dsimp only [dirichletLNonquadraticConductorLogHeightBlock]
      omega
    dsimp only [dirichletLTwistedSmoothedConductorLogCutoff,
      dirichletLNonquadraticConductorLogCutoff]
    exact_mod_cast Nat.mul_pos hq0 hh0
  have hlogcut := Real.log_le_log hcutpos hcut
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (pow_ne_zero _ (ne_of_gt hLpos)),
    Real.log_pow] at hlogcut
  norm_num only [Nat.cast_add] at hlogcut
  have hlog2 : Real.log (2 : ℝ) ≤ Real.log L := by
    apply Real.log_le_log (by norm_num)
    exact (show (2 : ℝ) ≤ Real.exp 1 by linarith [Real.exp_one_gt_d9]).trans hlog
  dsimp only [dirichletLTwistedSmoothedConductorLogLM]
  calc
    1 + Real.log (dirichletLTwistedSmoothedConductorLogCutoff q
        (nonquadraticPointwiseSWHeight D N) : ℝ) ≤
        1 + (Real.log 2 + (C + B) * Real.log L) := by linarith
    _ ≤ (C + B + 3 : ℕ) * Real.log L := by
      norm_num only [Nat.cast_add, Nat.cast_ofNat]
      nlinarith

/-- The quantitative left edge supplies an arbitrary fixed logarithmic saving,
uniformly for conductors below `logConductorThreshold`.  This is the genuinely
non-polynomial part of the parameter selection. -/
theorem eventually_nonquadraticPointwiseSW_leftEdge
    (C D E : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ q : ℕ, ∀ _inst : NeZero q,
      q ≤ logConductorThreshold N C →
      (N : ℝ) ^ (dirichletLTwistedSmoothedConductorLogFinalLeft q
          (nonquadraticPointwiseSWHeight D N)) ≤
        (N : ℝ) / Real.log (N : ℝ) ^ E := by
  let B := nonquadraticPointwiseSWHeightExponent D
  let A : ℝ := C + B + 3
  let M : ℝ := E + 1
  have hA : 0 < A := by dsimp only [A]; positivity
  have hM : 0 < M := by dsimp only [M]; positivity
  let c : ℝ := (4 * 4398046511104 * A ^ 9 * M)⁻¹
  have hc : 0 < c := by dsimp only [c]; positivity
  have hsmall := (isLittleO_log_rpow_rpow_atTop (10 : ℝ) (by norm_num : (0 : ℝ) < 1)).bound hc
  have hlogtop : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsmallN : ∀ᶠ N : ℕ in atTop,
      ‖Real.log (Real.log (N : ℝ)) ^ (10 : ℝ)‖ ≤
        c * ‖Real.log (N : ℝ) ^ (1 : ℝ)‖ := hlogtop.eventually hsmall
  filter_upwards [hsmallN,
      hlogtop.eventually (eventually_ge_atTop (Real.exp 1)),
      eventually_gt_atTop (0 : ℕ)] with N hsmallN hlog hN0
  intro q _inst hq
  let L := Real.log (N : ℝ)
  let z := Real.log L
  let LM := dirichletLTwistedSmoothedConductorLogLM q
    (nonquadraticPointwiseSWHeight D N)
  have hLpos : 0 < L := lt_of_lt_of_le (Real.exp_pos 1) hlog
  have hz1 : 1 ≤ z := (Real.le_log_iff_exp_le hLpos).2 hlog
  have hzpos : 0 < z := lt_of_lt_of_le zero_lt_one hz1
  have hLM := dirichletLTwistedSmoothedConductorLogLM_le_loglog_pointwise
    C D N q hlog hq
  have hLMpos : 0 < LM := by
    dsimp only [LM, dirichletLTwistedSmoothedConductorLogLM]
    have hcut : 0 < (dirichletLTwistedSmoothedConductorLogCutoff q
        (nonquadraticPointwiseSWHeight D N) : ℝ) := by
      have hq0 : 0 < q := NeZero.pos q
      have hh0 : 0 < dirichletLNonquadraticConductorLogHeightBlock
          (nonquadraticPointwiseSWHeight D N) := by
        dsimp only [dirichletLNonquadraticConductorLogHeightBlock]
        omega
      dsimp only [dirichletLTwistedSmoothedConductorLogCutoff,
        dirichletLNonquadraticConductorLogCutoff]
      exact_mod_cast Nat.mul_pos hq0 hh0
    have hcut1 : 1 ≤ dirichletLTwistedSmoothedConductorLogCutoff q
        (nonquadraticPointwiseSWHeight D N) := by exact_mod_cast hcut
    have hlogcut : 0 ≤ Real.log (dirichletLTwistedSmoothedConductorLogCutoff q
        (nonquadraticPointwiseSWHeight D N) : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hcut1)
    linarith
  have hLM' : LM ≤ A * z := by
    simpa only [LM, A, B, z, Nat.cast_add, Nat.cast_ofNat] using hLM
  have hLM9 : LM ^ 9 ≤ A ^ 9 * z ^ 9 := by
    calc
      LM ^ 9 ≤ (A * z) ^ 9 := pow_le_pow_left₀ hLMpos.le hLM' 9
      _ = A ^ 9 * z ^ 9 := by rw [mul_pow]
  have hsmall' : z ^ 10 ≤ c * L := by
    have hsmallR : z ^ (10 : ℝ) ≤ c * L := by
      rw [Real.norm_of_nonneg (Real.rpow_nonneg hzpos.le 10),
        Real.norm_of_nonneg (Real.rpow_nonneg hLpos.le 1), Real.rpow_one] at hsmallN
      exact hsmallN
    rw [← Real.rpow_natCast]
    exact hsmallR
  have hkey : 4 * 4398046511104 * LM ^ 9 * M * z ≤ L := by
    calc
      4 * 4398046511104 * LM ^ 9 * M * z ≤
          4 * 4398046511104 * (A ^ 9 * z ^ 9) * M * z := by gcongr
      _ = (4 * 4398046511104 * A ^ 9 * M) * z ^ 10 := by ring
      _ ≤ (4 * 4398046511104 * A ^ 9 * M) * (c * L) := by gcongr
      _ = L := by
        dsimp only [c]
        field_simp
  have hwidth : M * z ≤
      dirichletLTwistedSmoothedConductorLogEdgeWidth q
          (nonquadraticPointwiseSWHeight D N) / 4 * L := by
    dsimp only [dirichletLTwistedSmoothedConductorLogEdgeWidth]
    change M * z ≤ (1 / (4398046511104 * LM ^ 9)) / 4 * L
    rw [div_mul_eq_mul_div, one_div, inv_mul_eq_div, div_div]
    rw [le_div_iff₀ (show 0 < (4398046511104 * LM ^ 9) * 4 by positivity)]
    nlinarith
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN0
  have hexp : Real.exp (-(dirichletLTwistedSmoothedConductorLogEdgeWidth q
      (nonquadraticPointwiseSWHeight D N) / 4 * L)) ≤ Real.exp (-M * z) := by
    exact Real.exp_le_exp.mpr (by linarith)
  have hL1 : 1 ≤ L := (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 1)).le.trans hlog
  have hpow : Real.exp (-M * z) ≤ (Real.log (N : ℝ) ^ E)⁻¹ := by
    calc
      Real.exp (-M * z) = L ^ (-M) := by
        rw [Real.rpow_def_of_pos hLpos]
        congr 1
        dsimp only [z]
        ring
      _ ≤ L ^ (-(E : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le hL1 (by dsimp only [M]; push_cast; linarith)
      _ = (Real.log (N : ℝ) ^ E)⁻¹ := by
        rw [Real.rpow_neg hLpos.le, Real.rpow_natCast]
  rw [dirichletLTwistedSmoothedConductorLogFinalLeft,
    Real.rpow_def_of_pos hNpos]
  rw [show Real.log (N : ℝ) *
      (1 - dirichletLTwistedSmoothedConductorLogEdgeWidth q
        (nonquadraticPointwiseSWHeight D N) / 4) =
      Real.log (N : ℝ) +
        (-(dirichletLTwistedSmoothedConductorLogEdgeWidth q
          (nonquadraticPointwiseSWHeight D N) / 4 * L)) by
      dsimp only [L]; ring, Real.exp_add, Real.exp_log hNpos]
  calc
    (N : ℝ) * Real.exp (-(dirichletLTwistedSmoothedConductorLogEdgeWidth q
        (nonquadraticPointwiseSWHeight D N) / 4 * L)) ≤
        (N : ℝ) * Real.exp (-M * z) := by gcongr
    _ ≤ (N : ℝ) * (Real.log (N : ℝ) ^ E)⁻¹ := by gcongr
    _ = (N : ℝ) / Real.log (N : ℝ) ^ E := by rw [div_eq_mul_inv]

theorem rpow_one_add_inv_log_nat (N : ℕ) (hN : 1 < N) :
    (N : ℝ) ^ (1 + (Real.log (N : ℝ))⁻¹) = Real.exp 1 * N := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast (Nat.zero_lt_of_lt hN)
  have hlog : Real.log (N : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hN)).ne'
  rw [Real.rpow_add hNr, Real.rpow_one, Real.rpow_def_of_pos hNr]
  rw [mul_inv_cancel₀ hlog]
  ring

/-- The exact twisted prefix has the same elementary linear majorant as
Chebyshev's `psi`, uniformly in the character.  This is used to absorb all
prefixes below the square-root split. -/
theorem norm_lambdaCharacterPrefix_le_const_mul_self
    (N q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) :
    ‖lambdaCharacterPrefix N q χ‖ ≤ (Real.log 4 + 4) * N := by
  rw [lambdaCharacterPrefix]
  calc
    ‖∑ n ∈ Finset.range (N + 1), DirichletCharacter.twistedVonMangoldtCoeff χ n‖ ≤
        ∑ n ∈ Finset.range (N + 1), ‖DirichletCharacter.twistedVonMangoldtCoeff χ n‖ :=
      norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.range (N + 1), ArithmeticFunction.vonMangoldt n := by
      apply Finset.sum_le_sum
      intro n hn
      rw [DirichletCharacter.twistedVonMangoldtCoeff, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      exact mul_le_of_le_one_right ArithmeticFunction.vonMangoldt_nonneg
        (DirichletCharacter.norm_le_one χ n)
    _ = Chebyshev.psi (N : ℝ) := by
      rw [Chebyshev.psi_eq_sum_range]
      norm_num
    _ ≤ (Real.log 4 + 4) * N :=
      Chebyshev.psi_le_const_mul_self (by positivity)

/-- The smoothing-removal constant is uniform in both the modulus and the
character.  This is the quantifier order needed by pointwise applications. -/
theorem exists_uniform_twistedSmoothedPsiClose
    {SmoothingF : ℝ → ℝ} (diffSmoothingF : ContDiff ℝ 1 SmoothingF)
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (SmoothingFnonneg : ∀ x > 0, 0 ≤ SmoothingF x)
    (mass_one : ∫ x in Ioi 0, SmoothingF x / x = 1) :
    ∃ C > 0, ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
      (X : ℝ), 3 < X → ∀ (ε : ℝ), 0 < ε → ε < 1 → 2 < X * ε →
      ‖DirichletCharacter.twistedSmoothedPsi χ SmoothingF ε X -
        lambdaCharacterPrefix ⌊X⌋₊ q χ‖ ≤ C * ε * X * Real.log X := by
  obtain ⟨c₁, c₁_pos, c₁_eq, hc₁⟩ :=
    Smooth1Properties_below suppSmoothingF mass_one
  obtain ⟨c₂, c₂_pos, c₂_eq, hc₂⟩ :=
    Smooth1Properties_above suppSmoothingF
  have c₁_lt : c₁ < 1 := by
    rw [c₁_eq]
    exact lt_trans Real.log_two_lt_d9 (by norm_num)
  have c₂_lt : c₂ < 2 := by
    rw [c₂_eq]
    nth_rewrite 3 [← mul_one 2]
    apply mul_lt_mul'
    · rfl
    · exact lt_trans Real.log_two_lt_d9 (by norm_num)
    · exact Real.log_nonneg (by norm_num)
    · positivity
  let C₀ : ℝ := 6 * (3 * c₁ + c₂)
  have C₀_pos : 0 < C₀ := by dsimp [C₀]; positivity
  refine ⟨2 * C₀, mul_pos (by norm_num) C₀_pos, ?_⟩
  intro q _ χ X X_gt_three ε ε_pos ε_lt_one Xε_gt_two
  have X_pos : 0 < X := by linarith
  have n_div_X_pos {n : ℕ} (hn : 0 < n) : 0 < (n : ℝ) / X := by positivity
  have smoothAbove (n : ℕ) (hn : 0 < n) :
      Smooth1 SmoothingF ε (n / X) ≤ 1 :=
    Smooth1LeOne SmoothingFnonneg mass_one ε_pos (n_div_X_pos hn)
  have smoothBelow (n : ℕ) (hn : 0 < n) :
      0 ≤ Smooth1 SmoothingF ε (n / X) :=
    Smooth1Nonneg SmoothingFnonneg (n_div_X_pos hn) ε_pos
  have smoothOne (n : ℕ) (hn : 0 < n)
      (hnle : (n : ℝ) ≤ X * (1 - c₁ * ε)) :
      Smooth1 SmoothingF ε (n / X) = 1 := by
    apply hc₁ (ε := ε) (n / X) ε_pos (n_div_X_pos hn)
    exact (div_le_iff₀' X_pos).mpr hnle
  have smoothZero (n : ℕ)
      (hn : 1 + c₂ * ε ≤ (n : ℝ) / X) :
      Smooth1 SmoothingF ε (n / X) = 0 :=
    hc₂ (ε := ε) (n / X) ⟨ε_pos, ε_lt_one⟩ hn
  have X_bound_1 : 1 ≤ X * ε * c₁ := by
    rw [c₁_eq, ← div_le_iff₀]
    · have h : 1 / Real.log 2 < 2 := by
        nth_rewrite 2 [← one_div_one_div 2]
        rw [one_div_lt_one_div]
        · exact lt_of_le_of_lt (by norm_num) Real.log_two_gt_d9
        · exact Real.log_pos (by norm_num)
        · norm_num
      exact le_of_lt (h.trans Xε_gt_two)
    · exact Real.log_pos (by norm_num)
  have X_bound_2 : 1 ≤ X * ε * c₂ := by
    rw [c₂_eq, ← div_le_iff₀]
    · have h : 1 / (2 * Real.log 2) < 2 := by
        nth_rewrite 3 [← one_div_one_div 2]
        rw [one_div_lt_one_div, ← one_mul (1 / 2)]
        · apply mul_lt_mul
          · norm_num
          · exact le_of_lt (lt_trans (by norm_num) Real.log_two_gt_d9)
          · norm_num
          · norm_num
        · norm_num
          exact Real.log_pos (by norm_num)
        · norm_num
      exact le_of_lt (h.trans Xε_gt_two)
    · norm_num
      exact Real.log_pos (by norm_num)
  exact DirichletCharacter.twistedSmoothedPsiClose_aux
    SmoothingF c₁ c₁_pos c₁_lt c₂ c₂_pos c₂_lt hc₂ C₀ rfl
    ε ε_pos ε_lt_one X X_pos X_gt_three X_bound_1 X_bound_2
    smoothAbove smoothBelow smoothOne smoothZero χ

/-- Exact-prefix closure of the nonquadratic contour once the four scalar
payments (left edge, horizontal edges, right tails, and smoothing removal) have
been made.  The constants are chosen before the modulus and character. -/
theorem exists_nonquadraticExactPrefix_of_four_payments
    {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν)
    (νpos : ∀ x > 0, 0 ≤ ν x)
    (suppν : support ν ⊆ Icc (1 / 2) 2)
    (mass_one : ∫ x in Ioi (0 : ℝ), ν x / x = 1) :
    ∃ K > 0, ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
      {T d ε X R : ℝ}, χ ^ 2 ≠ 1 → 3 ≤ T → 0 < d → d ≤ 1 →
      0 < ε → ε < 1 → 3 < X → 2 < X * ε → 0 ≤ R →
      T * (dirichletLTwistedSmoothedConductorLogLM q T) ^ 11 *
          X ^ (dirichletLTwistedSmoothedConductorLogFinalLeft q T) / ε ≤ R →
      (dirichletLTwistedSmoothedConductorLogLM q T) ^ 11 * X ^ (1 + d) /
          (ε * (1 + T ^ 2)) ≤ R →
      X ^ (1 + d) * (1 + d⁻¹ ^ 2) / (ε * T) ≤ R →
      ε * X * Real.log X ≤ R →
      ‖lambdaCharacterPrefix ⌊X⌋₊ q χ‖ ≤ K * R := by
  obtain ⟨K₀, hK₀, hcontour⟩ :=
    exists_dirichletLTwistedSmoothedNonquadraticErrorAssembly
      diffν νpos suppν mass_one
  obtain ⟨C₀, hC₀, hclose⟩ :=
    exists_uniform_twistedSmoothedPsiClose diffν suppν νpos mass_one
  let K := 3 * K₀ + C₀ + 1
  refine ⟨K, by dsimp only [K]; positivity, ?_⟩
  intro q _ χ T d ε X R hχ hT hd hd1 hε hε1 hX hXε hR
    hleft hhoriz htail hsmooth
  have hs := hcontour (X := X) χ hχ hT hd hd1 hε hε1 (by linarith)
  have hc := hclose χ X hX ε hε hε1 hXε
  have hsmoothed : ‖DirichletCharacter.twistedSmoothedPsi χ ν ε X‖ ≤
      3 * K₀ * R := by
    calc
      _ ≤ K₀ *
          (T * (dirichletLTwistedSmoothedConductorLogLM q T) ^ 11 *
                X ^ (dirichletLTwistedSmoothedConductorLogFinalLeft q T) / ε +
            (dirichletLTwistedSmoothedConductorLogLM q T) ^ 11 * X ^ (1 + d) /
                (ε * (1 + T ^ 2)) +
            X ^ (1 + d) * (1 + d⁻¹ ^ 2) / (ε * T)) := hs
      _ ≤ K₀ * (R + R + R) := by gcongr
      _ = 3 * K₀ * R := by ring
  have hremove :
      ‖DirichletCharacter.twistedSmoothedPsi χ ν ε X -
          lambdaCharacterPrefix ⌊X⌋₊ q χ‖ ≤ C₀ * R := by
    calc
      _ ≤ C₀ * ε * X * Real.log X := hc
      _ = C₀ * (ε * X * Real.log X) := by ring
      _ ≤ C₀ * R := mul_le_mul_of_nonneg_left hsmooth hC₀.le
  calc
    ‖lambdaCharacterPrefix ⌊X⌋₊ q χ‖ =
        ‖DirichletCharacter.twistedSmoothedPsi χ ν ε X -
          (DirichletCharacter.twistedSmoothedPsi χ ν ε X -
            lambdaCharacterPrefix ⌊X⌋₊ q χ)‖ := by ring_nf
    _ ≤ ‖DirichletCharacter.twistedSmoothedPsi χ ν ε X‖ +
        ‖DirichletCharacter.twistedSmoothedPsi χ ν ε X -
          lambdaCharacterPrefix ⌊X⌋₊ q χ‖ := norm_sub_le _ _
    _ ≤ 3 * K₀ * R + C₀ * R := add_le_add hsmoothed hremove
    _ ≤ K * R := by dsimp only [K]; nlinarith

/-- A fixed logarithmic power is eventually bounded by the square root.
This scalar estimate is independent of the conductor and character. -/
private theorem eventually_log_pow_le_sqrt_nat (k : ℕ) :
    ∀ᶠ N : ℕ in atTop, Real.log (N : ℝ) ^ k ≤ Real.sqrt N := by
  exact log_pow_le_sqrt_eventually k

/-- At the strengthened loss `P = D + 20`, the prescribed polylogarithmic
height, reciprocal-log displacement, and smoothing width pay all four contour
terms against the common target `N / log(N)^D`, uniformly in the conductor. -/
theorem eventually_nonquadraticPointwiseSW_four_payments (C D : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ q : ℕ, ∀ _inst : NeZero q,
      q ≤ logConductorThreshold N C →
      let P := D + 20
      let T := nonquadraticPointwiseSWHeight P N
      let d := nonquadraticPointwiseSWDelta N
      let ε := nonquadraticPointwiseSWEpsilon P N
      let R := (N : ℝ) / Real.log (N : ℝ) ^ D
      3 ≤ T ∧ 0 < d ∧ d ≤ 1 ∧ 0 < ε ∧ ε < 1 ∧ 3 < (N : ℝ) ∧
      2 < (N : ℝ) * ε ∧ 0 ≤ R ∧
      T * (dirichletLTwistedSmoothedConductorLogLM q T) ^ 11 *
          (N : ℝ) ^ (dirichletLTwistedSmoothedConductorLogFinalLeft q T) / ε ≤ R ∧
      (dirichletLTwistedSmoothedConductorLogLM q T) ^ 11 *
          (N : ℝ) ^ (1 + d) / (ε * (1 + T ^ 2)) ≤ R ∧
      (N : ℝ) ^ (1 + d) * (1 + d⁻¹ ^ 2) / (ε * T) ≤ R ∧
      ε * (N : ℝ) * Real.log (N : ℝ) ≤ R := by
  let P := D + 20
  let B := nonquadraticPointwiseSWHeightExponent P
  let A : ℝ := C + B + 3
  let E := B + P + D + 20
  have hleft := eventually_nonquadraticPointwiseSW_leftEdge C P E
  have hlogtop : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hpoly := hlogtop.eventually
    (eventually_ge_atTop (max (Real.exp 1) (max (A ^ 11) 4)))
  have hsqrt := eventually_log_pow_le_sqrt_nat (P + 4)
  filter_upwards [hleft, hpoly, hsqrt, eventually_ge_atTop (4 : ℕ)] with
      N hleft hLlarge hsqrt hN
  intro q _inst hq
  let L := Real.log (N : ℝ)
  let T := nonquadraticPointwiseSWHeight P N
  let d := nonquadraticPointwiseSWDelta N
  let ε := nonquadraticPointwiseSWEpsilon P N
  let R := (N : ℝ) / L ^ D
  have hexpL : Real.exp 1 ≤ L := (le_max_left _ _).trans hLlarge
  have hLpos : 0 < L := lt_of_lt_of_le (Real.exp_pos 1) hexpL
  have hL1 : 1 ≤ L := (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 1)).le.trans
    hexpL
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hA11 : A ^ 11 ≤ L := (le_max_left _ _).trans ((le_max_right _ _).trans hLlarge)
  have h4L : (4 : ℝ) ≤ L := (le_max_right _ _).trans ((le_max_right _ _).trans hLlarge)
  have hlogL : Real.log L ≤ L := Real.log_le_self hLpos.le
  have hLM0 := dirichletLTwistedSmoothedConductorLogLM_le_loglog_pointwise
    C P N q hexpL hq
  have hLM : dirichletLTwistedSmoothedConductorLogLM q T ≤ A * L := by
    calc
      _ ≤ (C + nonquadraticPointwiseSWHeightExponent P + 3 : ℕ) * L :=
        hLM0.trans (mul_le_mul_of_nonneg_left hlogL (by positivity))
      _ = A * L := by norm_num [A, B]
  have hLMpos : 0 < dirichletLTwistedSmoothedConductorLogLM q T := by
    dsimp only [dirichletLTwistedSmoothedConductorLogLM]
    have hc : (1 : ℝ) ≤ dirichletLTwistedSmoothedConductorLogCutoff q T := by
      exact_mod_cast (show 1 ≤ dirichletLTwistedSmoothedConductorLogCutoff q T by
        dsimp only [dirichletLTwistedSmoothedConductorLogCutoff,
          dirichletLNonquadraticConductorLogCutoff,
          dirichletLNonquadraticConductorLogHeightBlock]
        exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (NeZero.ne q) (by omega)))
    linarith [Real.log_nonneg hc]
  have hLM11 : (dirichletLTwistedSmoothedConductorLogLM q T) ^ 11 ≤ L ^ 12 := by
    calc
      _ ≤ (A * L) ^ 11 := pow_le_pow_left₀ hLMpos.le hLM 11
      _ = A ^ 11 * L ^ 11 := by rw [mul_pow]
      _ ≤ L * L ^ 11 := mul_le_mul_of_nonneg_right hA11 (pow_nonneg hLpos.le _)
      _ = L ^ 12 := by ring
  have hT : T = L ^ B := rfl
  have hd : d = L⁻¹ := rfl
  have heps : ε = (L ^ (P + 3))⁻¹ := rfl
  have hNpos : (0 : ℝ) < N := by positivity
  have hNpow : (N : ℝ) ^ (1 + d) = Real.exp 1 * N := by
    simpa only [hd] using rpow_one_add_inv_log_nat N (by omega)
  have hR0 : 0 ≤ R := div_nonneg (by positivity) (pow_nonneg hLpos.le _)
  have hleftN := hleft q _inst hq
  have hleftPay :
      T * (dirichletLTwistedSmoothedConductorLogLM q T) ^ 11 *
          (N : ℝ) ^ (dirichletLTwistedSmoothedConductorLogFinalLeft q T) / ε ≤ R := by
    rw [hT, heps, div_inv_eq_mul]
    calc
      L ^ B * (dirichletLTwistedSmoothedConductorLogLM q T) ^ 11 *
          (N : ℝ) ^ (dirichletLTwistedSmoothedConductorLogFinalLeft q T) * L ^ (P + 3) ≤
          L ^ B * L ^ 12 * ((N : ℝ) / L ^ E) * L ^ (P + 3) := by gcongr
      _ ≤ (N : ℝ) / L ^ D := by
        rw [div_eq_mul_inv]
        field_simp
        dsimp only [E, B, P, nonquadraticPointwiseSWHeightExponent]
        ring_nf
        gcongr
        omega
  have hhorizPay :
      (dirichletLTwistedSmoothedConductorLogLM q T) ^ 11 *
          (N : ℝ) ^ (1 + d) / (ε * (1 + T ^ 2)) ≤ R := by
    rw [hNpow, heps, hT]
    have hden : 0 < (L ^ (P + 3))⁻¹ * (1 + (L ^ B) ^ 2) := by positivity
    rw [div_le_iff₀ hden]
    calc
      (dirichletLTwistedSmoothedConductorLogLM q T) ^ 11 * (Real.exp 1 * N) ≤
          L ^ 12 * (4 * N) := by gcongr; exact Real.exp_one_lt_d9.le.trans (by norm_num)
      _ ≤ R * ((L ^ (P + 3))⁻¹ * (1 + (L ^ B) ^ 2)) := by
        dsimp only [R]
        field_simp
        dsimp only [B, P, nonquadraticPointwiseSWHeightExponent]
        ring_nf
        calc
          L ^ 35 * L ^ (D * 2) * 4 ≤ L ^ 35 * L ^ (D * 2) * L := by gcongr
          _ ≤ L ^ 140 * L ^ (D * 4) := by
            calc
              L ^ 35 * L ^ (D * 2) * L = L ^ 36 * L ^ (D * 2) := by ring
              _ ≤ L ^ 140 * L ^ (D * 4) :=
                mul_le_mul
                  (pow_le_pow_right₀ hL1 (by norm_num))
                  (pow_le_pow_right₀ hL1 (show D * 2 ≤ D * 4 by omega))
                  (pow_nonneg hLpos.le _) (pow_nonneg hLpos.le _)
          _ ≤ 1 + L ^ 140 * L ^ (D * 4) := by linarith
  have htailPay :
      (N : ℝ) ^ (1 + d) * (1 + d⁻¹ ^ 2) / (ε * T) ≤ R := by
    rw [hNpow, hd, heps, hT]
    have hdinv : (L⁻¹)⁻¹ = L := inv_inv L
    rw [hdinv]
    have hden : 0 < (L ^ (P + 3))⁻¹ * L ^ B := by positivity
    rw [div_le_iff₀ hden]
    calc
      Real.exp 1 * N * (1 + L ^ 2) ≤ 8 * N * L ^ 2 := by
        have he : Real.exp 1 ≤ 4 := Real.exp_one_lt_d9.le.trans (by norm_num)
        have htwo : 1 + L ^ 2 ≤ 2 * L ^ 2 := by nlinarith [sq_nonneg L, hL1]
        calc
          _ ≤ 4 * N * (1 + L ^ 2) := by gcongr
          _ ≤ 4 * N * (2 * L ^ 2) := by gcongr
          _ = 8 * N * L ^ 2 := by ring
      _ ≤ R * ((L ^ (P + 3))⁻¹ * L ^ B) := by
        dsimp only [R]
        field_simp
        dsimp only [B, P, nonquadraticPointwiseSWHeightExponent]
        ring_nf
        have h8L2 : (8 : ℝ) ≤ L ^ 2 := by
          calc
            (8 : ℝ) ≤ 4 ^ 2 := by norm_num
            _ ≤ L ^ 2 := by gcongr
        calc
          L ^ 25 * L ^ (D * 2) * 8 ≤ L ^ 25 * L ^ (D * 2) * L ^ 2 := by gcongr
          _ = L ^ 27 * L ^ (D * 2) := by ring
          _ ≤ L ^ 70 * L ^ (D * 2) :=
            mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hL1 (by omega))
              (pow_nonneg hLpos.le _)
  have hsmoothPay : ε * (N : ℝ) * L ≤ R := by
    rw [heps]
    dsimp only [R]
    field_simp
    rw [mul_comm L, ← pow_succ]
    exact pow_le_pow_right₀ hL1 (by omega)
  have hT3 : 3 ≤ T := by
    rw [hT]
    have hLB : L ≤ L ^ B := by
      simpa only [pow_one] using pow_le_pow_right₀ hL1 (show 1 ≤ B by
        dsimp only [B, nonquadraticPointwiseSWHeightExponent]; omega)
    exact (show (3 : ℝ) ≤ 4 by norm_num).trans (h4L.trans hLB)
  have hdpos : 0 < d := by rw [hd]; positivity
  have hd1 : d ≤ 1 := by rw [hd]; exact (inv_le_one₀ hLpos).2 hL1
  have hepspos : 0 < ε := by rw [heps]; positivity
  have heps1 : ε < 1 := by
    rw [heps]
    have hLgt1 : 1 < L := lt_of_lt_of_le (Real.one_lt_exp_iff.mpr (by norm_num)) hexpL
    exact (inv_lt_one₀ (pow_pos hLpos _)).2 (one_lt_pow₀ hLgt1 (by omega))
  have hXeps : 2 < (N : ℝ) * ε := by
    rw [heps]
    have hsqrtpos : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.2 (by positivity)
    rw [← div_eq_mul_inv]
    apply (lt_div_iff₀ (pow_pos hLpos _)).2
    have h2L : (2 : ℝ) ≤ L := (show (2 : ℝ) ≤ 4 by norm_num).trans h4L
    calc
      2 * L ^ (P + 3) ≤ L * L ^ (P + 3) :=
        mul_le_mul_of_nonneg_right h2L (pow_nonneg hLpos.le _)
      _ = L ^ (P + 4) := by rw [← pow_succ']
      _ ≤ Real.sqrt (N : ℝ) := hsqrt
      _ < (N : ℝ) := by
        have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
        exact Real.sqrt_lt_self_iff.mpr hNr
  exact ⟨hT3, hdpos, hd1, hepspos, heps1, by exact_mod_cast (show 3 < N by omega),
    hXeps, hR0, hleftPay, hhorizPay, htailPay, hsmoothPay⟩

/-- Uniform-in-`y` nonquadratic pointwise Siegel--Walfisz bound.  The conductor
cutoff is measured at the ambient endpoint `N`; for large prefixes the same
`N`-based contour is used, while prefixes below `2√N` are paid by the elementary
Chebyshev bound. -/
theorem exists_nonquadraticPointwiseSiegelWalfisz_uniform
    {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν)
    (νpos : ∀ x > 0, 0 ≤ ν x)
    (suppν : support ν ⊆ Icc (1 / 2) 2)
    (mass_one : ∫ x in Ioi (0 : ℝ), ν x / x = 1)
    (C D : ℕ) :
    ∃ K > 0, ∀ᶠ N : ℕ in atTop, ∀ q : ℕ, ∀ _inst : NeZero q,
      q ≤ logConductorThreshold N C → ∀ χ : DirichletCharacter ℂ q,
        χ ^ 2 ≠ 1 → ∀ y : ℕ, y ≤ N →
          ‖lambdaCharacterPrefix y q χ‖ ≤
            K * (N : ℝ) / Real.log (N : ℝ) ^ D := by
  obtain ⟨K₀, hK₀, hexact⟩ :=
    exists_nonquadraticExactPrefix_of_four_payments diffν νpos suppν mass_one
  let c : ℝ := Real.log 4 + 4
  let K : ℝ := K₀ + 2 * c
  refine ⟨K, by dsimp only [K, c]; positivity, ?_⟩
  have hpay := eventually_nonquadraticPointwiseSW_four_payments C D
  have hsqrt := eventually_log_pow_le_sqrt_nat D
  let P := D + 20
  have hsqrtStrong := eventually_log_pow_le_sqrt_nat (P + 4)
  have hlogtop : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlog4ev := hlogtop.eventually (eventually_ge_atTop (4 : ℝ))
  filter_upwards [hpay, hsqrt, hsqrtStrong, hlog4ev,
      eventually_ge_atTop (4 : ℕ)] with N hpay hsqrt hsqrtStrong hlog4 hN
  intro q _inst hq χ hχ y hy
  let T := nonquadraticPointwiseSWHeight P N
  let d := nonquadraticPointwiseSWDelta N
  let ε := nonquadraticPointwiseSWEpsilon P N
  let R := (N : ℝ) / Real.log (N : ℝ) ^ D
  obtain ⟨hT, hd, hd1, hε, hε1, hN3, hNε, hR,
    hleft, hhoriz, htail, hsmooth⟩ := hpay q _inst hq
  have hlogpos : 0 < Real.log (N : ℝ) := Real.log_pos (by
    exact_mod_cast (show 1 < N by omega))
  have hRpos : 0 < R := div_pos (by positivity) (pow_pos hlogpos _)
  by_cases hsmall : (y : ℝ) ≤ 2 * Real.sqrt N
  · have helem := norm_lambdaCharacterPrefix_le_const_mul_self y q χ
    have hsqrtN : Real.sqrt (N : ℝ) * Real.sqrt N = N := by
      rw [← pow_two, Real.sq_sqrt (by positivity)]
    have hsmallR : 2 * c * Real.sqrt N ≤ 2 * c * R := by
      have hc : 0 ≤ c := by dsimp only [c]; positivity
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by norm_num) hc)
      rw [show R = (N : ℝ) / Real.log (N : ℝ) ^ D by rfl,
        le_div_iff₀ (pow_pos hlogpos _)]
      calc
        Real.sqrt N * Real.log (N : ℝ) ^ D ≤ Real.sqrt N * Real.sqrt N := by gcongr
        _ = N := hsqrtN
    calc
      ‖lambdaCharacterPrefix y q χ‖ ≤ c * y := helem
      _ ≤ c * (2 * Real.sqrt N) := by gcongr
      _ = 2 * c * Real.sqrt N := by ring
      _ ≤ 2 * c * R := hsmallR
      _ ≤ K * R := by dsimp only [K]; nlinarith
      _ = K * (N : ℝ) / Real.log (N : ℝ) ^ D := by rw [show R = (N : ℝ) /
          Real.log (N : ℝ) ^ D by rfl, mul_div_assoc]
  · have hlarge : 2 * Real.sqrt N < (y : ℝ) := lt_of_not_ge hsmall
    have hypos : (0 : ℝ) < y := lt_trans (by positivity : (0 : ℝ) < 2 * Real.sqrt N) hlarge
    have hNr4 : (4 : ℝ) ≤ N := by exact_mod_cast hN
    have hsqrt2 : (2 : ℝ) ≤ Real.sqrt N := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ N by positivity), Real.sqrt_nonneg (N : ℝ)]
    have hy3 : (3 : ℝ) < y := by nlinarith
    have hyN : (y : ℝ) ≤ N := by exact_mod_cast hy
    have hLMone : 1 ≤ dirichletLTwistedSmoothedConductorLogLM q T := by
      dsimp only [dirichletLTwistedSmoothedConductorLogLM]
      have hc : (1 : ℝ) ≤ dirichletLTwistedSmoothedConductorLogCutoff q T := by
        exact_mod_cast (show 1 ≤ dirichletLTwistedSmoothedConductorLogCutoff q T by
          dsimp only [dirichletLTwistedSmoothedConductorLogCutoff,
            dirichletLNonquadraticConductorLogCutoff,
            dirichletLNonquadraticConductorLogHeightBlock]
          exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (NeZero.ne q) (by omega)))
      linarith [Real.log_nonneg hc]
    have hfinal0 : 0 ≤ dirichletLTwistedSmoothedConductorLogFinalLeft q T := by
      dsimp only [dirichletLTwistedSmoothedConductorLogFinalLeft,
        dirichletLTwistedSmoothedConductorLogEdgeWidth]
      have hp9 : 1 ≤ (dirichletLTwistedSmoothedConductorLogLM q T) ^ 9 :=
        one_le_pow₀ hLMone
      have hden : (4 : ℝ) ≤ 4 * (4398046511104 *
          (dirichletLTwistedSmoothedConductorLogLM q T) ^ 9) := by nlinarith
      rw [div_div]
      have hden' : (1 : ℝ) ≤ 4398046511104 *
          (dirichletLTwistedSmoothedConductorLogLM q T) ^ 9 * 4 := by
        nlinarith
      exact sub_nonneg.mpr ((div_le_one (by positivity)).2 hden')
    have hrpowLeft :
        (y : ℝ) ^ dirichletLTwistedSmoothedConductorLogFinalLeft q T ≤
          (N : ℝ) ^ dirichletLTwistedSmoothedConductorLogFinalLeft q T :=
      Real.rpow_le_rpow (by positivity) hyN hfinal0
    have hrpowRight : (y : ℝ) ^ (1 + d) ≤ (N : ℝ) ^ (1 + d) := by
      apply Real.rpow_le_rpow (by positivity) hyN
      linarith
    have hleftY : T * (dirichletLTwistedSmoothedConductorLogLM q T) ^ 11 *
        (y : ℝ) ^ (dirichletLTwistedSmoothedConductorLogFinalLeft q T) / ε ≤ R := by
      apply le_trans _ hleft
      gcongr
    have hhorizY : (dirichletLTwistedSmoothedConductorLogLM q T) ^ 11 *
        (y : ℝ) ^ (1 + d) / (ε * (1 + T ^ 2)) ≤ R := by
      apply le_trans _ hhoriz
      gcongr
    have htailY : (y : ℝ) ^ (1 + d) * (1 + d⁻¹ ^ 2) / (ε * T) ≤ R := by
      apply le_trans _ htail
      gcongr
    have hsmoothY : ε * (y : ℝ) * Real.log (y : ℝ) ≤ R := by
      apply le_trans _ hsmooth
      have hlogy : Real.log (y : ℝ) ≤ Real.log (N : ℝ) := Real.log_le_log hypos hyN
      gcongr
    have hyε : 2 < (y : ℝ) * ε := by
      have hεdef : ε = (Real.log (N : ℝ) ^ (P + 3))⁻¹ := rfl
      rw [hεdef, ← div_eq_mul_inv]
      apply (lt_div_iff₀ (pow_pos hlogpos _)).2
      calc
        2 * Real.log (N : ℝ) ^ (P + 3) ≤
            2 * Real.log (N : ℝ) ^ (P + 4) := by
              exact mul_le_mul_of_nonneg_left
                (pow_le_pow_right₀ (by linarith [hlog4]) (by omega)) (by norm_num)
        _ ≤ 2 * Real.sqrt N := by gcongr
        _ < (y : ℝ) := hlarge
    have hbound := hexact χ (T := T) (d := d) (ε := ε) (X := (y : ℝ)) (R := R)
      hχ hT hd hd1 hε hε1 hy3 hyε hR hleftY hhorizY htailY hsmoothY
    have hfloor : ⌊(y : ℝ)⌋₊ = y := Nat.floor_natCast y
    rw [hfloor] at hbound
    calc
      ‖lambdaCharacterPrefix y q χ‖ ≤ K₀ * R := hbound
      _ ≤ K * R := by
        apply mul_le_mul_of_nonneg_right _ hR
        dsimp only [K, c]
        nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 4)]
      _ = K * (N : ℝ) / Real.log (N : ℝ) ^ D := by rw [show R = (N : ℝ) /
          Real.log (N : ℝ) ^ D by rfl, mul_div_assoc]

end

end AnalyticNumberTheory.LargeSieve