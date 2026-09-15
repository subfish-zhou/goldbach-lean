import MathlibNt.AnalyticNumberTheory.LargeSieve.DirichLTwistedSmoothedQuadraticConditionalExactPrefix
import MathlibNt.AnalyticNumberTheory.LargeSieve.LandauSiegelToLowSWConditionalAdapter
import MathlibNt.AnalyticNumberTheory.LargeSieve.StandardBVPayload

open Set Function Filter Complex Real MeasureTheory

namespace AnalyticNumberTheory.LargeSieve

noncomputable section

/-- The raw Landau--Siegel input is kept with the exact outer quantifier order
requested by the production adapter. -/
abbrev RawLandauSiegelLowerBound : Prop :=
  ∀ η : ℝ, 0 < η → ∃ c : ℝ, 0 < c ∧
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsPrimitive → χ ^ 2 = 1 → χ ≠ 1 →
      c * (q : ℝ) ^ (-η) ≤ (χ.LFunction 1).re

private theorem rpow_one_add_inv_log_nat (N : ℕ) (hN : 1 < N) :
    (N : ℝ) ^ (1 + (Real.log (N : ℝ))⁻¹) = Real.exp 1 * N := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast (Nat.zero_lt_of_lt hN)
  have hlog : Real.log (N : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hN)).ne'
  rw [Real.rpow_add hNr, Real.rpow_one, Real.rpow_def_of_pos hNr]
  rw [mul_inv_cancel₀ hlog]
  ring

private theorem quadratic_integral_lower_middle_upper
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

/-- The pointwise quadratic contour keeps the conditional left edge but lets
the right edge move anywhere inside the quarter-width strip. -/
noncomputable def dirichletLTwistedSmoothedQuadraticPointwiseRectangle
    (A c η : ℝ) (q : ℕ) (T δ : ℝ) : Set ℂ :=
  ((dirichletLTwistedSmoothedQuadraticConditionalLeft A c η q T : ℂ) - I * T).Rectangle
    (((1 + δ : ℝ) : ℂ) + I * T)

theorem dirichletLTwistedSmoothedQuadraticPointwiseRectangle_subset
    {A c η T δ : ℝ} {q : ℕ}
    (hT : 0 ≤ T)
    (hδ : 0 < δ)
    (hδwidth : δ ≤ dirichletLTwistedSmoothedQuadraticConditionalDelta A c η q T) :
    dirichletLTwistedSmoothedQuadraticPointwiseRectangle A c η q T δ ⊆
      dirichletLTwistedSmoothedQuadraticConditionalRectangle A c η q T := by
  intro s hs
  have hw : 0 < dirichletLQuadraticConditionalCrossZeroWidth A c η q T := by
    dsimp only [dirichletLTwistedSmoothedQuadraticConditionalDelta] at hδwidth
    linarith
  rw [dirichletLTwistedSmoothedQuadraticPointwiseRectangle, Complex.Rectangle,
    Complex.mem_reProdIm] at hs
  norm_num at hs
  have hleftRight :
      dirichletLTwistedSmoothedQuadraticConditionalLeft A c η q T ≤ 1 + δ := by
    dsimp only [dirichletLTwistedSmoothedQuadraticConditionalLeft]
    linarith
  rw [Set.uIcc_of_le hleftRight, Set.uIcc_of_le (by linarith)] at hs
  rcases hs with ⟨hsre, hsim⟩
  rw [dirichletLTwistedSmoothedQuadraticConditionalRectangle, Complex.Rectangle,
    Complex.mem_reProdIm]
  norm_num
  have hfixed :
      dirichletLTwistedSmoothedQuadraticConditionalLeft A c η q T ≤
        dirichletLTwistedSmoothedQuadraticConditionalRight A c η q T := by
    dsimp only [dirichletLTwistedSmoothedQuadraticConditionalLeft,
      dirichletLTwistedSmoothedQuadraticConditionalRight,
      dirichletLTwistedSmoothedQuadraticConditionalDelta]
    linarith [hw]
  rw [Set.uIcc_of_le hfixed, Set.uIcc_of_le (by linarith)]
  refine ⟨⟨hsre.1, ?_⟩, hsim⟩
  have hδright :
      1 + δ ≤ dirichletLTwistedSmoothedQuadraticConditionalRight A c η q T := by
    dsimp only [dirichletLTwistedSmoothedQuadraticConditionalRight,
      dirichletLTwistedSmoothedQuadraticConditionalDelta] at hδwidth ⊢
    linarith
  exact le_trans hsre.2 hδright

theorem twistedSmoothedPerronIntegrand_holomorphicOn_quadraticPointwiseRectangle
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {A A₀ c η T δ : ℝ} (hAA₀ : A ≤ A₀) (hA : 0 < A)
    (hc : 0 < c) (hη : 0 < η) (hT : 0 < T) (hχ : χ ≠ 1)
    (hw : 0 < dirichletLQuadraticConditionalCrossZeroWidth A c η q T)
    (hw2 : dirichletLQuadraticConditionalCrossZeroWidth A c η q T ≤ 1 / 2)
    (hwidthle : dirichletLQuadraticConditionalCrossZeroWidth A c η q T ≤
      dirichletLQuadraticConditionalCrossZeroWidth A₀ c η q T)
    (hzero : ∀ s ∈ dirichletLQuadraticConditionalCrossZeroRectangle A₀ c η q T,
      χ.LFunction s ≠ 0)
    (hT0 : 0 < T)
    (hδ : 0 < δ)
    (hδwidth : δ ≤ dirichletLTwistedSmoothedQuadraticConditionalDelta A c η q T)
    {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν)
    (νpos : ∀ x > 0, 0 ≤ ν x)
    (suppν : support ν ⊆ Icc (1 / 2) 2)
    (mass_one : ∫ x in Ioi (0 : ℝ), ν x / x = 1)
    {X ε : ℝ} (hX : 0 < X) (hε : 0 < ε) (hε1 : ε < 1) :
    HolomorphicOn (DirichletCharacter.twistedSmoothedPerronIntegrand χ ν ε X)
      (dirichletLTwistedSmoothedQuadraticPointwiseRectangle A c η q T δ) := by
  exact (twistedSmoothedPerronIntegrand_holomorphicOn_quadraticConditionalRectangle
    χ hAA₀ hA hc hη hT hχ hw hw2 hwidthle hzero diffν νpos suppν mass_one hX hε hε1).mono
      (dirichletLTwistedSmoothedQuadraticPointwiseRectangle_subset hT0.le hδ hδwidth)

/-- Exact finite contour shift for the quadratic pointwise rectangle with
variable right edge `1 + δ`. -/
theorem dirichletLTwistedSmoothedPerron_quadraticPointwiseFiniteContourIdentity
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {A A₀ c η T δ : ℝ} (hAA₀ : A ≤ A₀) (hA : 0 < A)
    (hc : 0 < c) (hη : 0 < η) (hT : 0 < T) (hχ : χ ≠ 1)
    (hw : 0 < dirichletLQuadraticConditionalCrossZeroWidth A c η q T)
    (hw2 : dirichletLQuadraticConditionalCrossZeroWidth A c η q T ≤ 1 / 2)
    (hwidthle : dirichletLQuadraticConditionalCrossZeroWidth A c η q T ≤
      dirichletLQuadraticConditionalCrossZeroWidth A₀ c η q T)
    (hzero : ∀ s ∈ dirichletLQuadraticConditionalCrossZeroRectangle A₀ c η q T,
      χ.LFunction s ≠ 0)
    (hT0 : 0 < T)
    (hδ : 0 < δ)
    (hδwidth : δ ≤ dirichletLTwistedSmoothedQuadraticConditionalDelta A c η q T)
    {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν)
    (νpos : ∀ x > 0, 0 ≤ ν x)
    (suppν : support ν ⊆ Icc (1 / 2) 2)
    (mass_one : ∫ x in Ioi (0 : ℝ), ν x / x = 1)
    {X ε : ℝ} (hX : 0 < X) (hε : 0 < ε) (hε1 : ε < 1) :
    VIntegral (DirichletCharacter.twistedSmoothedPerronIntegrand χ ν ε X)
        (1 + δ) (-T) T -
      VIntegral (DirichletCharacter.twistedSmoothedPerronIntegrand χ ν ε X)
        (dirichletLTwistedSmoothedQuadraticConditionalLeft A c η q T) (-T) T =
      HIntegral (DirichletCharacter.twistedSmoothedPerronIntegrand χ ν ε X)
        (dirichletLTwistedSmoothedQuadraticConditionalLeft A c η q T)
        (1 + δ) T -
      HIntegral (DirichletCharacter.twistedSmoothedPerronIntegrand χ ν ε X)
        (dirichletLTwistedSmoothedQuadraticConditionalLeft A c η q T)
        (1 + δ) (-T) := by
  have hz := (twistedSmoothedPerronIntegrand_holomorphicOn_quadraticPointwiseRectangle
    χ hAA₀ hA hc hη hT hχ hw hw2 hwidthle hzero hT0 hδ hδwidth
    diffν νpos suppν mass_one hX hε hε1).vanishesOnRectangle (by rfl)
  norm_num [RectangleIntegral, dirichletLTwistedSmoothedQuadraticPointwiseRectangle] at hz
  linear_combination hz

/-- Contour norms for the variable-right quadratic pointwise rectangle. -/
theorem exists_dirichletLTwistedSmoothedQuadraticPointwiseContourNormBounds
    {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν)
    (suppν : support ν ⊆ Icc (1 / 2) 2) :
    ∃ C > 0, ∀ (Z : ℝ), 0 < Z →
      (∀ (x u : ℝ), 0 < x → x ≤ 1 → u ≠ 0 →
        ‖riemannZeta (1 + x + I * u)‖ ≤
          Z * (1 + Real.log (|u| + 2) + 1 / |u|)) →
      ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
        {A c η T δ ε X : ℝ}, χ ^ 2 = 1 → χ ≠ 1 →
        0 < A → A ≤ c / 256 → A ≤ 1 / 2 →
        A ≤ 1 / (16 * Z * 192 ^ 4) → 0 < η → 3 ≤ T →
        c * (q : ℝ) ^ (-η) ≤ (χ.LFunction 1).re →
        0 < δ → δ ≤ dirichletLTwistedSmoothedQuadraticConditionalDelta A c η q T →
        0 < ε → ε < 1 → 1 ≤ X →
        let Q := (128 * dirichletLQuadraticConditionalCentralH q T ^ 2) /
              (c * (q : ℝ) ^ (-η)) +
            dirichletLQuadraticConditionalFixedH q
                (dirichletLQuadraticConditionalCentralHeight c η q T) T ^ 12 /
              (A * (q : ℝ) ^ (-2 * η))
        let a := dirichletLTwistedSmoothedQuadraticConditionalLeft A c η q T
        ‖VIntegral (DirichletCharacter.twistedSmoothedPerronIntegrand χ ν ε X)
            a (-T) T‖ ≤ C * T * Q * X ^ a / ε ∧
        ‖HIntegral (DirichletCharacter.twistedSmoothedPerronIntegrand χ ν ε X)
            a (1 + δ) T‖ ≤ C * Q * X ^ (1 + δ) / (ε * (1 + T ^ 2)) ∧
        ‖HIntegral (DirichletCharacter.twistedSmoothedPerronIntegrand χ ν ε X)
            a (1 + δ) (-T)‖ ≤ C * Q * X ^ (1 + δ) / (ε * (1 + T ^ 2)) := by
  obtain ⟨M, hM, hMellin⟩ := MellinOfSmooth1b diffν suppν
  obtain ⟨C₀, hC₀, hbase⟩ :=
    exists_dirichletLTwistedSmoothedQuadraticConditionalContourNormBounds diffν suppν
  refine ⟨C₀ + 16 * M, by positivity, ?_⟩
  intro Z hZ hzeta q _ χ A c η T δ ε X hquad hχ hA hAc hAhalf hAsmall hη
    hT hSiegel hδ hδwidth hε hε1 hX
  dsimp only
  let Q := (128 * dirichletLQuadraticConditionalCentralH q T ^ 2) /
        (c * (q : ℝ) ^ (-η)) +
      dirichletLQuadraticConditionalFixedH q
          (dirichletLQuadraticConditionalCentralHeight c η q T) T ^ 12 /
        (A * (q : ℝ) ^ (-2 * η))
  let a := dirichletLTwistedSmoothedQuadraticConditionalLeft A c η q T
  have hX0 : 0 < X := lt_of_lt_of_le zero_lt_one hX
  have hT0 : 0 < T := by linarith
  have hc : 0 < c := by linarith
  have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
  have hw : 0 < dirichletLQuadraticConditionalCrossZeroWidth A c η q T := by
    dsimp only [dirichletLTwistedSmoothedQuadraticConditionalDelta] at hδwidth
    linarith
  have hδ1 : δ ≤ 1 := by
    have hw2 : dirichletLQuadraticConditionalCrossZeroWidth A c η q T ≤ 1 / 2 := by
      have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
      have hq1 : (1 : ℝ) ≤ q := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
      have hcentralH : 0 < dirichletLQuadraticConditionalCentralH q T := by
        dsimp only [dirichletLQuadraticConditionalCentralH]
        have hcut : (1 : ℝ) ≤ dirichletLNonquadraticConductorLogCutoff q T := by
          exact_mod_cast (show 1 ≤ dirichletLNonquadraticConductorLogCutoff q T by
            unfold dirichletLNonquadraticConductorLogCutoff
            exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (NeZero.ne q) (by
              unfold dirichletLNonquadraticConductorLogHeightBlock
              omega)))
        linarith [Real.log_nonneg hcut]
      have hτ : 0 < dirichletLQuadraticConditionalCentralHeight c η q T := by
        dsimp only [dirichletLQuadraticConditionalCentralHeight]
        exact lt_min hT0 (div_pos (mul_pos hc (Real.rpow_pos_of_pos hq _))
          (mul_pos (by norm_num) (sq_pos_of_pos hcentralH)))
      have hH1 : 1 ≤ dirichletLQuadraticConditionalFixedH q
          (dirichletLQuadraticConditionalCentralHeight c η q T) T := by
        dsimp only [dirichletLQuadraticConditionalFixedH]
        have hcut : (1 : ℝ) ≤ dirichletLNonquadraticConductorLogCutoff q T := by
          exact_mod_cast (show 1 ≤ dirichletLNonquadraticConductorLogCutoff q T by
            unfold dirichletLNonquadraticConductorLogCutoff
            exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (NeZero.ne q) (by
              unfold dirichletLNonquadraticConductorLogHeightBlock
              omega)))
        have hlog : 0 ≤ Real.log (dirichletLNonquadraticConductorLogCutoff q T) :=
          Real.log_nonneg hcut
        have hlogT : 0 ≤ Real.log (2 * T + 2) := Real.log_nonneg (by linarith)
        have hinv : 0 < 1 / (2 * dirichletLQuadraticConditionalCentralHeight c η q T) := by
          positivity
        linarith
      have hH : 0 < dirichletLQuadraticConditionalFixedH q
          (dirichletLQuadraticConditionalCentralHeight c η q T) T :=
        lt_of_lt_of_le zero_lt_one hH1
      have hp1 : (q : ℝ) ^ (-2 * η) ≤ 1 := by
        simpa using Real.rpow_le_rpow_of_exponent_le hq1 (by linarith : -2 * η ≤ 0)
      dsimp only [dirichletLQuadraticConditionalCrossZeroWidth]
      calc
        A * (q : ℝ) ^ (-2 * η) /
            dirichletLQuadraticConditionalFixedH q
                (dirichletLQuadraticConditionalCentralHeight c η q T) T ^ 12 ≤ A := by
          rw [div_le_iff₀ (pow_pos hH 12)]
          nlinarith [one_le_pow₀ hH1 (n := 12), mul_le_of_le_one_right hA.le hp1]
        _ ≤ 1 / 2 := hAhalf
    dsimp only [dirichletLTwistedSmoothedQuadraticConditionalDelta] at hδwidth
    linarith
  have hbase' := hbase Z hZ hzeta χ hquad hχ hA hAc hAhalf hAsmall hc hη
    hT hSiegel hε hε1 hX
  have hvertical :
      ‖VIntegral (DirichletCharacter.twistedSmoothedPerronIntegrand χ ν ε X)
          a (-T) T‖ ≤ (C₀ + 16 * M) * T * Q * X ^ a / ε := by
    have hleft := hbase'.1
    have hfactor : 0 ≤ T * Q * X ^ a / ε := by positivity
    have hcoef : C₀ ≤ C₀ + 16 * M := by nlinarith [hM.le]
    calc
      _ ≤ C₀ * T * Q * X ^ a / ε := hleft
      _ ≤ (C₀ + 16 * M) * T * Q * X ^ a / ε := by
        simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
          (mul_le_mul_of_nonneg_right hcoef hfactor)
  have hb :
      1 + δ ≤ dirichletLTwistedSmoothedQuadraticConditionalRight A c η q T := by
    dsimp only [dirichletLTwistedSmoothedQuadraticConditionalRight,
      dirichletLTwistedSmoothedQuadraticConditionalDelta] at hδwidth ⊢
    linarith
  have ha : (1 / 2 : ℝ) ≤ a := by
    dsimp only [a, dirichletLTwistedSmoothedQuadraticConditionalLeft]
    have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
    have hp1 : (q : ℝ) ^ (-2 * η) ≤ 1 := by
      have hq1 : (1 : ℝ) ≤ q := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
      simpa using Real.rpow_le_rpow_of_exponent_le hq1 (by linarith : -2 * η ≤ 0)
    have hcentralH : 0 < dirichletLQuadraticConditionalCentralH q T := by
      dsimp only [dirichletLQuadraticConditionalCentralH]
      have hcut : (1 : ℝ) ≤ dirichletLNonquadraticConductorLogCutoff q T := by
        exact_mod_cast (show 1 ≤ dirichletLNonquadraticConductorLogCutoff q T by
          unfold dirichletLNonquadraticConductorLogCutoff
          exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (NeZero.ne q) (by
            unfold dirichletLNonquadraticConductorLogHeightBlock
            omega)))
      linarith [Real.log_nonneg hcut]
    have hτ : 0 < dirichletLQuadraticConditionalCentralHeight c η q T := by
      dsimp only [dirichletLQuadraticConditionalCentralHeight]
      exact lt_min hT0 (div_pos (mul_pos (show 0 < c by linarith)
        (Real.rpow_pos_of_pos hq _)) (mul_pos (by norm_num) (sq_pos_of_pos hcentralH)))
    have hH1 : 1 ≤ dirichletLQuadraticConditionalFixedH q
        (dirichletLQuadraticConditionalCentralHeight c η q T) T := by
      dsimp only [dirichletLQuadraticConditionalFixedH]
      have hcut : (1 : ℝ) ≤ dirichletLNonquadraticConductorLogCutoff q T := by
        exact_mod_cast (show 1 ≤ dirichletLNonquadraticConductorLogCutoff q T by
          unfold dirichletLNonquadraticConductorLogCutoff
          exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (NeZero.ne q) (by
            unfold dirichletLNonquadraticConductorLogHeightBlock
            omega)))
      have hlog : 0 ≤ Real.log (dirichletLNonquadraticConductorLogCutoff q T) :=
        Real.log_nonneg hcut
      have hlogT : 0 ≤ Real.log (2 * T + 2) := Real.log_nonneg (by linarith)
      have hinv : 0 < 1 / (2 * dirichletLQuadraticConditionalCentralHeight c η q T) := by
        positivity
      linarith
    have hH : 0 < dirichletLQuadraticConditionalFixedH q
        (dirichletLQuadraticConditionalCentralHeight c η q T) T :=
      lt_of_lt_of_le zero_lt_one hH1
    calc
      1 / 2 ≤ 1 - dirichletLQuadraticConditionalCrossZeroWidth A c η q T := by
        dsimp only [dirichletLQuadraticConditionalCrossZeroWidth]
        have hpow : 1 ≤ dirichletLQuadraticConditionalFixedH q
            (dirichletLQuadraticConditionalCentralHeight c η q T) T ^ 12 := one_le_pow₀ hH1
        have hAq : A * (q : ℝ) ^ (-2 * η) ≤ A := mul_le_of_le_one_right hA.le hp1
        have hsmall :
            A * (q : ℝ) ^ (-2 * η) /
              dirichletLQuadraticConditionalFixedH q
                (dirichletLQuadraticConditionalCentralHeight c η q T) T ^ 12 ≤ A := by
          rw [div_le_iff₀ (pow_pos hH 12)]
          nlinarith
        linarith
      _ ≤ a := by rfl
  have horizontalPoint (σ t : ℝ) (hσa : a ≤ σ) (hσb : σ ≤ 1 + δ) (ht' : |t| = T) :
      ‖DirichletCharacter.twistedSmoothedPerronIntegrand χ ν ε X (σ + t * I)‖ ≤
        (2 * Q) * (2 * M / (ε * (1 + T ^ 2))) * X ^ (1 + δ) := by
    have hlog := norm_logDerivative_le_on_quadraticConditionalPerronHorizontal
      Z hZ hzeta χ hquad hχ hA hAc hAhalf hAsmall hc hη
      hT hSiegel ht'
      (by simpa only [a] using hσa) (hσb.trans hb)
    have hm := hMellin (1 / 2) (by norm_num) (σ + t * I)
      (by simp; linarith) (by simp; linarith [hσb, hδ1]) ε hε hε1
    have hnormsq : T ^ 2 ≤ ‖(σ : ℂ) + t * I‖ ^ 2 := by
      rw [Complex.sq_norm]
      simp [Complex.normSq_apply]
      have ht2 := congrArg (fun u : ℝ => u ^ 2) ht'
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
    have hXpow : X ^ σ ≤ X ^ (1 + δ) := Real.rpow_le_rpow_of_exponent_le hX hσb
    dsimp only [DirichletCharacter.twistedSmoothedPerronIntegrand]
    rw [norm_mul, norm_mul, hXnorm]
    have hlog' : ‖-deriv χ.LFunction (σ + I * t) / χ.LFunction (σ + I * t)‖ ≤
        2 * Q := by
      simpa only [neg_div, norm_neg, Q, mul_comm] using hlog
    have hst : ((σ : ℂ) + t * I) = ((σ : ℂ) + I * t) := by ring
    have hlog'' : ‖-deriv χ.LFunction (σ + t * I) / χ.LFunction (σ + t * I)‖ ≤
        2 * Q := by
      simpa only [hst] using hlog'
    calc
      _ ≤ (2 * Q) * (2 * M / (ε * (1 + T ^ 2))) * X ^ σ := by
        have hprod :
            ‖-deriv χ.LFunction (σ + t * I) / χ.LFunction (σ + t * I)‖ *
                ‖mellin (fun x ↦ (Smooth1 ν ε x : ℂ)) (σ + t * I)‖ ≤
              (2 * Q) * (2 * M / (ε * (1 + T ^ 2))) := by
          simpa only [mul_assoc, mul_left_comm] using
            (mul_le_mul hlog'' hm' (norm_nonneg _) (by positivity))
        exact mul_le_mul_of_nonneg_right hprod (Real.rpow_nonneg hX0.le _)
      _ ≤ _ := by gcongr
  have horizontalBound (t : ℝ) (ht' : |t| = T) :
      ‖HIntegral (DirichletCharacter.twistedSmoothedPerronIntegrand χ ν ε X) a (1 + δ) t‖ ≤
        (C₀ + 16 * M) * Q * X ^ (1 + δ) / (ε * (1 + T ^ 2)) := by
    have hab : a ≤ 1 + δ := by
      dsimp only [a, dirichletLTwistedSmoothedQuadraticConditionalLeft]
      linarith
    rw [HIntegral]
    calc
      _ ≤ ((2 * Q) * (2 * M / (ε * (1 + T ^ 2))) * X ^ (1 + δ)) * |(1 + δ) - a| := by
        apply intervalIntegral.norm_integral_le_of_norm_le_const
        intro σ hσ
        rw [uIoc_of_le hab] at hσ
        exact horizontalPoint σ t hσ.1.le hσ.2 ht'
      _ ≤ (C₀ + 16 * M) * Q * X ^ (1 + δ) / (ε * (1 + T ^ 2)) := by
        have hlen : |(1 + δ) - a| ≤ 2 := by
          rw [abs_of_nonneg (sub_nonneg.mpr hab)]
          linarith [ha, hδ1]
        have hden : 0 < ε * (1 + T ^ 2) := by positivity
        calc
          _ ≤ ((2 * Q) * (2 * M / (ε * (1 + T ^ 2))) * X ^ (1 + δ)) * 2 := by
            gcongr
          _ ≤ (C₀ + 16 * M) * Q * X ^ (1 + δ) / (ε * (1 + T ^ 2)) := by
            field_simp [hden.ne']
            nlinarith [Real.rpow_nonneg hX0.le (1 + δ)]
  exact ⟨hvertical,
    horizontalBound T (by simp [abs_of_nonneg hT0.le]),
    horizontalBound (-T) (by rw [abs_neg, abs_of_nonneg hT0.le])⟩

/-- Smoothed quadratic pointwise error assembly at a variable right edge. -/
theorem exists_dirichletLTwistedSmoothedQuadraticPointwiseErrorAssembly
    (c η : ℝ) (hc : 0 < c) (hη : 0 < η)
    {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν)
    (νpos : ∀ x > 0, 0 ≤ ν x)
    (suppν : support ν ⊆ Icc (1 / 2) 2)
    (mass_one : ∫ x in Ioi (0 : ℝ), ν x / x = 1) :
    ∃ A > 0, ∃ K > 0, ∀ {q : ℕ} [NeZero q]
      (χ : DirichletCharacter ℂ q) {T δ ε X : ℝ},
      χ ^ 2 = 1 → χ ≠ 1 → 3 ≤ T →
      c * (q : ℝ) ^ (-η) ≤ (χ.LFunction 1).re →
      0 < δ →
      δ ≤ dirichletLTwistedSmoothedQuadraticConditionalDelta A c η q T →
      0 < ε → ε < 1 → 1 ≤ X →
      let Q := (128 * dirichletLQuadraticConditionalCentralH q T ^ 2) /
            (c * (q : ℝ) ^ (-η)) +
          dirichletLQuadraticConditionalFixedH q
              (dirichletLQuadraticConditionalCentralHeight c η q T) T ^ 12 /
            (A * (q : ℝ) ^ (-2 * η))
      let a := dirichletLTwistedSmoothedQuadraticConditionalLeft A c η q T
      ‖DirichletCharacter.twistedSmoothedPsi χ ν ε X‖ ≤
        K * (T * Q * X ^ a / ε +
          Q * X ^ (1 + δ) / (ε * (1 + T ^ 2)) +
          X ^ (1 + δ) * (1 + δ⁻¹ ^ 2) / (ε * T)) := by
  obtain ⟨Z, hZ, hzeta⟩ := zeta_pole_plus_log_bound
  obtain ⟨A₀, hA₀, hzero⟩ :=
    exists_LFunction_ne_zero_on_quadraticConditionalCrossZeroRectangle c η hc hη
  let A : ℝ := min A₀ (min (c / 256) (min (1 / 2) (1 / (16 * Z * 192 ^ 4))))
  have hA : 0 < A := by
    dsimp only [A]
    exact lt_min hA₀ (lt_min (div_pos hc (by norm_num))
      (lt_min (by norm_num) (by positivity)))
  have hAA₀ : A ≤ A₀ := min_le_left _ _
  have hAc : A ≤ c / 256 := (min_le_right _ _).trans (min_le_left _ _)
  have hAhalf : A ≤ 1 / 2 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hAsmall : A ≤ 1 / (16 * Z * 192 ^ 4) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨C, hC, hcontour⟩ :=
    exists_dirichletLTwistedSmoothedQuadraticPointwiseContourNormBounds diffν suppν
  obtain ⟨Ctail, hCtail, htails⟩ :=
    DirichletCharacter.twistedSmoothedPerron_right_tails_quantitative
      diffν νpos suppν mass_one
  refine ⟨A, hA, 2 * (C + Ctail), by positivity, ?_⟩
  intro q _ χ T δ ε X hquad hχ hT hSiegel hδ hδwidth hε hε1 hX
  dsimp only
  let Q := (128 * dirichletLQuadraticConditionalCentralH q T ^ 2) /
        (c * (q : ℝ) ^ (-η)) +
      dirichletLQuadraticConditionalFixedH q
          (dirichletLQuadraticConditionalCentralHeight c η q T) T ^ 12 /
        (A * (q : ℝ) ^ (-2 * η))
  let a := dirichletLTwistedSmoothedQuadraticConditionalLeft A c η q T
  let F := DirichletCharacter.twistedSmoothedPerronIntegrand χ ν ε X
  let Eleft := T * Q * X ^ a / ε
  let Ehoriz := Q * X ^ (1 + δ) / (ε * (1 + T ^ 2))
  let Etail := X ^ (1 + δ) * (1 + δ⁻¹ ^ 2) / (ε * T)
  have hT0 : 0 < T := by linarith
  have hT1 : 1 ≤ T := by linarith
  have hX0 : 0 < X := lt_of_lt_of_le zero_lt_one hX
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hq1 : (1 : ℝ) ≤ q := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hcut : (1 : ℝ) ≤ dirichletLNonquadraticConductorLogCutoff q T := by
    exact_mod_cast (show 1 ≤ dirichletLNonquadraticConductorLogCutoff q T by
      unfold dirichletLNonquadraticConductorLogCutoff
      exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (NeZero.ne q) (by
        unfold dirichletLNonquadraticConductorLogHeightBlock
        omega)))
  have hcentralH : 0 < dirichletLQuadraticConditionalCentralH q T := by
    dsimp only [dirichletLQuadraticConditionalCentralH]
    linarith [Real.log_nonneg hcut]
  have hτ : 0 < dirichletLQuadraticConditionalCentralHeight c η q T := by
    dsimp only [dirichletLQuadraticConditionalCentralHeight]
    exact lt_min hT0 (div_pos (mul_pos hc (Real.rpow_pos_of_pos hq _))
      (mul_pos (by norm_num) (sq_pos_of_pos hcentralH)))
  have hH1 : 1 ≤ dirichletLQuadraticConditionalFixedH q
      (dirichletLQuadraticConditionalCentralHeight c η q T) T := by
    dsimp only [dirichletLQuadraticConditionalFixedH]
    have hlog : 0 ≤ Real.log (dirichletLNonquadraticConductorLogCutoff q T) :=
      Real.log_nonneg hcut
    have hlogT : 0 ≤ Real.log (2 * T + 2) := Real.log_nonneg (by linarith)
    have hinv : 0 < 1 / (2 * dirichletLQuadraticConditionalCentralHeight c η q T) := by
      positivity
    linarith
  have hH : 0 < dirichletLQuadraticConditionalFixedH q
      (dirichletLQuadraticConditionalCentralHeight c η q T) T :=
    lt_of_lt_of_le zero_lt_one hH1
  have hw : 0 < dirichletLQuadraticConditionalCrossZeroWidth A c η q T := by
    dsimp only [dirichletLQuadraticConditionalCrossZeroWidth]
    positivity
  have hw2 : dirichletLQuadraticConditionalCrossZeroWidth A c η q T ≤ 1 / 2 := by
    have hp1 : (q : ℝ) ^ (-2 * η) ≤ 1 := by
      simpa using Real.rpow_le_rpow_of_exponent_le hq1 (by linarith : -2 * η ≤ 0)
    dsimp only [dirichletLQuadraticConditionalCrossZeroWidth]
    calc
      A * (q : ℝ) ^ (-2 * η) /
          dirichletLQuadraticConditionalFixedH q
              (dirichletLQuadraticConditionalCentralHeight c η q T) T ^ 12 ≤ A := by
        rw [div_le_iff₀ (pow_pos hH 12)]
        nlinarith [one_le_pow₀ hH1 (n := 12), mul_le_of_le_one_right hA.le hp1]
      _ ≤ 1 / 2 := hAhalf
  have hwidthle : dirichletLQuadraticConditionalCrossZeroWidth A c η q T ≤
      dirichletLQuadraticConditionalCrossZeroWidth A₀ c η q T := by
    dsimp only [dirichletLQuadraticConditionalCrossZeroWidth]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hAA₀ (Real.rpow_nonneg hq.le _))
      (pow_nonneg hH.le 12)
  have hδ1 : δ ≤ 1 := by
    dsimp only [dirichletLTwistedSmoothedQuadraticConditionalDelta] at hδwidth
    linarith
  have hf : Integrable (fun t : ℝ => F (((1 + δ : ℝ) : ℂ) + t * I)) := by
    simpa only [F] using
      (DirichletCharacter.twistedSmoothedPerronIntegrand_integrable_right
        (q := q) (σ := 1 + δ) (X := X) (ε := ε) χ diffν νpos suppν mass_one
        hX0 hε hε1 (by linarith) (by linarith [hδ1]))
  have hp := DirichletCharacter.twistedSmoothedPerron χ diffν νpos suppν mass_one
    hX0 hε hε1 (σ := 1 + δ) (by linarith) (by linarith [hδ1])
  have ht := htails χ hδ hδ1 hε hε1 hX0 hT1
  have hct := hcontour Z hZ hzeta χ hquad hχ hA hAc hAhalf hAsmall hη hT
    hSiegel hδ hδwidth hε hε1 hX
  have hshift := dirichletLTwistedSmoothedPerron_quadraticPointwiseFiniteContourIdentity
    χ hAA₀ hA hc hη hT0 hχ hw hw2 hwidthle
      (hzero q χ T hquad hχ hT0 hSiegel) hT0 hδ hδwidth
      diffν νpos suppν mass_one hX0 hε hε1
  have hsplit := quadratic_integral_lower_middle_upper
    (fun t : ℝ => F (((1 + δ : ℝ) : ℂ) + t * I)) hf hT0.le
  have htlow : ‖∫ t in Iic (-T), F (((1 + δ : ℝ) : ℂ) + t * I)‖ ≤ Ctail * Etail := by
    dsimp only [F, Etail]
    convert ht.1 using 1 <;> ring
  have htupper : ‖∫ t in Ici T, F (((1 + δ : ℝ) : ℂ) + t * I)‖ ≤ Ctail * Etail := by
    dsimp only [F, Etail]
    convert ht.2 using 1 <;> ring
  have hmid : ‖∫ t in Ioc (-T) T, F (((1 + δ : ℝ) : ℂ) + t * I)‖ =
      ‖VIntegral F (1 + δ) (-T) T‖ := by
    rw [VIntegral, norm_smul, norm_I, one_mul,
      intervalIntegral.integral_of_le (by linarith : -T ≤ T)]
  have hv : ‖VIntegral F (1 + δ) (-T) T‖ ≤ C * Eleft + C * Ehoriz + C * Ehoriz := by
    have heq : VIntegral F (1 + δ) (-T) T =
        VIntegral F a (-T) T + HIntegral F a (1 + δ) T -
          HIntegral F a (1 + δ) (-T) := by
      simpa only [F, a] using (by linear_combination hshift)
    have hleft : ‖VIntegral F a (-T) T‖ ≤ C * Eleft := by
      dsimp only [F, a, Eleft, Q]
      convert hct.1 using 1 <;> (try ring)
    have htop : ‖HIntegral F a (1 + δ) T‖ ≤ C * Ehoriz := by
      dsimp only [F, a, Ehoriz, Q]
      convert hct.2.1 using 1 <;> (try ring)
    have hbottom : ‖HIntegral F a (1 + δ) (-T)‖ ≤ C * Ehoriz := by
      dsimp only [F, a, Ehoriz, Q]
      convert hct.2.2 using 1 <;> (try ring)
    rw [heq]
    calc
      _ ≤ ‖VIntegral F a (-T) T‖ + ‖HIntegral F a (1 + δ) T‖ +
          ‖HIntegral F a (1 + δ) (-T)‖ := by
        calc
          _ ≤ ‖VIntegral F a (-T) T + HIntegral F a (1 + δ) T‖ +
              ‖HIntegral F a (1 + δ) (-T)‖ := by
            simpa only [sub_eq_add_neg, norm_neg] using
              norm_add_le (VIntegral F a (-T) T + HIntegral F a (1 + δ) T)
                (-HIntegral F a (1 + δ) (-T))
          _ ≤ _ := add_le_add (norm_add_le _ _) (le_refl _)
      _ ≤ C * Eleft + C * Ehoriz + C * Ehoriz :=
        add_le_add (add_le_add hleft htop) hbottom
  have hfull : ‖∫ t : ℝ, F (((1 + δ : ℝ) : ℂ) + t * I)‖ ≤
      Ctail * Etail + (C * Eleft + C * Ehoriz + C * Ehoriz) + Ctail * Etail := by
    rw [← hsplit]
    calc
      _ ≤ ‖∫ t in Iic (-T), F (((1 + δ : ℝ) : ℂ) + t * I)‖ +
          ‖∫ t in Ioc (-T) T, F (((1 + δ : ℝ) : ℂ) + t * I)‖ +
          ‖∫ t in Ici T, F (((1 + δ : ℝ) : ℂ) + t * I)‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (le_refl _))
      _ ≤ _ := by rw [hmid]; exact add_le_add (add_le_add htlow hv) htupper
  have hnorm : ‖(1 / (2 * (Real.pi : ℂ) * I) : ℂ)‖ ≤ 1 := by
    rw [norm_div, norm_one, norm_mul, norm_mul, Complex.norm_ofNat,
      Complex.norm_real, norm_I]
    norm_num
    rw [abs_of_pos Real.pi_pos]
    have hinv : Real.pi⁻¹ ≤ 1 :=
      (inv_le_one₀ Real.pi_pos).2 (by linarith [Real.pi_gt_three])
    nlinarith [inv_nonneg.mpr Real.pi_pos.le]
  have hnormalized : ‖VerticalIntegral' F (1 + δ)‖ ≤
      ‖∫ t : ℝ, F (((1 + δ : ℝ) : ℂ) + t * I)‖ := by
    rw [VerticalIntegral', VerticalIntegral, norm_smul, norm_smul, norm_I, one_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) hnorm
  have hEleft : 0 ≤ Eleft := by dsimp only [Eleft, Q]; positivity
  have hEhoriz : 0 ≤ Ehoriz := by dsimp only [Ehoriz, Q]; positivity
  have hEtail : 0 ≤ Etail := by dsimp only [Etail]; positivity
  rw [hp]
  change ‖VerticalIntegral' F (1 + δ)‖ ≤ _
  calc
    _ ≤ ‖∫ t : ℝ, F (((1 + δ : ℝ) : ℂ) + t * I)‖ := hnormalized
    _ ≤ Ctail * Etail + (C * Eleft + C * Ehoriz + C * Ehoriz) +
        Ctail * Etail := hfull
    _ ≤ 2 * (C + Ctail) * (Eleft + Ehoriz + Etail) := by
      nlinarith [mul_nonneg hC.le hEleft, mul_nonneg hC.le hEhoriz,
        mul_nonneg hCtail.le hEtail]
    _ = _ := by rfl

/-- Exact-prefix closure once the four variable-right quadratic payments are
paid by a common ambient target `R`. -/
theorem exists_quadraticPointwiseExactPrefix_of_four_payments
    (c η : ℝ) (hc : 0 < c) (hη : 0 < η)
    {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν)
    (νpos : ∀ x > 0, 0 ≤ ν x)
    (suppν : support ν ⊆ Icc (1 / 2) 2)
    (mass_one : ∫ x in Ioi (0 : ℝ), ν x / x = 1) :
    ∃ A > 0, ∃ K > 0, ∀ {q : ℕ} [NeZero q]
      (χ : DirichletCharacter ℂ q) {T δ ε X R : ℝ},
      χ ^ 2 = 1 → χ ≠ 1 → 3 ≤ T →
      c * (q : ℝ) ^ (-η) ≤ (χ.LFunction 1).re →
      0 < δ →
      δ ≤ dirichletLTwistedSmoothedQuadraticConditionalDelta A c η q T →
      0 < ε → ε < 1 → 3 < X → 2 < X * ε → 0 ≤ R →
      let Q := (128 * dirichletLQuadraticConditionalCentralH q T ^ 2) /
            (c * (q : ℝ) ^ (-η)) +
          dirichletLQuadraticConditionalFixedH q
              (dirichletLQuadraticConditionalCentralHeight c η q T) T ^ 12 /
            (A * (q : ℝ) ^ (-2 * η))
      let a := dirichletLTwistedSmoothedQuadraticConditionalLeft A c η q T
      T * Q * X ^ a / ε ≤ R →
      Q * X ^ (1 + δ) / (ε * (1 + T ^ 2)) ≤ R →
      X ^ (1 + δ) * (1 + δ⁻¹ ^ 2) / (ε * T) ≤ R →
      ε * X * Real.log X ≤ R →
      ‖lambdaCharacterPrefix ⌊X⌋₊ q χ‖ ≤ K * R := by
  obtain ⟨A, hA, K₀, hK₀, herror⟩ :=
    exists_dirichletLTwistedSmoothedQuadraticPointwiseErrorAssembly
      c η hc hη diffν νpos suppν mass_one
  obtain ⟨C, hC, hclose⟩ :=
    exists_uniform_twistedSmoothedPsiClose diffν suppν νpos mass_one
  refine ⟨A, hA, 3 * K₀ + C + 1, by positivity, ?_⟩
  intro q _ χ T δ ε X R hquad hχ hT hSiegel hδ hδwidth hε hε1 hX hXε hR
  intro Q a hleft hhoriz htail hsmooth
  have hs := herror χ hquad hχ hT hSiegel hδ hδwidth hε hε1 (by linarith : 1 ≤ X)
  have hcclose := hclose χ X hX ε hε hε1 hXε
  have hsmoothed : ‖DirichletCharacter.twistedSmoothedPsi χ ν ε X‖ ≤ 3 * K₀ * R := by
    calc
      _ ≤ K₀ * (T * Q * X ^ a / ε + Q * X ^ (1 + δ) / (ε * (1 + T ^ 2)) +
          X ^ (1 + δ) * (1 + δ⁻¹ ^ 2) / (ε * T)) := by simpa only using hs
      _ ≤ K₀ * (R + R + R) := by gcongr
      _ = 3 * K₀ * R := by ring
  have hremove : ‖DirichletCharacter.twistedSmoothedPsi χ ν ε X -
      lambdaCharacterPrefix ⌊X⌋₊ q χ‖ ≤ C * R := by
    calc
      _ ≤ C * ε * X * Real.log X := hcclose
      _ = C * (ε * X * Real.log X) := by ring
      _ ≤ C * R := mul_le_mul_of_nonneg_left hsmooth hC.le
  calc
    ‖lambdaCharacterPrefix ⌊X⌋₊ q χ‖ =
        ‖DirichletCharacter.twistedSmoothedPsi χ ν ε X -
          (DirichletCharacter.twistedSmoothedPsi χ ν ε X -
            lambdaCharacterPrefix ⌊X⌋₊ q χ)‖ := by ring_nf
    _ ≤ ‖DirichletCharacter.twistedSmoothedPsi χ ν ε X‖ +
        ‖DirichletCharacter.twistedSmoothedPsi χ ν ε X -
          lambdaCharacterPrefix ⌊X⌋₊ q χ‖ := norm_sub_le _ _
    _ ≤ 3 * K₀ * R + C * R := add_le_add hsmoothed hremove
    _ ≤ (3 * K₀ + C + 1) * R := by nlinarith

/-- The small exponent selected before `q, χ`; it depends only on the target
loss parameters. -/
def quadraticPointwiseSWEta (C D : ℕ) : ℝ :=
  (4096 * (C + D + 1 : ℝ))⁻¹

private theorem quadraticPointwiseSWEta_pos (C D : ℕ) :
    0 < quadraticPointwiseSWEta C D := by
  dsimp [quadraticPointwiseSWEta]
  positivity

private theorem quadraticPointwiseSWEta_mul_C_le (C D : ℕ) :
    (C : ℝ) * quadraticPointwiseSWEta C D ≤ (1 / 4096 : ℝ) := by
  dsimp [quadraticPointwiseSWEta]
  have hden : 0 < (4096 : ℝ) * (C + D + 1 : ℝ) := by positivity
  rw [inv_eq_one_div]
  field_simp [hden.ne']
  nlinarith

private theorem two_mul_quadraticPointwiseSWEta_mul_C_le (C D : ℕ) :
    (2 * (C : ℝ)) * quadraticPointwiseSWEta C D ≤ (1 / 2048 : ℝ) := by
  have h := quadraticPointwiseSWEta_mul_C_le C D
  nlinarith

private theorem eventually_const_le_log_rpow (K θ : ℝ) (hθ : 0 < θ) :
    ∀ᶠ N : ℕ in atTop, K ≤ Real.log (N : ℝ) ^ θ := by
  have ht : Tendsto (fun N : ℕ => Real.log (N : ℝ) ^ θ) atTop atTop :=
    (tendsto_rpow_atTop hθ).comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  exact ht.eventually (eventually_ge_atTop K)

private theorem eventually_loglog_le_mul_log_rpow (K θ : ℝ)
    (hK : 0 < K) (hθ : 0 < θ) :
    ∀ᶠ N : ℕ in atTop,
      Real.log (Real.log (N : ℝ)) ≤ K * Real.log (N : ℝ) ^ θ := by
  have hsmall := (isLittleO_log_rpow_rpow_atTop (1 : ℝ) hθ).bound hK
  have hlogtop : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsmallN :
      ∀ᶠ N : ℕ in atTop,
        ‖Real.log (Real.log (N : ℝ)) ^ (1 : ℝ)‖ ≤
          K * ‖Real.log (N : ℝ) ^ θ‖ := hlogtop.eventually hsmall
  filter_upwards [hsmallN, hlogtop.eventually (eventually_ge_atTop (Real.exp 1))] with
      N hsmallN hlog
  have hLpos : 0 < Real.log (N : ℝ) :=
    lt_of_lt_of_le (Real.exp_pos 1) hlog
  have hL1 : 1 ≤ Real.log (N : ℝ) := by
    have hexp1 : (1 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    exact hexp1.trans hlog
  have hznonneg : 0 ≤ Real.log (Real.log (N : ℝ)) := Real.log_nonneg hL1
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hznonneg (1 : ℝ)),
    Real.norm_of_nonneg (Real.rpow_nonneg hLpos.le θ), Real.rpow_one] at hsmallN
  simpa only using hsmallN

private theorem eventually_log_rpow_mul_exp_le_one
    (A c β : ℝ) (hA : 0 < A) (hc : 0 < c) (hβ : 0 < β) :
    ∀ᶠ x : ℝ in Filter.atTop,
      Real.log x ^ A * Real.exp (-c * Real.log x ^ β) ≤ 1 := by
  have hsmall :=
    Real.tendsto_log_atTop.eventually
      ((isLittleO_log_rpow_atTop hβ).bound (div_pos hc hA))
  filter_upwards [hsmall, Filter.eventually_gt_atTop (Real.exp 1)] with x hx hxlarge
  have hx1 : 1 < x := by
    have : (1 : ℝ) < Real.exp 1 := by simpa using Real.exp_lt_exp.mpr (zero_lt_one)
    linarith
  have hlog : 0 < Real.log x := Real.log_pos hx1
  have hlogone : 1 < Real.log x := by
    rw [← Real.log_exp 1]
    exact Real.log_lt_log (Real.exp_pos 1) hxlarge
  have hpow0 : 0 ≤ Real.log x ^ β := Real.rpow_nonneg hlog.le _
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hlogone.le),
    Real.norm_eq_abs, abs_of_nonneg hpow0] at hx
  have hscaled : A * Real.log (Real.log x) ≤ c * Real.log x ^ β := by
    calc
      A * Real.log (Real.log x) ≤ A * ((c / A) * Real.log x ^ β) :=
        mul_le_mul_of_nonneg_left hx hA.le
      _ = c * Real.log x ^ β := by field_simp
  rw [Real.rpow_def_of_pos hlog, ← Real.exp_add]
  calc
    Real.exp (Real.log (Real.log x) * A + -c * Real.log x ^ β) ≤ Real.exp 0 := by
      rw [Real.exp_le_exp]
      nlinarith
    _ = 1 := Real.exp_zero

set_option maxHeartbeats 1600000
/-- Uniform coarse control of the two genuinely quadratic scales.  In
particular this expands the `τ⁻¹` contribution inside `FixedH`; it is not a
scalar-payment assumption. -/
private theorem eventually_quadraticPointwiseSW_scale_bounds
    (c A : ℝ) (hc : 0 < c) (hA : 0 < A) (C D : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ q : ℕ, ∀ _inst : NeZero q,
      q ≤ logConductorThreshold N C →
      let P := D + 40
      let T := nonquadraticPointwiseSWHeight P N
      let H := dirichletLQuadraticConditionalFixedH q
        (dirichletLQuadraticConditionalCentralHeight c (quadraticPointwiseSWEta C D) q T) T
      let Q := (128 * dirichletLQuadraticConditionalCentralH q T ^ 2) /
            (c * (q : ℝ) ^ (-quadraticPointwiseSWEta C D)) +
          H ^ 12 / (A * (q : ℝ) ^ (-2 * quadraticPointwiseSWEta C D))
      H ≤ Real.log (N : ℝ) ^ (1 / 1024 : ℝ) ∧
      Q ≤ Real.log (N : ℝ) ∧
      Real.log (N : ℝ) ^ (-1 / 8 : ℝ) ≤
        dirichletLQuadraticConditionalCrossZeroWidth A c
          (quadraticPointwiseSWEta C D) q T := by
  let P := D + 40
  let B := nonquadraticPointwiseSWHeightExponent P
  let Alog : ℝ := C + B + 3
  let η := quadraticPointwiseSWEta C D
  let θ : ℝ := 1 / 8192
  let KH : ℝ := Alog + (B + 3) + 1 + (128 / c) * Alog ^ 2
  let KQ : ℝ := 128 / c * Alog ^ 2 + 1 / A + 1
  have hη : 0 < η := quadraticPointwiseSWEta_pos C D
  have hθ : 0 < θ := by dsimp only [θ]; norm_num
  have hKH : 0 < KH := by dsimp only [KH, Alog]; positivity
  have hKQ : 0 < KQ := by dsimp only [KQ]; positivity
  have hlogtop : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hz := eventually_loglog_le_mul_log_rpow 1 θ (by norm_num) hθ
  have hKHgrow := eventually_const_le_log_rpow KH θ hθ
  have hKQgrow := eventually_const_le_log_rpow KQ (1 / 16 : ℝ) (by norm_num)
  have hAgrow := eventually_const_le_log_rpow (1 / A) (1 / 16 : ℝ) (by norm_num)
  have hTgrow := eventually_const_le_log_rpow (c / 256) (B : ℝ) (by
    dsimp only [B, P, nonquadraticPointwiseSWHeightExponent]
    positivity)
  filter_upwards [hz, hKHgrow, hKQgrow, hAgrow, hTgrow,
      hlogtop.eventually (eventually_ge_atTop (Real.exp 1)),
      eventually_ge_atTop (2 : ℕ)] with N hz hKHgrow hKQgrow hAgrow hTgrow hLlarge hN2
  intro q _inst hqN
  let L := Real.log (N : ℝ)
  let z := Real.log L
  let T := nonquadraticPointwiseSWHeight P N
  let H0 := dirichletLQuadraticConditionalCentralH q T
  let τ := dirichletLQuadraticConditionalCentralHeight c η q T
  let H := dirichletLQuadraticConditionalFixedH q τ T
  let Q := (128 * H0 ^ 2) / (c * (q : ℝ) ^ (-η)) +
    H ^ 12 / (A * (q : ℝ) ^ (-2 * η))
  have hLpos : 0 < L := lt_of_lt_of_le (Real.exp_pos 1) hLlarge
  have hL1 : 1 ≤ L :=
    (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 1)).le.trans hLlarge
  have hz0 : 0 ≤ z := Real.log_nonneg hL1
  have hqpos : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hqpow : (q : ℝ) ≤ L ^ C := by
    calc
      (q : ℝ) ≤ logConductorThreshold N C := by exact_mod_cast hqN
      _ ≤ L ^ C := by
        dsimp only [logConductorThreshold, L]
        exact_mod_cast Nat.floor_le (pow_nonneg hLpos.le C)
  have hqη : (q : ℝ) ^ η ≤ L ^ (1 / 4096 : ℝ) := by
    calc
      (q : ℝ) ^ η ≤ (L ^ C) ^ η := Real.rpow_le_rpow hqpos.le hqpow hη.le
      _ = L ^ ((C : ℝ) * η) := by
        rw [← Real.rpow_natCast, Real.rpow_mul hLpos.le]
      _ ≤ L ^ (1 / 4096 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hL1
          (quadraticPointwiseSWEta_mul_C_le C D)
  have hq2η : (q : ℝ) ^ (2 * η) ≤ L ^ (1 / 2048 : ℝ) := by
    calc
      (q : ℝ) ^ (2 * η) ≤ (L ^ C) ^ (2 * η) :=
        Real.rpow_le_rpow hqpos.le hqpow (mul_nonneg (by norm_num) hη.le)
      _ = L ^ ((C : ℝ) * (2 * η)) := by
        rw [← Real.rpow_natCast, Real.rpow_mul hLpos.le]
      _ = L ^ ((2 * (C : ℝ)) * η) := by ring_nf
      _ ≤ L ^ (1 / 2048 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hL1
          (two_mul_quadraticPointwiseSWEta_mul_C_le C D)
  have hqneg : (q : ℝ) ^ (-η) = ((q : ℝ) ^ η)⁻¹ :=
    Real.rpow_neg hqpos.le η
  have hq2neg : (q : ℝ) ^ (-2 * η) = ((q : ℝ) ^ (2 * η))⁻¹ := by
    rw [show -2 * η = -(2 * η) by ring]
    exact Real.rpow_neg hqpos.le (2 * η)
  have hH0bound : H0 ≤ Alog * z := by
    convert (dirichletLTwistedSmoothedConductorLogLM_le_loglog_pointwise
      C P N q hLlarge hqN) using 1 <;>
      norm_num [H0, T, Alog, B, z, L,
        dirichletLQuadraticConditionalCentralH,
        dirichletLTwistedSmoothedConductorLogLM,
        dirichletLTwistedSmoothedConductorLogCutoff]
  have hcut1 : (1 : ℝ) ≤ dirichletLNonquadraticConductorLogCutoff q T := by
    exact_mod_cast (show 1 ≤ dirichletLNonquadraticConductorLogCutoff q T by
      dsimp only [dirichletLNonquadraticConductorLogCutoff,
        dirichletLNonquadraticConductorLogHeightBlock]
      exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (NeZero.ne q) (by omega)))
  have hH01 : 1 ≤ H0 := by
    dsimp only [H0, dirichletLQuadraticConditionalCentralH]
    linarith [Real.log_nonneg hcut1]
  have hT : T = L ^ B := rfl
  have hT1 : 1 ≤ T := by rw [hT]; exact one_le_pow₀ hL1
  have hlogT : Real.log (2 * T + 2) ≤ (B + 3 : ℝ) * z := by
    have harg : 2 * T + 2 ≤ 4 * T := by nlinarith
    have hlogarg := Real.log_le_log (by positivity : 0 < 2 * T + 2) harg
    rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) (by positivity : T ≠ 0)] at hlogarg
    have hlogT' : Real.log T = (B : ℝ) * z := by
      rw [hT, Real.log_pow]
    rw [hlogT'] at hlogarg
    have hlog4 : Real.log (4 : ℝ) ≤ 2 * z := by
      have hz1 : 1 ≤ z := (Real.le_log_iff_exp_le hLpos).2 hLlarge
      have hlog4two : Real.log (4 : ℝ) = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 * 2 by norm_num,
          Real.log_mul (by norm_num) (by norm_num)]
        ring
      rw [hlog4two]
      nlinarith [Real.log_two_lt_d9]
    nlinarith
  have hτeq : τ = c * (q : ℝ) ^ (-η) / (256 * H0 ^ 2) := by
    dsimp only [τ, dirichletLQuadraticConditionalCentralHeight]
    apply min_eq_right
    have hqneg1 : (q : ℝ) ^ (-η) ≤ 1 := by
      simpa only [← Real.rpow_zero q] using
        Real.rpow_le_rpow_of_exponent_le hq1 (by linarith : -η ≤ 0)
    have hfrac : c * (q : ℝ) ^ (-η) / (256 * H0 ^ 2) ≤ c / 256 := by
      rw [div_le_iff₀ (by positivity : 0 < 256 * H0 ^ 2)]
      have hcq : c * (q : ℝ) ^ (-η) ≤ c := mul_le_of_le_one_right hc.le hqneg1
      have hsq : 1 ≤ H0 ^ 2 := by nlinarith [sq_nonneg (H0 - 1)]
      nlinarith
    rw [hT]
    exact hfrac.trans (by simpa only [L, Real.rpow_natCast] using hTgrow)
  have hτpos : 0 < τ := by rw [hτeq]; positivity
  have hinvτ : 1 / (2 * τ) = (128 / c) * H0 ^ 2 * (q : ℝ) ^ η := by
    rw [hτeq, hqneg]
    field_simp [hc.ne', hqpos.ne', ne_of_gt (Real.rpow_pos_of_pos hqpos η)]
    ring
  have hzsmall : z ≤ L ^ θ := by simpa only [L, z, one_mul] using hz
  have hH0small : H0 ≤ Alog * L ^ θ := hH0bound.trans
    (mul_le_mul_of_nonneg_left hzsmall (by dsimp only [Alog]; positivity))
  have hH0sq : H0 ^ 2 ≤ Alog ^ 2 * L ^ (2 * θ) := by
    have hpθ2 : (L ^ θ) ^ 2 = L ^ (2 * θ) := by
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul hLpos.le]
      ring_nf
    calc
      H0 ^ 2 ≤ (Alog * L ^ θ) ^ 2 :=
        pow_le_pow_left₀ (le_trans (by norm_num) hH01) hH0small 2
      _ = Alog ^ 2 * L ^ (2 * θ) := by rw [mul_pow, hpθ2]
  have hqη' : (q : ℝ) ^ η ≤ L ^ (2 * θ) := by
    rw [show 2 * θ = (1 / 4096 : ℝ) by norm_num [θ]]
    exact hqη
  have hprod : H0 ^ 2 * (q : ℝ) ^ η ≤ Alog ^ 2 * L ^ (4 * θ) := by
    have hpadd : L ^ (2 * θ) * L ^ (2 * θ) = L ^ (4 * θ) := by
      rw [← Real.rpow_add hLpos]
      ring_nf
    calc
      _ ≤ (Alog ^ 2 * L ^ (2 * θ)) * L ^ (2 * θ) := by gcongr
      _ = Alog ^ 2 * L ^ (4 * θ) := by rw [mul_assoc, hpadd]
  have hHbound0 : H ≤ KH * L ^ (4 * θ) := by
    have hpowθ1 : L ^ θ ≤ L ^ (4 * θ) :=
      Real.rpow_le_rpow_of_exponent_le hL1 (by nlinarith [hθ])
    dsimp only [H, dirichletLQuadraticConditionalFixedH]
    rw [show 1 + Real.log (dirichletLNonquadraticConductorLogCutoff q T) = H0 by rfl,
      hinvτ]
    have hH0coarse : H0 ≤ Alog * L ^ (4 * θ) := hH0small.trans
      (mul_le_mul_of_nonneg_left hpowθ1 (by dsimp only [Alog]; positivity))
    have hlogcoarse : Real.log (2 * T + 2) ≤ (B + 3 : ℝ) * L ^ (4 * θ) :=
      hlogT.trans (mul_le_mul_of_nonneg_left
        (hzsmall.trans hpowθ1) (by positivity))
    have hLpow1 : 1 ≤ L ^ (4 * θ) := Real.one_le_rpow hL1 (by positivity)
    have hcoef : 0 ≤ 128 / c := by positivity
    have hinvcoarse : (128 / c) * H0 ^ 2 * (q : ℝ) ^ η ≤
        (128 / c) * (Alog ^ 2 * L ^ (4 * θ)) := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hprod hcoef
    calc
      H0 + (1 + Real.log (2 * T + 2) + (128 / c) * H0 ^ 2 * (q : ℝ) ^ η) ≤
          Alog * L ^ (4 * θ) +
            (1 * L ^ (4 * θ) + (B + 3 : ℝ) * L ^ (4 * θ) +
              (128 / c) * (Alog ^ 2 * L ^ (4 * θ))) := by
        exact add_le_add hH0coarse
          (add_le_add (add_le_add (by simpa only [one_mul] using hLpow1) hlogcoarse)
            hinvcoarse)
      _ = KH * L ^ (4 * θ) := by dsimp only [KH]; ring
  have hHbound : H ≤ L ^ (5 * θ) := by
    calc
      H ≤ KH * L ^ (4 * θ) := hHbound0
      _ ≤ L ^ θ * L ^ (4 * θ) := by gcongr
      _ = L ^ (5 * θ) := by rw [← Real.rpow_add hLpos]; ring_nf
  have hHpos : 0 < H := by
    dsimp only [H, dirichletLQuadraticConditionalFixedH]
    have hlogcut0 : 0 ≤ Real.log (dirichletLNonquadraticConductorLogCutoff q T) :=
      Real.log_nonneg hcut1
    have hlogT0 : 0 ≤ Real.log (2 * T + 2) := Real.log_nonneg (by linarith [hT1])
    have hinv0 : 0 < 1 / (2 * τ) := by positivity
    linarith
  have hH12 : H ^ 12 ≤ L ^ (60 * θ) := by
    calc
      H ^ 12 ≤ (L ^ (5 * θ)) ^ 12 := pow_le_pow_left₀ hHpos.le hHbound 12
      _ = L ^ (60 * θ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hLpos.le]
        norm_num
  have hq2η' : (q : ℝ) ^ (2 * η) ≤ L ^ (4 * θ) := by
    rw [show 4 * θ = (1 / 2048 : ℝ) by norm_num [θ]]
    exact hq2η
  have hprod64 : H ^ 12 * (q : ℝ) ^ (2 * η) ≤ L ^ (64 * θ) := by
    calc
      _ ≤ L ^ (60 * θ) * L ^ (4 * θ) := by gcongr
      _ = L ^ (64 * θ) := by rw [← Real.rpow_add hLpos]; ring_nf
  have hQbound : Q ≤ L := by
    have hfirst : (128 * H0 ^ 2) / (c * (q : ℝ) ^ (-η)) ≤
        (128 / c * Alog ^ 2) * L ^ (4 * θ) := by
      rw [hqneg]
      field_simp [hc.ne', hqpos.ne', ne_of_gt (Real.rpow_pos_of_pos hqpos η)]
      nlinarith [hprod]
    have hsecond : H ^ 12 / (A * (q : ℝ) ^ (-2 * η)) ≤
        (1 / A) * L ^ (64 * θ) := by
      rw [hq2neg]
      field_simp [hA.ne', hqpos.ne', ne_of_gt (Real.rpow_pos_of_pos hqpos (2 * η))]
      nlinarith [hprod64]
    have hpowmono : L ^ (4 * θ) ≤ L ^ (64 * θ) :=
      Real.rpow_le_rpow_of_exponent_le hL1 (by nlinarith [hθ])
    have h64 : 64 * θ = (1 / 128 : ℝ) := by dsimp only [θ]; norm_num
    have hsmallone : L ^ (64 * θ) ≤ L ^ (1 / 16 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hL1 (by dsimp only [θ]; norm_num)
    have hcoef0 : 0 ≤ 128 / c * Alog ^ 2 := by positivity
    have hAinv0 : 0 ≤ 1 / A := by positivity
    have hfirst' : (128 / c * Alog ^ 2) * L ^ (4 * θ) ≤
        (128 / c * Alog ^ 2) * L ^ (64 * θ) :=
      mul_le_mul_of_nonneg_left hpowmono hcoef0
    have hsum :
        (128 / c * Alog ^ 2) * L ^ (4 * θ) + (1 / A) * L ^ (64 * θ) ≤
          (128 / c * Alog ^ 2 + 1 / A) * L ^ (64 * θ) := by
      calc
        _ ≤ (128 / c * Alog ^ 2) * L ^ (64 * θ) +
            (1 / A) * L ^ (64 * θ) := add_le_add hfirst' (le_refl _)
        _ = _ := by ring
    calc
      Q ≤ (128 / c * Alog ^ 2) * L ^ (4 * θ) + (1 / A) * L ^ (64 * θ) :=
        add_le_add hfirst hsecond
      _ ≤ (128 / c * Alog ^ 2 + 1 / A) * L ^ (64 * θ) := hsum
      _ ≤ KQ * L ^ (64 * θ) := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hLpos.le _)
        dsimp only [KQ]
        linarith
      _ ≤ L ^ (1 / 16 : ℝ) * L ^ (1 / 16 : ℝ) := by gcongr
      _ = L ^ (1 / 8 : ℝ) := by rw [← Real.rpow_add hLpos]; norm_num
      _ ≤ L := by
        have h18 : L ^ (1 / 8 : ℝ) ≤ L ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
        simpa only [Real.rpow_one] using h18
  have hwidth : L ^ (-1 / 8 : ℝ) ≤
      dirichletLQuadraticConditionalCrossZeroWidth A c η q T := by
    have hden : 0 < H ^ 12 * (q : ℝ) ^ (2 * η) / A := by positivity
    have hdenle : H ^ 12 * (q : ℝ) ^ (2 * η) / A ≤ L ^ (1 / 8 : ℝ) := by
      calc
        _ ≤ (1 / A) * L ^ (64 * θ) := by
          rw [div_eq_mul_inv]
          calc
            H ^ 12 * (q : ℝ) ^ (2 * η) * A⁻¹ =
                (1 / A) * (H ^ 12 * (q : ℝ) ^ (2 * η)) := by ring
            _ ≤ (1 / A) * L ^ (64 * θ) :=
              mul_le_mul_of_nonneg_left hprod64 (by positivity)
        _ ≤ L ^ (1 / 16 : ℝ) * L ^ (64 * θ) := by gcongr
        _ = L ^ (9 / 128 : ℝ) := by
          rw [← Real.rpow_add hLpos]
          dsimp only [θ]
          norm_num
        _ ≤ L ^ (1 / 8 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
    dsimp only [dirichletLQuadraticConditionalCrossZeroWidth]
    rw [hq2neg]
    have hid : A * ((q : ℝ) ^ (2 * η))⁻¹ / H ^ 12 =
        (H ^ 12 * (q : ℝ) ^ (2 * η) / A)⁻¹ := by
      field_simp [hA.ne', hHpos.ne',
        ne_of_gt (Real.rpow_pos_of_pos hqpos (2 * η))]
    rw [hid, show L ^ (-1 / 8 : ℝ) = (L ^ (1 / 8 : ℝ))⁻¹ by
      rw [show (-1 / 8 : ℝ) = -(1 / 8) by ring, Real.rpow_neg hLpos.le]]
    exact (inv_le_inv₀ (by positivity) hden).2 hdenle
  have hHfinal : H ≤ L ^ (1 / 1024 : ℝ) := by
    exact hHbound.trans (Real.rpow_le_rpow_of_exponent_le hL1 (by
      dsimp only [θ]; norm_num))
  exact ⟨hHfinal, hQbound, hwidth⟩

set_option maxRecDepth 4000
/-- At the strengthened loss `P = D + 40`, the quadratic scale bounds pay all
four variable-right contour terms against `N / log(N)^D`, uniformly in the
conductor. -/
theorem eventually_quadraticPointwiseSW_four_payments
    (c A : ℝ) (hc : 0 < c) (hA : 0 < A) (C D : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ q : ℕ, ∀ _inst : NeZero q,
      q ≤ logConductorThreshold N C →
      let P := D + 40
      let η := quadraticPointwiseSWEta C D
      let T := nonquadraticPointwiseSWHeight P N
      let δ := (Real.log (N : ℝ))⁻¹
      let ε := nonquadraticPointwiseSWEpsilon P N
      let H := dirichletLQuadraticConditionalFixedH q
        (dirichletLQuadraticConditionalCentralHeight c η q T) T
      let Q := (128 * dirichletLQuadraticConditionalCentralH q T ^ 2) /
            (c * (q : ℝ) ^ (-η)) + H ^ 12 / (A * (q : ℝ) ^ (-2 * η))
      let a := dirichletLTwistedSmoothedQuadraticConditionalLeft A c η q T
      let R := (N : ℝ) / Real.log (N : ℝ) ^ D
      3 ≤ T ∧ 0 < δ ∧
      δ ≤ dirichletLTwistedSmoothedQuadraticConditionalDelta A c η q T ∧
      0 < ε ∧ ε < 1 ∧ 3 < (N : ℝ) ∧ 2 < (N : ℝ) * ε ∧ 0 ≤ R ∧
      T * Q * (N : ℝ) ^ a / ε ≤ R ∧
      T * Q / ε ≤ R ∧
      Q * (N : ℝ) ^ (1 + δ) / (ε * (1 + T ^ 2)) ≤ R ∧
      (N : ℝ) ^ (1 + δ) * (1 + δ⁻¹ ^ 2) / (ε * T) ≤ R ∧
      ε * (N : ℝ) * Real.log (N : ℝ) ≤ R := by
  let P := D + 40
  let B := nonquadraticPointwiseSWHeightExponent P
  let E : ℕ := B + P + D + 4
  have hscale := eventually_quadraticPointwiseSW_scale_bounds c A hc hA C D
  have hdecay := eventually_log_rpow_mul_exp_le_one (E : ℝ) 1 (7 / 8 : ℝ)
    (by dsimp only [E, B, P, nonquadraticPointwiseSWHeightExponent]; positivity)
    (by norm_num) (by norm_num)
  have hdecayN := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually hdecay
  have hlogtop : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsqrtReal :=
    (Real.isLittleO_pow_log_id_atTop (n := 2 * (P + 4))).eventuallyLE
  have hsqrtNat := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually hsqrtReal
  have hsqrtEReal :=
    (Real.isLittleO_pow_log_id_atTop (n := 2 * E)).eventuallyLE
  have hsqrtENat := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually hsqrtEReal
  have hsqrtE : ∀ᶠ N : ℕ in atTop, Real.log (N : ℝ) ^ E ≤ Real.sqrt N := by
    filter_upwards [hsqrtENat, eventually_ge_atTop (2 : ℕ)] with N hlog hN2
    have hN0 : (0 : ℝ) ≤ N := by positivity
    have hlog0 : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by
      exact_mod_cast (show 1 ≤ N by omega))
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hlog0 _),
      Real.norm_eq_abs, id_eq, abs_of_nonneg hN0] at hlog
    rw [show 2 * E = E * 2 by omega, pow_mul] at hlog
    nlinarith [Real.sq_sqrt hN0, Real.sqrt_nonneg (N : ℝ)]
  have hsqrt : ∀ᶠ N : ℕ in atTop,
      Real.log (N : ℝ) ^ (P + 4) ≤ Real.sqrt N := by
    filter_upwards [hsqrtNat, eventually_ge_atTop (2 : ℕ)] with N hlog hN2
    have hN0 : (0 : ℝ) ≤ N := by positivity
    have hlog0 : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by
      exact_mod_cast (show 1 ≤ N by omega))
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hlog0 _),
      Real.norm_eq_abs, id_eq, abs_of_nonneg hN0] at hlog
    rw [show 2 * (P + 4) = (P + 4) * 2 by omega, pow_mul] at hlog
    nlinarith [Real.sq_sqrt hN0, Real.sqrt_nonneg (N : ℝ)]
  filter_upwards [hscale, hdecayN, hsqrt, hsqrtE,
      hlogtop.eventually (eventually_ge_atTop (Real.exp 2)),
      eventually_const_le_log_rpow 4 (7 / 8 : ℝ) (by norm_num),
      eventually_ge_atTop (4 : ℕ)] with N hscale hdecay hsqrt hsqrtE hLlarge hwidthgrow hN
  intro q _inst hq
  let L := Real.log (N : ℝ)
  let η := quadraticPointwiseSWEta C D
  let T := nonquadraticPointwiseSWHeight P N
  let δ := L⁻¹
  let ε := nonquadraticPointwiseSWEpsilon P N
  let H := dirichletLQuadraticConditionalFixedH q
    (dirichletLQuadraticConditionalCentralHeight c η q T) T
  let Q := (128 * dirichletLQuadraticConditionalCentralH q T ^ 2) /
      (c * (q : ℝ) ^ (-η)) + H ^ 12 / (A * (q : ℝ) ^ (-2 * η))
  let a := dirichletLTwistedSmoothedQuadraticConditionalLeft A c η q T
  let R := (N : ℝ) / L ^ D
  obtain ⟨hH, hQ, hwidth⟩ := hscale q _inst hq
  have hLpos : 0 < L := lt_of_lt_of_le (Real.exp_pos 2) hLlarge
  have hL1 : 1 ≤ L := by
    have : (1 : ℝ) ≤ Real.exp 2 := by
      rw [← Real.exp_zero]
      exact (Real.exp_lt_exp.mpr (by norm_num)).le
    exact this.trans hLlarge
  have hL3 : 3 ≤ L := by
    have he : (3 : ℝ) ≤ Real.exp 2 := by
      rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
      nlinarith [Real.exp_one_gt_d9, Real.exp_pos 1]
    exact he.trans hLlarge
  have hL2 : 2 ≤ L := (by linarith : (2 : ℝ) ≤ 3).trans hL3
  have hT : T = L ^ B := rfl
  have hδ : δ = L⁻¹ := rfl
  have hε : ε = (L ^ (P + 3))⁻¹ := rfl
  have hR0 : 0 ≤ R := div_nonneg (by positivity) (pow_nonneg hLpos.le _)
  have hwidthδ : δ ≤ dirichletLTwistedSmoothedQuadraticConditionalDelta A c η q T := by
    dsimp only [dirichletLTwistedSmoothedQuadraticConditionalDelta]
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 4)).2
    have hprod : L * L ^ (-1 / 8 : ℝ) = L ^ (7 / 8 : ℝ) := by
      calc
        L * L ^ (-1 / 8 : ℝ) = L ^ (1 : ℝ) * L ^ (-1 / 8 : ℝ) := by rw [Real.rpow_one]
        _ = L ^ ((1 : ℝ) + (-1 / 8 : ℝ)) := (Real.rpow_add hLpos _ _).symm
        _ = L ^ (7 / 8 : ℝ) := by norm_num
    have hfour : L⁻¹ * 4 ≤ L ^ (-1 / 8 : ℝ) := by
      rw [inv_mul_eq_div, div_le_iff₀ hLpos]
      calc
        (4 : ℝ) ≤ L ^ (7 / 8 : ℝ) := by simpa only [L] using hwidthgrow
        _ = L * L ^ (-1 / 8 : ℝ) := hprod.symm
        _ = L ^ (-1 / 8 : ℝ) * L := mul_comm _ _
    rw [hδ]
    exact hfour.trans hwidth
  have ha : a ≤ 1 - L ^ (-1 / 8 : ℝ) := by
    dsimp only [a, dirichletLTwistedSmoothedQuadraticConditionalLeft]
    linarith
  have hNpos : (0 : ℝ) < N := by positivity
  have hNa : (N : ℝ) ^ a ≤ (N : ℝ) * Real.exp (-(L ^ (7 / 8 : ℝ))) := by
    calc
      (N : ℝ) ^ a ≤ (N : ℝ) ^ (1 - L ^ (-1 / 8 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by
          exact_mod_cast (show 1 ≤ N by omega)) ha
      _ = (N : ℝ) * Real.exp (-(L ^ (7 / 8 : ℝ))) := by
        rw [Real.rpow_def_of_pos hNpos]
        change Real.exp (L * (1 - L ^ (-1 / 8 : ℝ))) = _
        rw [← Real.exp_log hNpos, show Real.log (N : ℝ) = L by rfl, ← Real.exp_add]
        congr 1
        have hprod : L * L ^ (-1 / 8 : ℝ) = L ^ (7 / 8 : ℝ) := by
          calc
            L * L ^ (-1 / 8 : ℝ) = L ^ (1 : ℝ) * L ^ (-1 / 8 : ℝ) := by
              rw [Real.rpow_one]
            _ = L ^ ((1 : ℝ) + (-1 / 8 : ℝ)) := (Real.rpow_add hLpos _ _).symm
            _ = L ^ (7 / 8 : ℝ) := by norm_num
        calc
          L * (1 - L ^ (-1 / 8 : ℝ)) = L - L * L ^ (-1 / 8 : ℝ) := by ring
          _ = L + -L ^ (7 / 8 : ℝ) := by rw [hprod]; ring
  have hleft : T * Q * (N : ℝ) ^ a / ε ≤ R := by
    rw [hT, hε, div_inv_eq_mul]
    calc
      L ^ B * Q * (N : ℝ) ^ a * L ^ (P + 3) ≤
          L ^ B * L * ((N : ℝ) * Real.exp (-(L ^ (7 / 8 : ℝ)))) * L ^ (P + 3) := by
            gcongr
      _ ≤ (N : ℝ) / L ^ D := by
        have hd : L ^ E * Real.exp (-(L ^ (7 / 8 : ℝ))) ≤ 1 := by
          simpa only [L, Real.rpow_natCast, one_mul, neg_mul] using hdecay
        apply (le_div_iff₀ (pow_pos hLpos D)).2
        calc
          L ^ B * L * ((N : ℝ) * Real.exp (-(L ^ (7 / 8 : ℝ)))) *
                L ^ (P + 3) * L ^ D =
              (N : ℝ) * (L ^ E * Real.exp (-(L ^ (7 / 8 : ℝ)))) := by
                dsimp only [E]
                ring
          _ ≤ (N : ℝ) * 1 := mul_le_mul_of_nonneg_left hd (by positivity)
          _ = (N : ℝ) := by ring
  have hbase : T * Q / ε ≤ R := by
    rw [hT, hε, div_inv_eq_mul]
    calc
      L ^ B * Q * L ^ (P + 3) ≤ L ^ B * L * L ^ (P + 3) := by gcongr
      _ ≤ (N : ℝ) / L ^ D := by
        apply (le_div_iff₀ (pow_pos hLpos D)).2
        calc
          L ^ B * L * L ^ (P + 3) * L ^ D = L ^ E := by
            dsimp only [E]
            ring
          _ ≤ Real.sqrt (N : ℝ) := hsqrtE
          _ ≤ (N : ℝ) := by
            have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
            nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ N by positivity),
              Real.sqrt_nonneg (N : ℝ)]
  have hNpow : (N : ℝ) ^ (1 + δ) = Real.exp 1 * N := by
    simpa only [hδ] using rpow_one_add_inv_log_nat N (by omega)
  have hhoriz : Q * (N : ℝ) ^ (1 + δ) / (ε * (1 + T ^ 2)) ≤ R := by
    rw [hNpow, hε, hT]
    have hden : 0 < (L ^ (P + 3))⁻¹ * (1 + (L ^ B) ^ 2) := by positivity
    rw [div_le_iff₀ hden]
    calc
      Q * (Real.exp 1 * N) ≤ L * (4 * N) := by
        gcongr
        exact Real.exp_one_lt_d9.le.trans (by norm_num)
      _ ≤ R * ((L ^ (P + 3))⁻¹ * (1 + (L ^ B) ^ 2)) := by
        dsimp only [R]
        field_simp
        dsimp only [B, P, nonquadraticPointwiseSWHeightExponent]
        ring_nf
        have h4L : (4 : ℝ) ≤ L ^ 2 := by nlinarith
        calc
          L ^ 44 * L ^ (D * 2) * 4 ≤ L ^ 44 * L ^ (D * 2) * L ^ 2 := by gcongr
          _ = L ^ 46 * L ^ (D * 2) := by ring
          _ ≤ L ^ 180 * L ^ (D * 4) := by
            exact mul_le_mul
              (pow_le_pow_right₀ hL1 (show 46 ≤ 180 by omega))
              (pow_le_pow_right₀ hL1 (show D * 2 ≤ D * 4 by omega))
              (pow_nonneg hLpos.le _) (pow_nonneg hLpos.le _)
          _ ≤ L ^ 220 * L ^ (D * 4) :=
            mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hL1 (by omega))
              (pow_nonneg hLpos.le _)
          _ ≤ 1 + L ^ 220 * L ^ (D * 4) := by linarith
  have htail : (N : ℝ) ^ (1 + δ) * (1 + δ⁻¹ ^ 2) / (ε * T) ≤ R := by
    rw [hNpow, hδ, hε, hT, inv_inv]
    have hden : 0 < (L ^ (P + 3))⁻¹ * L ^ B := by positivity
    rw [div_le_iff₀ hden]
    calc
      Real.exp 1 * N * (1 + L ^ 2) ≤ 8 * N * L ^ 2 := by
        have he : Real.exp 1 ≤ 4 := Real.exp_one_lt_d9.le.trans (by norm_num)
        have htwo : 1 + L ^ 2 ≤ 2 * L ^ 2 := by nlinarith
        calc
          _ ≤ 4 * N * (1 + L ^ 2) := by gcongr
          _ ≤ 4 * N * (2 * L ^ 2) := by gcongr
          _ = 8 * N * L ^ 2 := by ring
      _ ≤ R * ((L ^ (P + 3))⁻¹ * L ^ B) := by
        dsimp only [R]
        field_simp
        dsimp only [B, P, nonquadraticPointwiseSWHeightExponent]
        ring_nf
        have h8L3 : (8 : ℝ) ≤ L ^ 3 := by
          calc
            (8 : ℝ) = 2 ^ 3 := by norm_num
            _ ≤ L ^ 3 := pow_le_pow_left₀ (by norm_num) hL2 3
        calc
          L ^ 45 * L ^ (D * 2) * 8 ≤ L ^ 45 * L ^ (D * 2) * L ^ 3 := by gcongr
          _ = L ^ 48 * L ^ (D * 2) := by ring
          _ ≤ L ^ 110 * L ^ (D * 2) :=
            mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hL1 (by omega))
              (pow_nonneg hLpos.le _)
  have hsmooth : ε * (N : ℝ) * L ≤ R := by
    rw [hε]
    dsimp only [R]
    field_simp
    rw [mul_comm L, ← pow_succ]
    exact pow_le_pow_right₀ hL1 (by omega)
  have hT3 : 3 ≤ T := by
    rw [hT]
    exact hL3.trans
      (by simpa only [pow_one] using pow_le_pow_right₀ hL1 (show 1 ≤ B by
        dsimp only [B, P, nonquadraticPointwiseSWHeightExponent]; omega))
  have hδpos : 0 < δ := by rw [hδ]; positivity
  have hεpos : 0 < ε := by rw [hε]; positivity
  have hε1 : ε < 1 := by
    rw [hε]
    exact (inv_lt_one₀ (pow_pos hLpos _)).2 (one_lt_pow₀ (by linarith) (by omega))
  have hNε : 2 < (N : ℝ) * ε := by
    rw [hε, ← div_eq_mul_inv]
    apply (lt_div_iff₀ (pow_pos hLpos _)).2
    calc
      2 * L ^ (P + 3) ≤ L * L ^ (P + 3) := by gcongr
      _ = L ^ (P + 4) := by rw [← pow_succ']
      _ ≤ Real.sqrt (N : ℝ) := hsqrt
      _ < (N : ℝ) := Real.sqrt_lt_self_iff.mpr (by exact_mod_cast (show 1 < N by omega))
  exact ⟨hT3, hδpos, hwidthδ, hεpos, hε1,
    by exact_mod_cast (show 3 < N by omega), hNε, hR0, hleft, hbase, hhoriz, htail, hsmooth⟩

/-- Uniform-in-`y` quadratic pointwise Siegel--Walfisz bound from the selected
Landau--Siegel lower bound. -/
theorem exists_quadraticPointwiseSiegelWalfisz_uniform
    (c : ℝ) (hc : 0 < c)
    {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν)
    (νpos : ∀ x > 0, 0 ≤ ν x)
    (suppν : support ν ⊆ Icc (1 / 2) 2)
    (mass_one : ∫ x in Ioi (0 : ℝ), ν x / x = 1)
    (C D : ℕ)
    (hSiegel : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsPrimitive → χ ^ 2 = 1 → χ ≠ 1 →
      c * (q : ℝ) ^ (-quadraticPointwiseSWEta C D) ≤ (χ.LFunction 1).re) :
    ∃ K > 0, ∀ᶠ N : ℕ in atTop, ∀ q : ℕ, ∀ _inst : NeZero q,
      q ≤ logConductorThreshold N C → ∀ χ : DirichletCharacter ℂ q,
        χ.IsPrimitive → χ ^ 2 = 1 → χ ≠ 1 → ∀ y : ℕ, y ≤ N →
          ‖lambdaCharacterPrefix y q χ‖ ≤
            K * (N : ℝ) / Real.log (N : ℝ) ^ D := by
  let η := quadraticPointwiseSWEta C D
  have hη : 0 < η := quadraticPointwiseSWEta_pos C D
  obtain ⟨A, hA, K₀, hK₀, hexact⟩ :=
    exists_quadraticPointwiseExactPrefix_of_four_payments
      c η hc hη diffν νpos suppν mass_one
  let c₀ : ℝ := Real.log 4 + 4
  let K : ℝ := K₀ + 2 * c₀
  refine ⟨K, by dsimp only [K, c₀]; positivity, ?_⟩
  have hpay := eventually_quadraticPointwiseSW_four_payments c A hc hA C D
  have hsqrtReal :=
    (Real.isLittleO_pow_log_id_atTop (n := 2 * D)).eventuallyLE
  have hsqrtNat := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually hsqrtReal
  have hsqrt : ∀ᶠ N : ℕ in atTop,
      Real.log (N : ℝ) ^ D ≤ Real.sqrt N := by
    filter_upwards [hsqrtNat, eventually_ge_atTop (2 : ℕ)] with N hlog hN2
    have hN0 : (0 : ℝ) ≤ N := by positivity
    have hlog0 : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by
      exact_mod_cast (show 1 ≤ N by omega))
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hlog0 _),
      Real.norm_eq_abs, id_eq, abs_of_nonneg hN0] at hlog
    rw [show 2 * D = D * 2 by omega, pow_mul] at hlog
    nlinarith [Real.sq_sqrt hN0, Real.sqrt_nonneg (N : ℝ)]
  let P := D + 40
  have hsqrtStrongReal :=
    (Real.isLittleO_pow_log_id_atTop (n := 2 * (P + 4))).eventuallyLE
  have hsqrtStrongNat :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually hsqrtStrongReal
  have hsqrtStrong : ∀ᶠ N : ℕ in atTop,
      Real.log (N : ℝ) ^ (P + 4) ≤ Real.sqrt N := by
    filter_upwards [hsqrtStrongNat, eventually_ge_atTop (2 : ℕ)] with N hlog hN2
    have hN0 : (0 : ℝ) ≤ N := by positivity
    have hlog0 : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by
      exact_mod_cast (show 1 ≤ N by omega))
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hlog0 _),
      Real.norm_eq_abs, id_eq, abs_of_nonneg hN0] at hlog
    rw [show 2 * (P + 4) = (P + 4) * 2 by omega, pow_mul] at hlog
    nlinarith [Real.sq_sqrt hN0, Real.sqrt_nonneg (N : ℝ)]
  have hlogtop : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlog4ev := hlogtop.eventually (eventually_ge_atTop (4 : ℝ))
  filter_upwards [hpay, hsqrt, hsqrtStrong, hlog4ev,
      eventually_ge_atTop (4 : ℕ)] with N hpay hsqrt hsqrtStrong hlog4 hN
  intro q _inst hq χ hprimitive hquad hχ y hy
  let T := nonquadraticPointwiseSWHeight P N
  let δ := (Real.log (N : ℝ))⁻¹
  let ε := nonquadraticPointwiseSWEpsilon P N
  let H := dirichletLQuadraticConditionalFixedH q
    (dirichletLQuadraticConditionalCentralHeight c η q T) T
  let Q := (128 * dirichletLQuadraticConditionalCentralH q T ^ 2) /
      (c * (q : ℝ) ^ (-η)) + H ^ 12 / (A * (q : ℝ) ^ (-2 * η))
  let a := dirichletLTwistedSmoothedQuadraticConditionalLeft A c η q T
  let R := (N : ℝ) / Real.log (N : ℝ) ^ D
  obtain ⟨hT, hδ, hδwidth, hε, hε1, hN3, hNε, hR,
    hleft, hbase, hhoriz, htail, hsmooth⟩ := hpay q _inst hq
  have hlogpos : 0 < Real.log (N : ℝ) := Real.log_pos (by
    exact_mod_cast (show 1 < N by omega))
  have hRpos : 0 < R := div_pos (by positivity) (pow_pos hlogpos _)
  by_cases hsmall : (y : ℝ) ≤ 2 * Real.sqrt N
  · have helem := norm_lambdaCharacterPrefix_le_const_mul_self y q χ
    have hsqrtN : Real.sqrt (N : ℝ) * Real.sqrt N = N := by
      rw [← pow_two, Real.sq_sqrt (by positivity)]
    have hsmallR : 2 * c₀ * Real.sqrt N ≤ 2 * c₀ * R := by
      have hc₀ : 0 ≤ c₀ := by dsimp only [c₀]; positivity
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by norm_num) hc₀)
      rw [show R = (N : ℝ) / Real.log (N : ℝ) ^ D by rfl,
        le_div_iff₀ (pow_pos hlogpos _)]
      calc
        Real.sqrt N * Real.log (N : ℝ) ^ D ≤ Real.sqrt N * Real.sqrt N := by gcongr
        _ = N := hsqrtN
    calc
      ‖lambdaCharacterPrefix y q χ‖ ≤ c₀ * y := helem
      _ ≤ c₀ * (2 * Real.sqrt N) := by gcongr
      _ = 2 * c₀ * Real.sqrt N := by ring
      _ ≤ 2 * c₀ * R := hsmallR
      _ ≤ K * R := by dsimp only [K]; nlinarith
      _ = K * (N : ℝ) / Real.log (N : ℝ) ^ D := by
        rw [show R = (N : ℝ) / Real.log (N : ℝ) ^ D by rfl, mul_div_assoc]
  · have hlarge : 2 * Real.sqrt N < (y : ℝ) := lt_of_not_ge hsmall
    have hypos : (0 : ℝ) < y := lt_trans (by positivity : (0 : ℝ) < 2 * Real.sqrt N) hlarge
    have hy3 : (3 : ℝ) < y := by
      have hsqrt2 : (2 : ℝ) ≤ Real.sqrt N := by
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ N by positivity),
          Real.sqrt_nonneg (N : ℝ), (show (4 : ℝ) ≤ N by exact_mod_cast hN)]
      nlinarith
    have hyN : (y : ℝ) ≤ N := by exact_mod_cast hy
    have hrpowRight : (y : ℝ) ^ (1 + δ) ≤ (N : ℝ) ^ (1 + δ) := by
      apply Real.rpow_le_rpow (by positivity) hyN
      linarith
    have hleftY : T * Q * (y : ℝ) ^ a / ε ≤ R := by
      by_cases ha0 : 0 ≤ a
      · apply le_trans _ hleft
        have hrpowLeft : (y : ℝ) ^ a ≤ (N : ℝ) ^ a :=
          Real.rpow_le_rpow (by positivity) hyN ha0
        gcongr
      · apply le_trans _ hbase
        have hy1 : (1 : ℝ) ≤ y := by linarith
        have hya : (y : ℝ) ^ a ≤ 1 :=
          Real.rpow_le_one_of_one_le_of_nonpos hy1 (le_of_not_ge ha0)
        have hQ0 : 0 ≤ Q := by dsimp only [Q, H]; positivity
        apply (div_le_div_iff_of_pos_right hε).2
        calc
          T * Q * (y : ℝ) ^ a ≤ T * Q * 1 :=
            mul_le_mul_of_nonneg_left hya
              (mul_nonneg (by dsimp only [T, P, nonquadraticPointwiseSWHeight]; positivity) hQ0)
          _ = T * Q := by ring
    have hhorizY : Q * (y : ℝ) ^ (1 + δ) / (ε * (1 + T ^ 2)) ≤ R := by
      apply le_trans _ hhoriz
      gcongr
    have htailY : (y : ℝ) ^ (1 + δ) * (1 + δ⁻¹ ^ 2) / (ε * T) ≤ R := by
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
    have hbound := hexact χ (T := T) (δ := δ) (ε := ε) (X := (y : ℝ)) (R := R)
      hquad hχ hT (by simpa only [η] using hSiegel q χ hprimitive hquad hχ)
      hδ hδwidth hε hε1 hy3 hyε hR hleftY hhorizY htailY hsmoothY
    have hfloor : ⌊(y : ℝ)⌋₊ = y := Nat.floor_natCast y
    rw [hfloor] at hbound
    calc
      ‖lambdaCharacterPrefix y q χ‖ ≤ K₀ * R := hbound
      _ ≤ K * R := by
        apply mul_le_mul_of_nonneg_right _ hR
        dsimp only [K, c₀]
        nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 4)]
      _ = K * (N : ℝ) / Real.log (N : ℝ) ^ D := by
        rw [show R = (N : ℝ) / Real.log (N : ℝ) ^ D by rfl, mul_div_assoc]

/-- The raw Landau--Siegel hypothesis alone now supplies the quadratic
uniform-in-prefix pointwise bound. -/
theorem exists_quadraticPointwiseSiegelWalfisz_uniform_of_rawLandauSiegelLowerBound
    (hLandauSiegel : RawLandauSiegelLowerBound)
    {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν)
    (νpos : ∀ x > 0, 0 ≤ ν x)
    (suppν : support ν ⊆ Icc (1 / 2) 2)
    (mass_one : ∫ x in Ioi (0 : ℝ), ν x / x = 1)
    (C D : ℕ) :
    ∃ K > 0, ∀ᶠ N : ℕ in atTop, ∀ q : ℕ, ∀ _inst : NeZero q,
      q ≤ logConductorThreshold N C → ∀ χ : DirichletCharacter ℂ q,
        χ.IsPrimitive → χ ^ 2 = 1 → χ ≠ 1 → ∀ y : ℕ, y ≤ N →
          ‖lambdaCharacterPrefix y q χ‖ ≤
            K * (N : ℝ) / Real.log (N : ℝ) ^ D := by
  let η := quadraticPointwiseSWEta C D
  have hη : 0 < η := quadraticPointwiseSWEta_pos C D
  obtain ⟨c, hc, hSiegel⟩ := hLandauSiegel η hη
  exact exists_quadraticPointwiseSiegelWalfisz_uniform c hc diffν νpos suppν mass_one C D
    (by intro q _ χ hp hquad hχ; simpa only [η] using hSiegel q χ hp hquad hχ)

end

end AnalyticNumberTheory.LargeSieve
