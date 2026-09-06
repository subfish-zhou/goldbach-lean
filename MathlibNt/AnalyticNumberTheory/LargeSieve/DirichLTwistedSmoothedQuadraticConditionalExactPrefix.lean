import MathlibNt.AnalyticNumberTheory.LargeSieve.DirichLTwistedSmoothedQuadraticConditionalContourNorm
import MathlibNt.AnalyticNumberTheory.LargeSieve.DirichLTwistedNonquadraticPointwiseSiegelWalfisz

open Set Function Filter Complex Real MeasureTheory

namespace AnalyticNumberTheory.LargeSieve

private theorem quadratic_integral_lower_middle_upper
    (f : ℝ → ℂ) {T : ℝ} (hf : Integrable f) (hT : 0 ≤ T) :
    (∫ t in Iic (-T), f t) + (∫ t in Ioc (-T) T, f t) +
        (∫ t in Ici T, f t) = ∫ t, f t := by
  exact AnalyticNumberTheory.LargeSieve.integral_lower_middle_upper f hf hT

/-- Raw quadratic Siegel data select a single contour scale and give the full
smoothed Perron error.  The three displayed terms pay respectively the left
edge, both horizontal edges, and both right-line tails. -/
theorem exists_dirichletLTwistedSmoothedQuadraticConditionalErrorAssembly
    (c η : ℝ) (hc : 0 < c) (hη : 0 < η)
    {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν)
    (νpos : ∀ x > 0, 0 ≤ ν x)
    (suppν : support ν ⊆ Icc (1 / 2) 2)
    (mass_one : ∫ x in Ioi (0 : ℝ), ν x / x = 1) :
    ∃ A > 0, ∃ K > 0, ∀ {q : ℕ} [NeZero q]
      (χ : DirichletCharacter ℂ q) {T ε X : ℝ},
      χ ^ 2 = 1 → χ ≠ 1 → 3 ≤ T →
      c * (q : ℝ) ^ (-η) ≤ (χ.LFunction 1).re →
      0 < ε → ε < 1 → 1 ≤ X →
      let Q := (128 * dirichletLQuadraticConditionalCentralH q T ^ 2) /
            (c * (q : ℝ) ^ (-η)) +
          dirichletLQuadraticConditionalFixedH q
              (dirichletLQuadraticConditionalCentralHeight c η q T) T ^ 12 /
            (A * (q : ℝ) ^ (-2 * η))
      let a := dirichletLTwistedSmoothedQuadraticConditionalLeft A c η q T
      let d := dirichletLTwistedSmoothedQuadraticConditionalDelta A c η q T
      let b := dirichletLTwistedSmoothedQuadraticConditionalRight A c η q T
      ‖DirichletCharacter.twistedSmoothedPsi χ ν ε X‖ ≤
        K * (T * Q * X ^ a / ε +
          Q * X ^ b / (ε * (1 + T ^ 2)) +
          X ^ b * (1 + d⁻¹ ^ 2) / (ε * T)) := by
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
    exists_dirichletLTwistedSmoothedQuadraticConditionalContourNormBounds diffν suppν
  obtain ⟨Ctail, hCtail, htails⟩ :=
    DirichletCharacter.twistedSmoothedPerron_right_tails_quantitative
      diffν νpos suppν mass_one
  refine ⟨A, hA, 2 * (C + Ctail), by positivity, ?_⟩
  intro q _ χ T ε X hquad hχ hT hSiegel hε hε1 hX
  dsimp only
  let Q := (128 * dirichletLQuadraticConditionalCentralH q T ^ 2) /
        (c * (q : ℝ) ^ (-η)) +
      dirichletLQuadraticConditionalFixedH q
          (dirichletLQuadraticConditionalCentralHeight c η q T) T ^ 12 /
        (A * (q : ℝ) ^ (-2 * η))
  let a := dirichletLTwistedSmoothedQuadraticConditionalLeft A c η q T
  let d := dirichletLTwistedSmoothedQuadraticConditionalDelta A c η q T
  let b := dirichletLTwistedSmoothedQuadraticConditionalRight A c η q T
  let F := DirichletCharacter.twistedSmoothedPerronIntegrand χ ν ε X
  let Eleft := T * Q * X ^ a / ε
  let Ehoriz := Q * X ^ b / (ε * (1 + T ^ 2))
  let Etail := X ^ b * (1 + d⁻¹ ^ 2) / (ε * T)
  have hT0 : 0 < T := by linarith
  have hT1 : 1 ≤ T := by linarith
  have hX0 : 0 < X := lt_of_lt_of_le zero_lt_one hX
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hq1 : (1 : ℝ) ≤ q := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hp1 : (q : ℝ) ^ (-2 * η) ≤ 1 := by
    simpa using Real.rpow_le_rpow_of_exponent_le hq1 (by linarith : -2 * η ≤ 0)
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
    dsimp only [dirichletLQuadraticConditionalCrossZeroWidth]
    calc
      A * (q : ℝ) ^ (-2 * η) /
          dirichletLQuadraticConditionalFixedH q
              (dirichletLQuadraticConditionalCentralHeight c η q T) T ^ 12 ≤ A := by
        rw [div_le_iff₀ (pow_pos hH 12)]
        nlinarith [one_le_pow₀ hH1 (n := 12), mul_le_of_le_one_right hA.le hp1]
      _ ≤ 1 / 2 := hAhalf
  have hd : 0 < d := by
    dsimp only [d, dirichletLTwistedSmoothedQuadraticConditionalDelta]
    positivity
  have hd1 : d ≤ 1 := by
    dsimp only [d, dirichletLTwistedSmoothedQuadraticConditionalDelta]
    linarith
  have hwidthle : dirichletLQuadraticConditionalCrossZeroWidth A c η q T ≤
      dirichletLQuadraticConditionalCrossZeroWidth A₀ c η q T := by
    dsimp only [dirichletLQuadraticConditionalCrossZeroWidth]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hAA₀ (Real.rpow_nonneg hq.le _))
      (pow_nonneg hH.le 12)
  have hf : Integrable (fun t : ℝ => F ((b : ℂ) + t * I)) := by
    simpa only [F, b, d, dirichletLTwistedSmoothedQuadraticConditionalRight,
      dirichletLTwistedSmoothedQuadraticConditionalDelta] using
      (DirichletCharacter.twistedSmoothedPerronIntegrand_integrable_right
        (q := q) (σ := 1 + d) (X := X) (ε := ε) χ diffν νpos suppν mass_one
        hX0 hε hε1 (by linarith) (by linarith))
  have hp := DirichletCharacter.twistedSmoothedPerron χ diffν νpos suppν mass_one
    hX0 hε hε1 (σ := 1 + d) (by linarith) (by linarith)
  have ht := htails χ hd hd1 hε hε1 hX0 hT1
  have hct := hcontour Z hZ hzeta χ hquad hχ hA hAc hAhalf hAsmall hc hη hT
    hSiegel hε hε1 hX
  have hshift := dirichletLTwistedSmoothedPerron_quadraticConditionalFiniteContourIdentity
    χ hAA₀ hA hc hη hT0 hχ hw hw2 hwidthle
      (hzero q χ T hquad hχ hT0 hSiegel) diffν νpos suppν mass_one hX0 hε hε1
  have hsplit := quadratic_integral_lower_middle_upper
    (fun t : ℝ => F ((b : ℂ) + t * I)) hf hT0.le
  have hbdef : b = 1 + d := by rfl
  have htlow : ‖∫ t in Iic (-T), F ((b : ℂ) + t * I)‖ ≤ Ctail * Etail := by
    dsimp only [F, Etail]
    rw [hbdef]
    convert ht.1 using 1 <;> ring
  have htupper : ‖∫ t in Ici T, F ((b : ℂ) + t * I)‖ ≤ Ctail * Etail := by
    dsimp only [F, Etail]
    rw [hbdef]
    convert ht.2 using 1 <;> ring
  have hmid : ‖∫ t in Ioc (-T) T, F ((b : ℂ) + t * I)‖ =
      ‖VIntegral F b (-T) T‖ := by
    rw [VIntegral, norm_smul, norm_I, one_mul,
      intervalIntegral.integral_of_le (by linarith : -T ≤ T)]
  have hv : ‖VIntegral F b (-T) T‖ ≤ C * Eleft + C * Ehoriz + C * Ehoriz := by
    have heq : VIntegral F b (-T) T =
        VIntegral F a (-T) T + HIntegral F a b T - HIntegral F a b (-T) := by
      simpa only [F, a, b] using (by linear_combination hshift)
    have hleft : ‖VIntegral F a (-T) T‖ ≤ C * Eleft := by
      dsimp only [F, a, Eleft, Q]
      convert hct.1 using 1 <;> (try ring)
    have htop : ‖HIntegral F a b T‖ ≤ C * Ehoriz := by
      dsimp only [F, a, b, Ehoriz, Q]
      convert hct.2.1 using 1 <;> (try ring)
    have hbottom : ‖HIntegral F a b (-T)‖ ≤ C * Ehoriz := by
      dsimp only [F, a, b, Ehoriz, Q]
      convert hct.2.2 using 1 <;> (try ring)
    rw [heq]
    calc
      _ ≤ ‖VIntegral F a (-T) T‖ + ‖HIntegral F a b T‖ +
          ‖HIntegral F a b (-T)‖ :=
        (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) (le_refl _))
      _ ≤ C * Eleft + C * Ehoriz + C * Ehoriz :=
        add_le_add (add_le_add hleft htop) hbottom
  have hfull : ‖∫ t : ℝ, F ((b : ℂ) + t * I)‖ ≤
      Ctail * Etail + (C * Eleft + C * Ehoriz + C * Ehoriz) + Ctail * Etail := by
    rw [← hsplit]
    calc
      _ ≤ ‖∫ t in Iic (-T), F ((b : ℂ) + t * I)‖ +
          ‖∫ t in Ioc (-T) T, F ((b : ℂ) + t * I)‖ +
          ‖∫ t in Ici T, F ((b : ℂ) + t * I)‖ :=
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
  have hnormalized : ‖VerticalIntegral' F b‖ ≤
      ‖∫ t : ℝ, F ((b : ℂ) + t * I)‖ := by
    rw [VerticalIntegral', VerticalIntegral, norm_smul, norm_smul, norm_I, one_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) hnorm
  have hEleft : 0 ≤ Eleft := by dsimp only [Eleft, Q]; positivity
  have hEhoriz : 0 ≤ Ehoriz := by dsimp only [Ehoriz, Q]; positivity
  have hEtail : 0 ≤ Etail := by dsimp only [Etail]; positivity
  rw [hp]
  change ‖VerticalIntegral' F b‖ ≤ _
  calc
    _ ≤ ‖∫ t : ℝ, F ((b : ℂ) + t * I)‖ := hnormalized
    _ ≤ Ctail * Etail + (C * Eleft + C * Ehoriz + C * Ehoriz) +
        Ctail * Etail := hfull
    _ ≤ 2 * (C + Ctail) * (Eleft + Ehoriz + Etail) := by
      nlinarith [mul_nonneg hC.le hEleft, mul_nonneg hC.le hEhoriz,
        mul_nonneg hCtail.le hEtail]
    _ = _ := by rfl

/-- The strongest exact-prefix consumer at the contour level: once each of the
three contour terms and the smoothing-removal term is paid by a common `R`,
the genuine prefix through `⌊X⌋₊` is `O(R)`.  No nonquadratic theorem is used. -/
theorem exists_quadraticConditionalExactPrefix_of_four_payments
    (c η : ℝ) (hc : 0 < c) (hη : 0 < η)
    {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν)
    (νpos : ∀ x > 0, 0 ≤ ν x)
    (suppν : support ν ⊆ Icc (1 / 2) 2)
    (mass_one : ∫ x in Ioi (0 : ℝ), ν x / x = 1) :
    ∃ A > 0, ∃ K > 0, ∀ {q : ℕ} [NeZero q]
      (χ : DirichletCharacter ℂ q) {T ε X R : ℝ},
      χ ^ 2 = 1 → χ ≠ 1 → 3 ≤ T →
      c * (q : ℝ) ^ (-η) ≤ (χ.LFunction 1).re →
      0 < ε → ε < 1 → 3 < X → 2 < X * ε → 0 ≤ R →
      let Q := (128 * dirichletLQuadraticConditionalCentralH q T ^ 2) /
            (c * (q : ℝ) ^ (-η)) +
          dirichletLQuadraticConditionalFixedH q
              (dirichletLQuadraticConditionalCentralHeight c η q T) T ^ 12 /
            (A * (q : ℝ) ^ (-2 * η))
      let a := dirichletLTwistedSmoothedQuadraticConditionalLeft A c η q T
      let d := dirichletLTwistedSmoothedQuadraticConditionalDelta A c η q T
      let b := dirichletLTwistedSmoothedQuadraticConditionalRight A c η q T
      T * Q * X ^ a / ε ≤ R →
      Q * X ^ b / (ε * (1 + T ^ 2)) ≤ R →
      X ^ b * (1 + d⁻¹ ^ 2) / (ε * T) ≤ R →
      ε * X * Real.log X ≤ R →
      ‖lambdaCharacterPrefix ⌊X⌋₊ q χ‖ ≤ K * R := by
  obtain ⟨A, hA, K₀, hK₀, herror⟩ :=
    exists_dirichletLTwistedSmoothedQuadraticConditionalErrorAssembly
      c η hc hη diffν νpos suppν mass_one
  obtain ⟨C, hC, hclose⟩ :=
    exists_uniform_twistedSmoothedPsiClose diffν suppν νpos mass_one
  refine ⟨A, hA, 3 * K₀ + C + 1, by positivity, ?_⟩
  intro q _ χ T ε X R hquad hχ hT hSiegel hε hε1 hX hXε hR
  intro Q a d b hleft hhoriz htail hsmooth
  have hs := herror χ hquad hχ hT hSiegel hε hε1 (by linarith : 1 ≤ X)
  have hcclose := hclose χ X hX ε hε hε1 hXε
  have hsmoothed : ‖DirichletCharacter.twistedSmoothedPsi χ ν ε X‖ ≤ 3 * K₀ * R := by
    calc
      _ ≤ K₀ * (T * Q * X ^ a / ε + Q * X ^ b / (ε * (1 + T ^ 2)) +
          X ^ b * (1 + d⁻¹ ^ 2) / (ε * T)) := by simpa only using hs
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

end AnalyticNumberTheory.LargeSieve