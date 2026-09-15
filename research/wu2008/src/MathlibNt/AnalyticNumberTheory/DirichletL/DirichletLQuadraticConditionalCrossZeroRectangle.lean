import MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLQuadraticConditionalPowerRectangle

/-!
# A fixed quadratic rectangle crossing height zero

The high-height quadratic argument contains `1 / |2t|`, so its fixed-height
majorant degenerates as `t → 0`.  Here the low two-segment argument is kept
separate.  A fixed conductor cutoff at height `T`, paid for directly by the raw
lower bound for `L(1, χ)`, supplies a positive central band.  The existing
annular rectangles cover the two remaining bands.  Their common left edge then
gives one rectangle across the whole interval `[-T,T]`.
-/

open Complex Set

namespace AnalyticNumberTheory.LargeSieve

open DirichletLGlobalConductorLogValueBound
open DirichletLGlobalConductorLogDerivativeBound

/-- The nonsingular conductor scale used in the central low-height band. -/
noncomputable def dirichletLQuadraticConditionalCentralH (q : ℕ) (T : ℝ) : ℝ :=
  1 + Real.log (dirichletLNonquadraticConductorLogCutoff q T)

/-- A positive central half-height whose vertical derivative budget is paid by
`c q⁻η`.  The minimum also makes it automatically no larger than `T`. -/
noncomputable def dirichletLQuadraticConditionalCentralHeight
    (c η : ℝ) (q : ℕ) (T : ℝ) : ℝ :=
  min T (c * (q : ℝ) ^ (-η) /
    (256 * (dirichletLQuadraticConditionalCentralH q T) ^ 2))

/-- The final width uses the annular majorant at the positive central cutoff. -/
noncomputable def dirichletLQuadraticConditionalCrossZeroWidth
    (A c η : ℝ) (q : ℕ) (T : ℝ) : ℝ :=
  A * (q : ℝ) ^ (-2 * η) /
    (dirichletLQuadraticConditionalFixedH q
      (dirichletLQuadraticConditionalCentralHeight c η q T) T) ^ 12

/-- One fixed rectangle crossing `t = 0`. -/
def dirichletLQuadraticConditionalCrossZeroRectangle
    (A c η : ℝ) (q : ℕ) (T : ℝ) : Set ℂ :=
  (((1 - dirichletLQuadraticConditionalCrossZeroWidth A c η q T : ℝ) : ℂ) - I * T).Rectangle
    (2 + I * T)

private theorem central_parameters
    {q : ℕ} [NeZero q] {A c η T : ℝ}
    (hA : 0 < A) (hAc : A ≤ c / 256) (hAhalf : A ≤ 1 / 2)
    (hc : 0 < c) (hη : 0 < η) (hT : 0 < T) :
    let H₀ := dirichletLQuadraticConditionalCentralH q T
    let τ := dirichletLQuadraticConditionalCentralHeight c η q T
    let H := dirichletLQuadraticConditionalFixedH q τ T
    let w := dirichletLQuadraticConditionalCrossZeroWidth A c η q T
    1 ≤ H₀ ∧ 0 < τ ∧ τ ≤ T ∧ H₀ ≤ H ∧ 1 ≤ H ∧ 0 < w ∧
      w ≤ c * (q : ℝ) ^ (-η) / (256 * H₀ ^ 2) ∧ w ≤ 1 / H₀ := by
  dsimp only
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hcut : (1 : ℝ) ≤ dirichletLNonquadraticConductorLogCutoff q T := by
    exact_mod_cast (show 1 ≤ dirichletLNonquadraticConductorLogCutoff q T by
      unfold dirichletLNonquadraticConductorLogCutoff
      exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (NeZero.ne q) (by
        unfold dirichletLNonquadraticConductorLogHeightBlock
        omega)))
  have hH₀ : 1 ≤ 1 + Real.log (dirichletLNonquadraticConductorLogCutoff q T) := by
    linarith [Real.log_nonneg hcut]
  have hr : 0 < (q : ℝ) ^ (-η) := Real.rpow_pos_of_pos hq _
  have hp : 0 < (q : ℝ) ^ (-2 * η) := Real.rpow_pos_of_pos hq _
  have hpr : (q : ℝ) ^ (-2 * η) ≤ (q : ℝ) ^ (-η) :=
    Real.rpow_le_rpow_of_exponent_le hq1 (by linarith)
  let τ : ℝ := min T (c * (q : ℝ) ^ (-η) /
    (256 * (1 + Real.log (dirichletLNonquadraticConductorLogCutoff q T)) ^ 2))
  have hτ : 0 < τ := lt_min hT (by positivity)
  have hτT : τ ≤ T := min_le_left _ _
  have hlogarg : 0 ≤ Real.log (2 * T + 2) := Real.log_nonneg (by linarith)
  let H : ℝ := dirichletLQuadraticConditionalFixedH q τ T
  have hH₀H : 1 + Real.log (dirichletLNonquadraticConductorLogCutoff q T) ≤ H := by
    dsimp only [H, dirichletLQuadraticConditionalFixedH]
    have hinv : 0 < 1 / (2 * τ) := by positivity
    linarith
  have hH : 1 ≤ H := hH₀.trans hH₀H
  have hHpos : 0 < H := lt_of_lt_of_le zero_lt_one hH
  let w : ℝ := A * (q : ℝ) ^ (-2 * η) / H ^ 12
  have hw : 0 < w := by dsimp only [w]; positivity
  have hHpow2 :
      (1 + Real.log (dirichletLNonquadraticConductorLogCutoff q T)) ^ 2 ≤ H ^ 12 := by
    calc
      _ ≤ H ^ 2 := pow_le_pow_left₀ (zero_le_one.trans hH₀) hH₀H 2
      _ ≤ H ^ 12 := by exact pow_le_pow_right₀ hH (by omega)
  have hwbudget : w ≤ c * (q : ℝ) ^ (-η) /
      (256 * (1 + Real.log (dirichletLNonquadraticConductorLogCutoff q T)) ^ 2) := by
    rw [div_le_div_iff₀ (pow_pos hHpos 12) (by positivity)]
    have hAp : A * (q : ℝ) ^ (-2 * η) ≤ (c / 256) * (q : ℝ) ^ (-η) :=
      mul_le_mul hAc hpr hp.le (by positivity)
    calc
      A * (q : ℝ) ^ (-2 * η) *
          (256 * (1 + Real.log (dirichletLNonquadraticConductorLogCutoff q T)) ^ 2) ≤
          ((c / 256) * (q : ℝ) ^ (-η)) *
            (256 * (1 + Real.log (dirichletLNonquadraticConductorLogCutoff q T)) ^ 2) := by
              gcongr
      _ = c * (q : ℝ) ^ (-η) *
          (1 + Real.log (dirichletLNonquadraticConductorLogCutoff q T)) ^ 2 := by ring
      _ ≤ c * (q : ℝ) ^ (-η) * H ^ 12 := by gcongr
  have hwlog : w ≤ 1 / (1 + Real.log (dirichletLNonquadraticConductorLogCutoff q T)) := by
    apply (le_div_iff₀ (lt_of_lt_of_le zero_lt_one hH₀)).2
    dsimp only [w]
    rw [div_mul_eq_mul_div, div_le_iff₀ (pow_pos hHpos 12)]
    have hAp1 : A * (q : ℝ) ^ (-2 * η) ≤ 1 := by
      have hp1 : (q : ℝ) ^ (-2 * η) ≤ 1 := by
        simpa using Real.rpow_le_rpow_of_exponent_le hq1 (by linarith : -2 * η ≤ 0)
      calc
        A * (q : ℝ) ^ (-2 * η) ≤ (1 / 2 : ℝ) * 1 :=
          mul_le_mul hAhalf hp1 hp.le (by norm_num)
        _ ≤ 1 := by norm_num
    calc
      A * (q : ℝ) ^ (-2 * η) *
          (1 + Real.log (dirichletLNonquadraticConductorLogCutoff q T)) ≤
          1 * (1 + Real.log (dirichletLNonquadraticConductorLogCutoff q T)) :=
            mul_le_mul_of_nonneg_right hAp1 (zero_le_one.trans hH₀)
      _ ≤ H ^ 12 := by
        have hHpow : H ≤ H ^ 12 := by
          simpa only [pow_one] using (pow_le_pow_right₀ hH (by norm_num : 1 ≤ 12))
        simpa only [one_mul] using hH₀H.trans hHpow
      _ = 1 * H ^ 12 := by ring
  simpa only [dirichletLQuadraticConditionalCentralH,
    dirichletLQuadraticConditionalCentralHeight,
    dirichletLQuadraticConditionalCrossZeroWidth, τ, H, w] using
    And.intro hH₀ (And.intro hτ (And.intro hτT (And.intro hH₀H
      (And.intro hH (And.intro hw (And.intro hwbudget hwlog))))))

private theorem LFunction_ne_zero_centralBand
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hquad : χ ^ 2 = 1) (hχ : χ ≠ 1)
    {A c η T β t : ℝ}
    (hA : 0 < A) (hAc : A ≤ c / 256) (hAhalf : A ≤ 1 / 2)
    (hc : 0 < c) (hη : 0 < η) (hT : 0 < T)
    (hSiegel : c * (q : ℝ) ^ (-η) ≤ (χ.LFunction 1).re)
    (hβ : 1 - dirichletLQuadraticConditionalCrossZeroWidth A c η q T ≤ β)
    (hβone : β < 1)
    (ht : |t| ≤ dirichletLQuadraticConditionalCentralHeight c η q T) :
    χ.LFunction (β + I * t) ≠ 0 := by
  let H₀ := dirichletLQuadraticConditionalCentralH q T
  let τ := dirichletLQuadraticConditionalCentralHeight c η q T
  let w := dirichletLQuadraticConditionalCrossZeroWidth A c η q T
  have hp := central_parameters (q := q) hA hAc hAhalf hc hη hT
  dsimp only at hp
  have htT : |t| ≤ T := ht.trans hp.2.2.1
  have hcut := dirichletLConductorHeightCutoff_le_fixedHeightCutoff (q := q) htT
  have hcutpos : (0 : ℝ) < dirichletLConductorHeightCutoff q t := by
    exact_mod_cast Nat.mul_pos (NeZero.pos q) (by simp [dirichletLHeightBlock])
  have hcutR : (dirichletLConductorHeightCutoff q t : ℝ) ≤
      dirichletLNonquadraticConductorLogCutoff q T := by exact_mod_cast hcut
  have hlog : 1 + Real.log (dirichletLConductorHeightCutoff q t) ≤ H₀ := by
    dsimp only [H₀, dirichletLQuadraticConditionalCentralH]
    linarith [Real.log_le_log hcutpos hcutR]
  have hβhalf : 1 / 2 ≤ β := by
    have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
    have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
    have hpq : 0 < (q : ℝ) ^ (-2 * η) := Real.rpow_pos_of_pos hq _
    have hpq1 : (q : ℝ) ^ (-2 * η) ≤ 1 := by
      simpa using Real.rpow_le_rpow_of_exponent_le hq1 (by linarith : -2 * η ≤ 0)
    have hH : 1 ≤ dirichletLQuadraticConditionalFixedH q τ T := hp.2.2.2.2.1
    have hHpow : 1 ≤ (dirichletLQuadraticConditionalFixedH q τ T) ^ 12 :=
      one_le_pow₀ hH
    have hw_half : w ≤ 1 / 2 := by
      dsimp only [w, dirichletLQuadraticConditionalCrossZeroWidth]
      exact (div_le_iff₀ (lt_of_lt_of_le zero_lt_one hHpow)).2
        ((mul_le_mul_of_nonneg_left hpq1 hA.le).trans (by nlinarith))
    dsimp only [w] at hw_half ⊢
    linarith
  have hnear : 1 - 1 / Real.log (dirichletLConductorHeightCutoff q t) ≤ β := by
    have hlogpos := log_conductorHeightCutoff_pos χ hχ t
    have hw_invlog : w ≤ 1 / Real.log (dirichletLConductorHeightCutoff q t) := by
      apply (le_div_iff₀ hlogpos).2
      have hwH₀ : w * H₀ ≤ 1 := by
        apply (le_div_iff₀ (lt_of_lt_of_le zero_lt_one hp.1)).mp
        exact hp.2.2.2.2.2.2.2
      calc
        w * Real.log (dirichletLConductorHeightCutoff q t) ≤ w * H₀ := by
          have hlog' : Real.log (dirichletLConductorHeightCutoff q t) ≤ H₀ := by linarith [hlog]
          exact mul_le_mul_of_nonneg_left hlog' hp.2.2.2.2.2.1.le
        _ ≤ 1 := hwH₀
    linarith
  have hhorizontal := norm_LFunction_sub_le_sixtyfour_mul_conductorHeightLogSq
    χ hχ hβhalf hnear hβone.le (by norm_num : (1 : ℝ) ≤ 2)
  have hvertical := norm_LFunction_vertical_sub_le_sixtyfour_mul_conductorHeightLogSq χ hχ t
  have hBh : ‖χ.LFunction (1 + t * I) - χ.LFunction (β + t * I)‖ ≤ 64 * H₀ ^ 2 * w := by
    calc
      _ ≤ 64 * (1 + Real.log (dirichletLConductorHeightCutoff q t)) ^ 2 * (1 - β) := by
        simpa using hhorizontal
      _ ≤ 64 * H₀ ^ 2 * w := by
        have hwidth : 1 - β ≤ w := by dsimp only [w] at hβ ⊢; linarith
        have hnonneg : 0 ≤ 1 - β := sub_nonneg.mpr hβone.le
        gcongr
  have hBv : ‖χ.LFunction (1 + t * I) - χ.LFunction 1‖ ≤ 64 * H₀ ^ 2 * τ := by
    calc
      _ ≤ 64 * (1 + Real.log (dirichletLConductorHeightCutoff q t)) ^ 2 * |t| := hvertical
      _ ≤ 64 * H₀ ^ 2 * τ := by gcongr
  have hwpay : 64 * H₀ ^ 2 * w ≤ c * (q : ℝ) ^ (-η) / 4 := by
    have hwraw := hp.2.2.2.2.2.2.1
    have hden : 0 < 256 * H₀ ^ 2 := by
      have : 0 < H₀ := lt_of_lt_of_le zero_lt_one hp.1
      positivity
    have hmul : 256 * H₀ ^ 2 * w ≤ c * (q : ℝ) ^ (-η) := by
      have hx := (le_div_iff₀ hden).mp (by simpa only [H₀, w] using hwraw)
      simpa only [mul_comm] using hx
    calc
      64 * H₀ ^ 2 * w = (1 / 4 : ℝ) * (256 * H₀ ^ 2 * w) := by ring
      _ ≤ (1 / 4 : ℝ) * (c * (q : ℝ) ^ (-η)) := by gcongr
      _ = c * (q : ℝ) ^ (-η) / 4 := by ring
  have hτpay : 64 * H₀ ^ 2 * τ ≤ c * (q : ℝ) ^ (-η) / 4 := by
    have hτbound : τ ≤ c * (q : ℝ) ^ (-η) / (256 * H₀ ^ 2) := by
      dsimp only [τ, dirichletLQuadraticConditionalCentralHeight]
      exact min_le_right _ _
    have hH₀pos : 0 < H₀ := lt_of_lt_of_le zero_lt_one hp.1
    have hden : 0 < 256 * H₀ ^ 2 := by positivity
    have hmul : 256 * H₀ ^ 2 * τ ≤ c * (q : ℝ) ^ (-η) := by
      have hx := (le_div_iff₀ hden).mp hτbound
      simpa only [mul_comm] using hx
    calc
      64 * H₀ ^ 2 * τ = (1 / 4 : ℝ) * (256 * H₀ ^ 2 * τ) := by ring
      _ ≤ (1 / 4 : ℝ) * (c * (q : ℝ) ^ (-η)) := by gcongr
      _ = c * (q : ℝ) ^ (-η) / 4 := by ring
  have hbudget : 64 * H₀ ^ 2 * w + 64 * H₀ ^ 2 * τ < (χ.LFunction 1).re := by
    have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
    have hr : 0 < (q : ℝ) ^ (-η) := Real.rpow_pos_of_pos hq _
    have hhalf : 64 * H₀ ^ 2 * w + 64 * H₀ ^ 2 * τ ≤
        c * (q : ℝ) ^ (-η) / 2 := by linarith
    have hcr : 0 < c * (q : ℝ) ^ (-η) := mul_pos hc hr
    have hstrict : c * (q : ℝ) ^ (-η) / 2 < c * (q : ℝ) ^ (-η) := by linarith
    exact hhalf.trans_lt (hstrict.trans_le hSiegel)
  exact LFunction_ne_zero_lowHeight_of_twoSegmentBudgets χ hquad hχ hBh hBv hbudget

/-- A raw quadratic `L(1)` lower bound produces a single positive-width fixed
rectangle over every bounded height interval, including height zero. -/
theorem exists_LFunction_ne_zero_on_quadraticConditionalCrossZeroRectangle
    (c η : ℝ) (hc : 0 < c) (hη : 0 < η) :
    ∃ A : ℝ, 0 < A ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (T : ℝ),
        χ ^ 2 = 1 → χ ≠ 1 → 0 < T →
        c * (q : ℝ) ^ (-η) ≤ (χ.LFunction 1).re →
        ∀ s ∈ dirichletLQuadraticConditionalCrossZeroRectangle A c η q T,
          χ.LFunction s ≠ 0 := by
  obtain ⟨A₀, hA₀, hzero₀⟩ :=
    exists_dirichletL_quadratic_conditional_powerZeroFree c η hc hη
  let A : ℝ := min A₀ (min (c / 256) (1 / 2))
  have hA : 0 < A := lt_min hA₀ (lt_min (div_pos hc (by norm_num)) (by norm_num))
  have hAA₀ : A ≤ A₀ := min_le_left _ _
  have hAc : A ≤ c / 256 := (min_le_right _ _).trans (min_le_left _ _)
  have hAhalf : A ≤ 1 / 2 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨A, hA, ?_⟩
  intro q _ χ T hquad hχ hT hSiegel s hs
  let τ := dirichletLQuadraticConditionalCentralHeight c η q T
  let w := dirichletLQuadraticConditionalCrossZeroWidth A c η q T
  have hp := central_parameters (q := q) hA hAc hAhalf hc hη hT
  dsimp only at hp
  have hrect : (1 - w ≤ s.re ∧ s.re ≤ 2) ∧ (-T ≤ s.im ∧ s.im ≤ T) := by
    rw [dirichletLQuadraticConditionalCrossZeroRectangle, Complex.Rectangle,
      Complex.mem_reProdIm] at hs
    norm_num at hs
    rw [Set.uIcc_of_le (by
      have hw : 0 < w := hp.2.2.2.2.2.1
      linarith), Set.uIcc_of_le (by linarith : -T ≤ T)] at hs
    exact ⟨⟨hs.1.1, hs.1.2⟩, ⟨hs.2.1, hs.2.2⟩⟩
  by_cases hre : 1 ≤ s.re
  · exact χ.LFunction_ne_zero_of_one_le_re (Or.inl hχ) hre
  have hrelt : s.re < 1 := lt_of_not_ge hre
  by_cases hcentral : |s.im| ≤ τ
  · have hz := LFunction_ne_zero_centralBand χ hquad hχ hA hAc hAhalf hc hη hT hSiegel
      hrect.1.1 hrelt (by simpa only [τ] using hcentral)
    simpa only [mul_comm I, Complex.re_add_im] using hz
  · have hτabs : τ ≤ |s.im| := le_of_not_ge hcentral
    have hzero : ∀ (β t : ℝ),
        β ∈ Ico
          (1 - A * (q : ℝ) ^ (-2 * η) /
            (dirichletLQuadraticConditionalPowerZeroFreeH q t) ^ 12) 1 →
        χ.LFunction (β + I * t) ≠ 0 := by
      intro β t hβ
      apply hzero₀ q χ β t hquad hχ hSiegel
      refine ⟨?_, hβ.2⟩
      have hHpos : 0 < dirichletLQuadraticConditionalPowerZeroFreeH q t :=
        lt_of_lt_of_le zero_lt_one (one_le_dirichletLQuadraticConditionalPowerZeroFreeH q t)
      have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
      have hpq : 0 < (q : ℝ) ^ (-2 * η) := Real.rpow_pos_of_pos hq _
      have hwidth : A * (q : ℝ) ^ (-2 * η) /
          (dirichletLQuadraticConditionalPowerZeroFreeH q t) ^ 12 ≤
          A₀ * (q : ℝ) ^ (-2 * η) /
          (dirichletLQuadraticConditionalPowerZeroFreeH q t) ^ 12 := by
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hAA₀ hpq.le)
          (pow_nonneg hHpos.le 12)
      exact (sub_le_sub_left hwidth 1).trans hβ.1
    by_cases him : 0 ≤ s.im
    · apply LFunction_ne_zero_on_quadraticConditionalUpperRectangle χ hχ hA hp.2.1 hp.2.2.1 hzero
      rw [dirichletLQuadraticConditionalUpperRectangle, Complex.Rectangle,
        Complex.mem_reProdIm]
      norm_num
      rw [Set.uIcc_of_le (by
        change 1 - w ≤ 2
        linarith [hp.2.2.2.2.2.1]), Set.uIcc_of_le hp.2.2.1]
      refine ⟨⟨?_, hrect.1.2⟩, ?_, hrect.2.2⟩
      · simpa only [dirichletLQuadraticConditionalFixedLeft, w,
          dirichletLQuadraticConditionalCrossZeroWidth] using hrect.1.1
      · rw [abs_of_nonneg him] at hτabs
        exact hτabs
    · have him' : s.im ≤ 0 := le_of_not_ge him
      apply LFunction_ne_zero_on_quadraticConditionalLowerRectangle χ hχ hA hp.2.1 hp.2.2.1 hzero
      rw [dirichletLQuadraticConditionalLowerRectangle, Complex.Rectangle,
        Complex.mem_reProdIm]
      norm_num
      rw [Set.uIcc_of_le (by
        change 1 - w ≤ 2
        linarith [hp.2.2.2.2.2.1]), Set.uIcc_of_le (by linarith : -T ≤ -τ)]
      refine ⟨⟨?_, hrect.1.2⟩, hrect.2.1, ?_⟩
      · simpa only [dirichletLQuadraticConditionalFixedLeft, w,
          dirichletLQuadraticConditionalCrossZeroWidth] using hrect.1.1
      · rw [abs_of_nonpos him'] at hτabs
        linarith

end AnalyticNumberTheory.LargeSieve
