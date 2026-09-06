import MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLQuadraticConditionalCentralLogDerivative

set_option maxHeartbeats 800000

/-!
# Quantitative quadratic logarithmic derivatives on the annulus and whole strip

The `(3,4,1)` value product gives more than nonvanishing on a fixed height
annulus.  After paying the principal Euler correction and the zeta pole-plus-log
factor, it forces an explicit lower bound for the quadratic `L`-value.  Combining
that bound with the production derivative estimate gives a quantitative `L'/L`
bound.  The final theorem joins this annular estimate to the central-band bound;
no compactness argument is used.
-/

open Complex Set

namespace AnalyticNumberTheory.LargeSieve

open DirichletLGlobalConductorLogValueBound
open DirichletLGlobalConductorLogDerivativeBound

private theorem fixedH_annular_bounds
    {q : ℕ} [NeZero q] {τ T t : ℝ}
    (hτ : 0 < τ) (hτT : τ ≤ T) (htlow : τ ≤ |t|) (htT : |t| ≤ T) :
    let H := dirichletLQuadraticConditionalFixedH q τ T
    1 ≤ H ∧
      1 + Real.log q ≤ H ∧
      1 + Real.log (|2 * t| + 2) + 1 / |2 * t| ≤ H ∧
      1 + Real.log (dirichletLConductorHeightCutoff q t) ≤ H := by
  dsimp only
  have hHt := dirichletLQuadraticConditionalPowerZeroFreeH_le_fixedH
    (q := q) hτ hτT htlow htT
  have hHone := one_le_dirichletLQuadraticConditionalPowerZeroFreeH q t
  have hcond := one_add_log_conductorHeightCutoff_le_quadraticH q t
  have ht : t ≠ 0 := by
    intro ht
    subst t
    simp only [abs_zero] at htlow
    linarith
  have hpole := one_add_log_twoHeight_add_inv_le_quadraticH q ht
  have hqcut : q ≤ dirichletLConductorHeightCutoff q t := by
    unfold dirichletLConductorHeightCutoff
    exact Nat.le_mul_of_pos_right q (by simp [dirichletLHeightBlock])
  have hqpos : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hcast : (q : ℝ) ≤ dirichletLConductorHeightCutoff q t := by exact_mod_cast hqcut
  have hlogq := Real.log_le_log hqpos hcast
  exact ⟨hHone.trans hHt, (by linarith [hcond.trans hHt]),
    hpole.trans hHt, hcond.trans hHt⟩

/-- The power-width lies both in the half-strip and in the logarithmic strip
needed by the value-difference and derivative estimates. -/
private theorem powerWidth_le_half_and_inv_log
    {A p H L : ℝ} (hA : 0 < A) (hAhalf : A ≤ 1 / 2)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (hH1 : 1 ≤ H)
    (hL : 0 < L) (hLH : L ≤ H) :
    let x := A * p / H ^ 12
    x ≤ 1 / 2 ∧ x ≤ 1 / L := by
  dsimp only
  have hH : 0 < H := zero_lt_one.trans_le hH1
  have hAp : A * p ≤ A := mul_le_of_le_one_right hA.le hp1
  have hHpow : 1 ≤ H ^ 12 := one_le_pow₀ hH1
  have hhalf : A * p / H ^ 12 ≤ 1 / 2 := by
    calc
      A * p / H ^ 12 ≤ A := by
        rw [div_le_iff₀ (pow_pos hH 12)]
        exact hAp.trans (le_mul_of_one_le_right hA.le hHpow)
      _ ≤ 1 / 2 := hAhalf
  refine ⟨hhalf, (le_div_iff₀ hL).2 ?_⟩
  calc
    A * p / H ^ 12 * L ≤ A * p / H ^ 12 * H :=
      mul_le_mul_of_nonneg_left hLH (by positivity)
    _ ≤ 1 := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (pow_pos hH 12), one_mul]
      have hAp1 : A * p ≤ 1 := hAp.trans (hAhalf.trans (by norm_num))
      have hHle : H ≤ H ^ 12 := by
        calc
          H = H * 1 := (mul_one H).symm
          _ ≤ H * H ^ 11 := mul_le_mul_of_nonneg_left (one_le_pow₀ hH1) hH.le
          _ = H ^ 12 := by ring
      exact (mul_le_of_le_one_left hH.le hAp1).trans hHle

/-- On a fixed nonzero-height annulus the value product supplies an explicit
lower bound of size `H² x`, where `x` is the fixed power-width.  All factors in
the value product are bounded by the actual principal Euler-correction and
pole-plus-log estimates. -/
theorem norm_LFunction_ge_on_quadraticConditionalAnnulus
    (Z : ℝ) (hZ : 0 < Z)
    (hzeta : ∀ (x u : ℝ), 0 < x → x ≤ 1 → u ≠ 0 →
      ‖riemannZeta (1 + x + I * u)‖ ≤
        Z * (1 + Real.log (|u| + 2) + 1 / |u|))
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hquad : χ ^ 2 = 1) (hχ : χ ≠ 1)
    {A η τ T β t : ℝ}
    (hA : 0 < A) (hAhalf : A ≤ 1 / 2)
    (hAsmall : A ≤ 1 / (16 * Z * 192 ^ 4))
    (hη : 0 < η) (hτ : 0 < τ) (hτT : τ ≤ T)
    (hβ : dirichletLQuadraticConditionalFixedLeft A η q τ T ≤ β)
    (hβone : β ≤ 1) (htlow : τ ≤ |t|) (htT : |t| ≤ T) :
    let H := dirichletLQuadraticConditionalFixedH q τ T
    let x := A * (q : ℝ) ^ (-2 * η) / H ^ 12
    64 * H ^ 2 * x ≤ ‖χ.LFunction (β + I * t)‖ := by
  dsimp only
  let H : ℝ := dirichletLQuadraticConditionalFixedH q τ T
  let p : ℝ := (q : ℝ) ^ (-2 * η)
  let x : ℝ := A * p / H ^ 12
  change 64 * H ^ 2 * x ≤ ‖χ.LFunction (β + I * t)‖
  have hb := fixedH_annular_bounds (q := q) hτ hτT htlow htT
  dsimp only at hb
  have hH1 : 1 ≤ H := by simpa only [H] using hb.1
  have hH : 0 < H := lt_of_lt_of_le zero_lt_one hH1
  have hq1 : (1 : ℝ) ≤ q := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hp : 0 < p := by
    dsimp only [p]
    exact Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hq1) _
  have hp1 : p ≤ 1 := by
    dsimp only [p]
    simpa using Real.rpow_le_rpow_of_exponent_le hq1 (by linarith : -2 * η ≤ 0)
  have hx : 0 < x := by dsimp only [x]; positivity
  have hlogH : 1 + Real.log (dirichletLConductorHeightCutoff q t) ≤ H := by
    simpa only [H] using hb.2.2.2
  obtain ⟨hxhalf, hxlog⟩ := powerWidth_le_half_and_inv_log
    hA hAhalf hp.le hp1 hH1 (log_conductorHeightCutoff_pos χ hχ t)
      (by linarith only [hlogH])
  have hx1 : x ≤ 1 := hxhalf.trans (by norm_num)
  have hβleft : 1 - x ≤ β := by
    simpa only [dirichletLQuadraticConditionalFixedLeft, x, p, H] using hβ
  have hβhalf : 1 / 2 ≤ β := by linarith only [hβleft, hxhalf]
  have hnear : 1 - 1 / Real.log (dirichletLConductorHeightCutoff q t) ≤ β := by
    linarith only [hβleft, hxlog]
  have hdiff0 := norm_LFunction_sub_le_sixtyfour_mul_conductorHeightLogSq
    χ hχ (σ₁ := β) (σ₂ := 1 + x) (t := t) hβhalf hnear
      (by linarith) (by linarith [hx1] : 1 + x ≤ 2)
  have hdiff :
      ‖χ.LFunction (1 + x + I * t) - χ.LFunction (β + I * t)‖ ≤
        128 * H ^ 2 * x := by
    calc
      _ ≤ 64 * (1 + Real.log (dirichletLConductorHeightCutoff q t)) ^ 2 *
          ((1 + x) - β) := by
            convert hdiff0 using 1; push_cast; ring
      _ ≤ 64 * H ^ 2 * (2 * x) := by
        have hwidth : 1 - β ≤ x := by linarith
        have hinterval : 0 ≤ (1 + x) - β := by linarith
        have htwo : (1 + x) - β ≤ 2 * x := by linarith
        gcongr
      _ = 128 * H ^ 2 * x := by ring
  have ht : t ≠ 0 := by
    intro ht
    subst t
    simp only [abs_zero] at htlow
    linarith
  have htriv : ‖DirichletCharacter.LFunctionTrivChar q (1 + x)‖ ≤ 2 / x := by
    rw [DirichletCharacter.LFunctionTrivChar]
    calc
      ‖(1 : DirichletCharacter ℂ q).LFunction (1 + x)‖ ≤ 1 + 1 / x := by
        convert norm_dirichletLFunction_le
          (1 : DirichletCharacter ℂ q) (1 + x) 0 (by linarith) using 1 <;> norm_num
      _ ≤ 2 / x := by
        rw [le_div_iff₀ hx]
        field_simp [ne_of_gt hx]
        linarith
  have hsquare := norm_quadraticSquare_LFunction_le_principalPolePlusLog
    Z hzeta χ hquad hx hx1 ht
  have hprod : 1 ≤
      ‖DirichletCharacter.LFunctionTrivChar q (1 + x)‖ ^ 3 *
        ‖χ.LFunction (1 + x + I * t)‖ ^ 4 *
        ‖(χ ^ 2).LFunction (1 + x + I * (2 * t))‖ := by
    have hpv := χ.norm_LFunction_product_ge_one hx t
    convert (show 1 ≤
        ‖DirichletCharacter.LFunctionTrivChar q (1 + x)‖ ^ 3 *
          ‖χ.LFunction (1 + x + I * t)‖ ^ 4 *
          ‖(χ ^ 2).LFunction (1 + x + 2 * I * t)‖ by
      simpa only [norm_mul, norm_pow] using hpv) using 1; ring
  by_contra! hlow
  have hright : ‖χ.LFunction (1 + x + I * t)‖ < 192 * H ^ 2 * x := by
    have htri := norm_add_le
      (χ.LFunction (1 + x + I * t) - χ.LFunction (β + I * t))
      (χ.LFunction (β + I * t))
    rw [sub_add_cancel] at htri
    nlinarith
  have hSpos : 0 < 1 + Real.log (|2 * t| + 2) + 1 / |2 * t| := by
    have habs : 0 < |2 * t| := abs_pos.mpr (mul_ne_zero (by norm_num) ht)
    have hlogtwo : 0 ≤ Real.log (|2 * t| + 2) :=
      Real.log_nonneg (by linarith [abs_nonneg (2 * t)])
    positivity
  have hmajor : 1 < (2 / x) ^ 3 * (192 * H ^ 2 * x) ^ 4 *
      ((1 + Real.log q) *
        (Z * (1 + Real.log (|2 * t| + 2) + 1 / |2 * t|))) := by
    calc
      1 ≤ ‖DirichletCharacter.LFunctionTrivChar q (1 + x)‖ ^ 3 *
          ‖χ.LFunction (1 + x + I * t)‖ ^ 4 *
          ‖(χ ^ 2).LFunction (1 + x + I * (2 * t))‖ := hprod
      _ ≤ (2 / x) ^ 3 * ‖χ.LFunction (1 + x + I * t)‖ ^ 4 *
          ‖(χ ^ 2).LFunction (1 + x + I * (2 * t))‖ := by gcongr
      _ ≤ (2 / x) ^ 3 * ‖χ.LFunction (1 + x + I * t)‖ ^ 4 *
          ((1 + Real.log q) *
            (Z * (1 + Real.log (|2 * t| + 2) + 1 / |2 * t|))) := by gcongr
      _ < _ := by gcongr
  have hmajorH : 1 < (2 / x) ^ 3 * (192 * H ^ 2 * x) ^ 4 *
      (H * (Z * H)) := by
    have hqH : 1 + Real.log q ≤ H := by simpa only [H] using hb.2.1
    have hSH : 1 + Real.log (|2 * t| + 2) + 1 / |2 * t| ≤ H := by
      simpa only [H] using hb.2.2.1
    have hfactorUpper :
        (1 + Real.log q) *
            (Z * (1 + Real.log (|2 * t| + 2) + 1 / |2 * t|)) ≤ H * (Z * H) := by
      gcongr
    exact hmajor.trans_le
      (mul_le_mul_of_nonneg_left hfactorUpper (by positivity))
  have hmul := mul_lt_mul_of_pos_left hmajorH (pow_pos hx 3)
  have hcontr : x ^ 3 < 8 * Z * 192 ^ 4 * H ^ 10 * x ^ 4 := by
    calc
      x ^ 3 = x ^ 3 * 1 := by ring
      _ < x ^ 3 * ((2 / x) ^ 3 * (192 * H ^ 2 * x) ^ 4 *
          (H * (Z * H))) := hmul
      _ = 8 * Z * 192 ^ 4 * H ^ 10 * x ^ 4 := by
        field_simp [ne_of_gt hx]
        ring
  have hdenpos : 0 < 16 * Z * 192 ^ 4 := by positivity
  have hZA : 16 * Z * 192 ^ 4 * A ≤ 1 := by
    simpa only [mul_comm, mul_left_comm, mul_assoc] using
      (le_div_iff₀ hdenpos).mp hAsmall
  have hZAp : 16 * Z * 192 ^ 4 * A * p ≤ 1 :=
    (mul_le_of_le_one_right (by positivity) hp1).trans hZA
  have hfactor : 8 * Z * 192 ^ 4 * A * p / H ^ 2 ≤ 1 / 2 := by
    rw [div_le_iff₀ (pow_pos hH 2)]
    nlinarith [one_le_pow₀ hH1 (n := 2)]
  have hid : 8 * Z * 192 ^ 4 * H ^ 10 * x ^ 4 =
      (8 * Z * 192 ^ 4 * A * p / H ^ 2) * x ^ 3 := by
    dsimp only [x]
    field_simp [ne_of_gt hH]
  rw [hid] at hcontr
  have hhalf :
      (8 * Z * 192 ^ 4 * A * p / H ^ 2) * x ^ 3 ≤ (1 / 2) * x ^ 3 :=
    mul_le_mul_of_nonneg_right hfactor (pow_nonneg hx.le 3)
  nlinarith [pow_pos hx 3]

/-- Quantitative `L'/L` bound throughout a fixed annulus.  The inverse value
cost is displayed as `H^12 / (A q^(-2η))`. -/
theorem norm_logDerivative_le_on_quadraticConditionalAnnulus
    (Z : ℝ) (hZ : 0 < Z)
    (hzeta : ∀ (x u : ℝ), 0 < x → x ≤ 1 → u ≠ 0 →
      ‖riemannZeta (1 + x + I * u)‖ ≤
        Z * (1 + Real.log (|u| + 2) + 1 / |u|))
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hquad : χ ^ 2 = 1) (hχ : χ ≠ 1)
    {A η τ T β t : ℝ}
    (hA : 0 < A) (hAhalf : A ≤ 1 / 2)
    (hAsmall : A ≤ 1 / (16 * Z * 192 ^ 4))
    (hη : 0 < η) (hτ : 0 < τ) (hτT : τ ≤ T)
    (hβ : dirichletLQuadraticConditionalFixedLeft A η q τ T ≤ β)
    (hβone : β ≤ 1) (htlow : τ ≤ |t|) (htT : |t| ≤ T) :
    ‖deriv χ.LFunction (β + I * t) / χ.LFunction (β + I * t)‖ ≤
      (dirichletLQuadraticConditionalFixedH q τ T) ^ 12 /
        (A * (q : ℝ) ^ (-2 * η)) := by
  let H : ℝ := dirichletLQuadraticConditionalFixedH q τ T
  let p : ℝ := (q : ℝ) ^ (-2 * η)
  let x : ℝ := A * p / H ^ 12
  change ‖deriv χ.LFunction (β + I * t) / χ.LFunction (β + I * t)‖ ≤
    H ^ 12 / (A * p)
  have hb := fixedH_annular_bounds (q := q) hτ hτT htlow htT
  dsimp only at hb
  have hH : 0 < H := lt_of_lt_of_le zero_lt_one (by simpa only [H] using hb.1)
  have hp : 0 < p := by
    dsimp only [p]
    exact Real.rpow_pos_of_pos (by exact_mod_cast NeZero.pos q) _
  have hx : 0 < x := by dsimp only [x]; positivity
  have hlower := norm_LFunction_ge_on_quadraticConditionalAnnulus
    Z hZ hzeta χ hquad hχ hA hAhalf hAsmall hη hτ hτT hβ hβone htlow htT
  dsimp only at hlower
  have hH1 : 1 ≤ H := by simpa only [H] using hb.1
  have hq1 : (1 : ℝ) ≤ q := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hp1 : p ≤ 1 := by
    dsimp only [p]
    simpa using Real.rpow_le_rpow_of_exponent_le hq1 (by linarith : -2 * η ≤ 0)
  have hlogH : 1 + Real.log (dirichletLConductorHeightCutoff q t) ≤ H := by
    simpa only [H] using hb.2.2.2
  obtain ⟨hxhalf, hxlog⟩ := powerWidth_le_half_and_inv_log
    hA hAhalf hp.le hp1 hH1 (log_conductorHeightCutoff_pos χ hχ t)
      (by linarith only [hlogH])
  have hβleft : 1 - x ≤ β := by
    simpa only [dirichletLQuadraticConditionalFixedLeft, x, p, H] using hβ
  have hβhalf : 1 / 2 ≤ β := by linarith only [hβleft, hxhalf]
  have hnear : 1 - 1 / Real.log (dirichletLConductorHeightCutoff q t) ≤ β := by
    linarith only [hβleft, hxlog]
  have hderiv := norm_deriv_LFunction_le_sixtyfour_mul_one_add_log_sq_conductorHeightCutoff
    χ hχ hβhalf (hβone.trans (by norm_num)) hnear
  rw [norm_div]
  calc
    ‖deriv χ.LFunction (β + I * t)‖ / ‖χ.LFunction (β + I * t)‖
        ≤ (64 * H ^ 2) / ‖χ.LFunction (β + I * t)‖ := by
          exact div_le_div_of_nonneg_right (hderiv.trans (by gcongr)) (norm_nonneg _)
    _ ≤ (64 * H ^ 2) / (64 * H ^ 2 * x) := by
          exact div_le_div_of_nonneg_left (by positivity) (by positivity) hlower
    _ = H ^ 12 / (A * p) := by
      dsimp only [x, p]
      field_simp [ne_of_gt hH, ne_of_gt hA, ne_of_gt hp]

/-- One quantitative bound on the complete cross-zero rectangle to the left of
`1`: the first summand pays the central band and the second the two annuli. -/
theorem norm_logDerivative_le_on_quadraticConditionalWholeBand
    (Z : ℝ) (hZ : 0 < Z)
    (hzeta : ∀ (x u : ℝ), 0 < x → x ≤ 1 → u ≠ 0 →
      ‖riemannZeta (1 + x + I * u)‖ ≤
        Z * (1 + Real.log (|u| + 2) + 1 / |u|))
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hquad : χ ^ 2 = 1) (hχ : χ ≠ 1)
    {A c η T β t : ℝ}
    (hA : 0 < A) (hAc : A ≤ c / 256) (hAhalf : A ≤ 1 / 2)
    (hAsmall : A ≤ 1 / (16 * Z * 192 ^ 4))
    (hc : 0 < c) (hη : 0 < η) (hT : 0 < T)
    (hSiegel : c * (q : ℝ) ^ (-η) ≤ (χ.LFunction 1).re)
    (hβ : 1 - dirichletLQuadraticConditionalCrossZeroWidth A c η q T ≤ β)
    (hβone : β ≤ 1) (htT : |t| ≤ T) :
    ‖deriv χ.LFunction (β + I * t) / χ.LFunction (β + I * t)‖ ≤
      (128 * (dirichletLQuadraticConditionalCentralH q T) ^ 2) /
          (c * (q : ℝ) ^ (-η)) +
        (dirichletLQuadraticConditionalFixedH q
          (dirichletLQuadraticConditionalCentralHeight c η q T) T) ^ 12 /
          (A * (q : ℝ) ^ (-2 * η)) := by
  let τ := dirichletLQuadraticConditionalCentralHeight c η q T
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hcut : (1 : ℝ) ≤ dirichletLNonquadraticConductorLogCutoff q T := by
    exact_mod_cast (show 1 ≤ dirichletLNonquadraticConductorLogCutoff q T by
      unfold dirichletLNonquadraticConductorLogCutoff
      exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (NeZero.ne q) (by
        unfold dirichletLNonquadraticConductorLogHeightBlock
        omega)))
  have hH₀ : 0 < dirichletLQuadraticConditionalCentralH q T := by
    dsimp only [dirichletLQuadraticConditionalCentralH]
    linarith [Real.log_nonneg hcut]
  have hτ : 0 < τ := by
    dsimp only [τ, dirichletLQuadraticConditionalCentralHeight]
    exact lt_min hT (by positivity)
  have hτT : τ ≤ T := by
    dsimp only [τ, dirichletLQuadraticConditionalCentralHeight]
    exact min_le_left _ _
  have hcentralNonneg : 0 ≤
      (128 * (dirichletLQuadraticConditionalCentralH q T) ^ 2) /
        (c * (q : ℝ) ^ (-η)) := by positivity
  have hannularNonneg : 0 ≤
      (dirichletLQuadraticConditionalFixedH q τ T) ^ 12 /
        (A * (q : ℝ) ^ (-2 * η)) := by positivity
  by_cases htcentral : |t| ≤ τ
  · have hcbd := norm_logDerivative_le_on_quadraticConditionalCentralBand
      χ hχ hA hAc hAhalf hc hη hT hSiegel hβ hβone
        (by simpa only [τ] using htcentral)
    exact hcbd.trans (le_add_of_nonneg_right (by simpa only [τ] using hannularNonneg))
  · have htlow : τ ≤ |t| := le_of_not_ge htcentral
    have habd := norm_logDerivative_le_on_quadraticConditionalAnnulus
      Z hZ hzeta χ hquad hχ hA hAhalf hAsmall hη hτ hτT
        (by simpa only [dirichletLQuadraticConditionalFixedLeft,
          dirichletLQuadraticConditionalCrossZeroWidth, τ] using hβ)
        hβone htlow htT
    exact habd.trans (by
      simpa only [τ] using le_add_of_nonneg_left hcentralNonneg)

/-- Closed quantitative headline: the zeta constant and a positive common width
are selected before the modulus, character, height and point. -/
theorem exists_quadraticConditionalWholeBand_logDerivativeBound
    (c η : ℝ) (hc : 0 < c) (hη : 0 < η) :
    ∃ A : ℝ, 0 < A ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (T β t : ℝ),
        χ ^ 2 = 1 → χ ≠ 1 → 0 < T →
        c * (q : ℝ) ^ (-η) ≤ (χ.LFunction 1).re →
        1 - dirichletLQuadraticConditionalCrossZeroWidth A c η q T ≤ β →
        β ≤ 1 → |t| ≤ T →
        ‖deriv χ.LFunction (β + I * t) / χ.LFunction (β + I * t)‖ ≤
          (128 * (dirichletLQuadraticConditionalCentralH q T) ^ 2) /
              (c * (q : ℝ) ^ (-η)) +
            (dirichletLQuadraticConditionalFixedH q
              (dirichletLQuadraticConditionalCentralHeight c η q T) T) ^ 12 /
              (A * (q : ℝ) ^ (-2 * η)) := by
  obtain ⟨Z, hZ, hzeta⟩ := zeta_pole_plus_log_bound
  let A : ℝ := min (c / 256) (min (1 / 2) (1 / (16 * Z * 192 ^ 4)))
  have hA : 0 < A := by
    dsimp only [A]
    exact lt_min (div_pos hc (by norm_num))
      (lt_min (by norm_num) (by positivity))
  refine ⟨A, hA, ?_⟩
  intro q _ χ T β t hquad hχ hT hSiegel hβ hβone htT
  apply norm_logDerivative_le_on_quadraticConditionalWholeBand
    Z hZ hzeta χ hquad hχ hA
  · exact min_le_left _ _
  · exact (min_le_right _ _).trans (min_le_left _ _)
  · exact (min_le_right _ _).trans (min_le_right _ _)
  · exact hc
  · exact hη
  · exact hT
  · exact hSiegel
  · exact hβ
  · exact hβone
  · exact htT

end AnalyticNumberTheory.LargeSieve