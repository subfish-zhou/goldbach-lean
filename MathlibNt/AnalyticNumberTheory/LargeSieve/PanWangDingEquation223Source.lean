import MathlibNt.AnalyticNumberTheory.LargeSieve.PanWangDingEquation223Contour

set_option maxHeartbeats 800000
noncomputable section
open Classical Complex Finset MeasureTheory Set Filter
open scoped BigOperators Topology
namespace AnalyticNumberTheory.LargeSieve

/-- Literal (2.15) abscissa. -/
def panSourceSigma (x : ℕ) : ℝ := 1 + 1 / Real.log x
/-- Literal (2.16) height. -/
def panSourceHeight (x : ℕ) : ℝ := Real.exp (2 * (Real.log x) ^ 2)

/-- Elementary telescoping majorant for the sum appearing in (2.23). -/
theorem panHalfSum_le (N : ℕ) : panHalfSum N ≤ 2 * Real.sqrt N := by
  induction N with
  | zero => simp [panHalfSum]
  | succ N ih =>
    have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg _
    have hNp : (0 : ℝ) < N + 1 := by positivity
    have ha := Real.sq_sqrt hN
    have hb := Real.sq_sqrt hNp.le
    have hab : Real.sqrt N ≤ Real.sqrt ((N : ℝ) + 1) := Real.sqrt_le_sqrt (by linarith)
    have hab0 := Real.sqrt_nonneg (N : ℝ)
    have hbp := Real.sqrt_pos.mpr hNp
    have hinv : (Real.sqrt ((N : ℝ) + 1))⁻¹ ≤
        2 * (Real.sqrt ((N : ℝ) + 1) - Real.sqrt N) := by
      rw [inv_eq_one_div, div_le_iff₀ hbp]
      nlinarith [sq_nonneg (Real.sqrt ((N : ℝ) + 1) - Real.sqrt N)]
    rw [panHalfSum, Finset.sum_Icc_succ_top (by omega)]
    change panHalfSum N + (Real.sqrt (↑(N + 1) : ℝ))⁻¹ ≤ _
    push_cast
    linarith

theorem panSourceSigma_bounds {x : ℕ} (hx : 1 ≤ Real.log x) :
    1 / 2 ≤ panSourceSigma x ∧ panSourceSigma x ≤ 2 := by
  have hp : 0 < Real.log x := by linarith
  have hpos := one_div_pos.mpr hp
  have hle : 1 / Real.log x ≤ 1 := (div_le_one hp).mpr hx
  unfold panSourceSigma
  constructor <;> linarith

theorem panSourceSigma_power_le {x y : ℕ} (hx : 1 ≤ Real.log x)
    (hy : 1 ≤ y) (hyx : y ≤ x) :
    (y : ℝ) ^ panSourceSigma x ≤ Real.exp 1 * y := by
  have hy0 : (0 : ℝ) < y := by exact_mod_cast hy
  have hexponent : 0 ≤ (Real.log (x : ℝ))⁻¹ := inv_nonneg.mpr (by linarith)
  rw [panSourceSigma, Real.rpow_add hy0, Real.rpow_one, one_div]
  calc
    _ ≤ (y : ℝ) * (x : ℝ) ^ (Real.log (x : ℝ))⁻¹ :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow hy0.le (by exact_mod_cast hyx) hexponent) hy0.le
    _ ≤ (y : ℝ) * Real.exp 1 :=
      mul_le_mul_of_nonneg_left Real.rpow_inv_log_le_exp_one hy0.le
    _ = _ := mul_comm _ _

/-- The original height dominates `x^4` once `log x ≥ 2`; no change of T. -/
theorem panSourceHeight_ge_fourth {x : ℕ} (hx : 2 ≤ Real.log x) :
    (x : ℝ) ^ 4 ≤ panSourceHeight x := by
  have hx0 : (0 : ℝ) < x := by
    by_contra h
    have hz : x = 0 := by exact_mod_cast (le_antisymm (le_of_not_gt h) (Nat.cast_nonneg x))
    norm_num [hz] at hx
  have hh : 4 * Real.log (x : ℝ) ≤ 2 * (Real.log x) ^ 2 := by nlinarith
  have he := Real.exp_le_exp.mpr hh
  rw [mul_comm (4 : ℝ), Real.exp_mul, Real.exp_log hx0] at he
  rw [← Real.rpow_natCast (x : ℝ) 4]
  exact he

/-- First displayed O-term in (2.23), with one absolute constant. -/
theorem pan223_source_halfsum_bound {q x : ℕ} (f : ℕ → ℂ)
    (hf : ∀ n, ‖f n‖ ≤ 1) (m H y A₁ A₂ k : ℕ) (χ : PrimitiveCharacter q)
    (hx : 1 ≤ Real.log x) (hy : 1 ≤ y) (hyx : y ≤ x) :
    ‖I * (∫ t in -(panSourceHeight x)..panSourceHeight x, chen1973VerticalSection
        (pan223Kernel f m H y A₁ A₂ k χ) (panSourceSigma x) t) -
      I * (∫ t in -(panSourceHeight x)..panSourceHeight x, chen1973VerticalSection
        (pan223Kernel f m H y A₁ A₂ k χ) (1 / 2) t)‖ ≤
      (4 * Real.exp 1) * (y : ℝ) / panSourceHeight x * panHalfSum H * panHalfSum A₂ := by
  have hσ := panSourceSigma_bounds hx
  have hT : 0 < panSourceHeight x := Real.exp_pos _
  have hH := panHalfSum_nonneg H
  have hA := panHalfSum_nonneg A₂
  have hy0 : (0 : ℝ) ≤ y := Nat.cast_nonneg _
  have hpow := panSourceSigma_power_le hx hy hyx
  refine (pan223_finite_shift_bound f hf m H y A₁ A₂ k χ hy hσ.1 hT).trans ?_
  have hw : 2 * (panSourceSigma x - 1 / 2) ≤ 4 := by linarith [hσ.2]
  have hb : 2 * (panSourceSigma x - 1 / 2) * (y : ℝ) ^ panSourceSigma x ≤
      4 * (Real.exp 1 * y) :=
    mul_le_mul hw hpow (Real.rpow_nonneg hy0 _) (by norm_num)
  have hh := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hb hT.le) hH) hA
  convert hh using 1; ring

/-- Second displayed O-term of (2.23); `y * sqrt y` is `y^(3/2)`. -/
theorem pan223_source_sqrt_bound {q x : ℕ} (f : ℕ → ℂ)
    (hf : ∀ n, ‖f n‖ ≤ 1) (m H y A₁ A₂ k : ℕ) (χ : PrimitiveCharacter q)
    (hx : 1 ≤ Real.log x) (hy : 1 ≤ y) (hyx : y ≤ x) (hAy : A₂ ≤ y) :
    ‖I * (∫ t in -(panSourceHeight x)..panSourceHeight x, chen1973VerticalSection
        (pan223Kernel f m H y A₁ A₂ k χ) (panSourceSigma x) t) -
      I * (∫ t in -(panSourceHeight x)..panSourceHeight x, chen1973VerticalSection
        (pan223Kernel f m H y A₁ A₂ k χ) (1 / 2) t)‖ ≤
      (16 * Real.exp 1) * ((y : ℝ) * Real.sqrt y) * Real.sqrt H / panSourceHeight x := by
  have hT : 0 < panSourceHeight x := Real.exp_pos _
  have hH := panHalfSum_nonneg H
  have hA := panHalfSum_nonneg A₂
  have hsumH := panHalfSum_le H
  have hsumA : panHalfSum A₂ ≤ 2 * Real.sqrt y :=
    (panHalfSum_le A₂).trans (mul_le_mul_of_nonneg_left
      (Real.sqrt_le_sqrt (by exact_mod_cast hAy)) (by norm_num))
  refine (pan223_source_halfsum_bound f hf m H y A₁ A₂ k χ hx hy hyx).trans ?_
  calc
    _ ≤ (4 * Real.exp 1) * (y : ℝ) / panSourceHeight x *
        (2 * Real.sqrt H) * (2 * Real.sqrt y) := by gcongr
    _ = _ := by ring

/-- `y * sqrt y` is precisely the source exponent, not a weaker surrogate. -/
theorem pan_y_mul_sqrt (y : ℕ) (hy : 0 < y) :
    (y : ℝ) * Real.sqrt y = (y : ℝ) ^ (3 / 2 : ℝ) := by
  have hy0 : (0 : ℝ) < y := by exact_mod_cast hy
  rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hy0,
    Real.rpow_one, ← Real.sqrt_eq_rpow]

/-- Last O-term in (2.23). The hypothesis `H ≤ x` is explicit; this does not
claim to have substituted the later choice `H=(2^j log^B x)^2`. -/
theorem pan223_source_inverse_square {q x : ℕ} (f : ℕ → ℂ)
    (hf : ∀ n, ‖f n‖ ≤ 1) (m H y A₁ A₂ k : ℕ) (χ : PrimitiveCharacter q)
    (hx : 2 ≤ Real.log x) (hy : 1 ≤ y) (hyx : y ≤ x) (hAy : A₂ ≤ y) (hHx : H ≤ x) :
    ‖I * (∫ t in -(panSourceHeight x)..panSourceHeight x, chen1973VerticalSection
        (pan223Kernel f m H y A₁ A₂ k χ) (panSourceSigma x) t) -
      I * (∫ t in -(panSourceHeight x)..panSourceHeight x, chen1973VerticalSection
        (pan223Kernel f m H y A₁ A₂ k χ) (1 / 2) t)‖ ≤
      (16 * Real.exp 1) * ((x : ℝ) ^ 2)⁻¹ := by
  have hx0 : (0 : ℝ) < x := by exact_mod_cast (hy.trans hyx)
  have hT : 0 < panSourceHeight x := Real.exp_pos _
  have hT4 := panSourceHeight_ge_fourth hx
  have hsq := Real.sq_sqrt hx0.le
  refine (pan223_source_sqrt_bound f hf m H y A₁ A₂ k χ (by linarith) hy hyx hAy).trans ?_
  calc
    _ ≤ (16 * Real.exp 1) * ((x : ℝ) * Real.sqrt x) * Real.sqrt x / panSourceHeight x := by
      gcongr
    _ = (16 * Real.exp 1) * (x : ℝ) ^ 2 / panSourceHeight x := by
      calc
        _ = (16 * Real.exp 1) * (x : ℝ) * (Real.sqrt x) ^ 2 / panSourceHeight x := by ring
        _ = _ := by rw [hsq]; ring
    _ ≤ (16 * Real.exp 1) * (x : ℝ) ^ 2 / (x : ℝ) ^ 4 := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity) hT4
    _ = _ := by field_simp

/-- Literal `y^(3/2) sqrt(H)/T` rendering of the second bound. -/
theorem pan223_source_three_halves_bound {q x : ℕ} (f : ℕ → ℂ)
    (hf : ∀ n, ‖f n‖ ≤ 1) (m H y A₁ A₂ k : ℕ) (χ : PrimitiveCharacter q)
    (hx : 1 ≤ Real.log x) (hy : 1 ≤ y) (hyx : y ≤ x) (hAy : A₂ ≤ y) :
    ‖I * (∫ t in -(panSourceHeight x)..panSourceHeight x, chen1973VerticalSection
        (pan223Kernel f m H y A₁ A₂ k χ) (panSourceSigma x) t) -
      I * (∫ t in -(panSourceHeight x)..panSourceHeight x, chen1973VerticalSection
        (pan223Kernel f m H y A₁ A₂ k χ) (1 / 2) t)‖ ≤
      (16 * Real.exp 1) * (y : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt H / panSourceHeight x := by
  simpa only [pan_y_mul_sqrt y hy] using
    pan223_source_sqrt_bound f hf m H y A₁ A₂ k χ hx hy hyx hAy

/-- Equation (2.23), uniform eventual form. The absolute constant and threshold
precede `q`, the character, `m`, every cell, and the bounded coefficients.
The bound in fact does not need the source's extra restriction `1 ≤ A₁`. -/
theorem pan223_source_uniform_eventual :
    ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℕ, ∀ x : ℕ, X₀ ≤ x →
      ∀ (q : ℕ) (χ : PrimitiveCharacter q) (m H y A₁ A₂ k : ℕ) (f : ℕ → ℂ),
      (∀ n, ‖f n‖ ≤ 1) → 1 ≤ y → y ≤ x → A₂ ≤ y → H ≤ x →
      ‖I * (∫ t in -(panSourceHeight x)..panSourceHeight x, chen1973VerticalSection
          (pan223Kernel f m H y A₁ A₂ k χ) (panSourceSigma x) t) -
        I * (∫ t in -(panSourceHeight x)..panSourceHeight x, chen1973VerticalSection
          (pan223Kernel f m H y A₁ A₂ k χ) (1 / 2) t)‖ ≤ C * ((x : ℝ) ^ 2)⁻¹ := by
  have he : ∀ᶠ x : ℕ in atTop, 2 ≤ Real.log (x : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (2 : ℝ))
  obtain ⟨X₀, hX⟩ := Filter.eventually_atTop.mp he
  refine ⟨16 * Real.exp 1, by positivity, X₀, ?_⟩
  intro x hx q χ m H y A₁ A₂ k f hf hy hyx hAy hHx
  exact pan223_source_inverse_square f hf m H y A₁ A₂ k χ (hX x hx) hy hyx hAy hHx

end AnalyticNumberTheory.LargeSieve