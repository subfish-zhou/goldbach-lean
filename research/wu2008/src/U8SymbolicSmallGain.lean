import U8OriginalSmallIntegral

/-! A symbolic coefficient certificate on the original small interval.
The literal old expression is recorded without importing the legacy mother chain.
No assertion about a replacement in the mother inequality is made here. -/
noncomputable section
open MeasureTheory Set
open scoped Interval
namespace OriginalU8.SymbolicSmallGain

def a : ℝ := 100/1327
def b : ℝ := 1/10

def L : ℝ := ∫ t in a..b, Real.log (2-3*t)/(t*(1-t))

/-- Literal expression of the old small integral after expanding its alpha.
This is expression provenance, not cross-lineage mother-theorem wiring. -/
theorem L_literal : L =
    ∫ t in (100/1327 : ℝ)..(1/10), Real.log (2-3*t)/(t*(1-t)) := rfl

theorem I_literal : Weighted.originalSmallIntegral =
    (9/10 : ℝ) * ∫ t in a..b, Real.log (2-3*t)/(t*(1-t)^2) := rfl

theorem a_lt_b : a < b := by norm_num [a,b]

private theorem domain {t : ℝ} (ht : t ∈ Icc a b) :
    0 < t ∧ 0 < 1-t ∧ (17/10 : ℝ) ≤ 2-3*t := by
  dsimp [a,b] at ht
  constructor
  · linarith [ht.1]
  constructor <;> linarith [ht.2]

/-- The coefficient identity is checked algebraically before integration. -/
theorem integrand_identity {t : ℝ} (ht : t ∈ Icc a b) :
    Real.log (2-3*t)/(t*(1-t)) -
      (9/10 : ℝ)*(Real.log (2-3*t)/(t*(1-t)^2)) =
      (b-t)*Real.log (2-3*t)/(t*(1-t)^2) := by
  obtain ⟨ht0,ht1,_⟩ := domain ht
  dsimp [b]
  field_simp [ht0.ne',ht1.ne']
  ring

/-- Reuse the frozen original outer integrability and inner identity. -/
theorem weighted_integrable :
    IntervalIntegrable (fun t => Real.log (2-3*t)/(t*(1-t)^2)) volume a b := by
  have hi : IntervalIntegrable (fun u => ∫ v in (1/3 : ℝ)..((1-u)/2),
      1/(u*v*(1-u-v)*(1-u))) volume a b :=
    Weighted.outer_integrable (a := a) (by norm_num [a]) a_lt_b.le
  apply hi.congr
  intro t ht
  rw [uIoc_of_le a_lt_b.le] at ht
  exact Weighted.inner_weighted_eq ⟨(by norm_num [a] : (0 : ℝ) < a).trans ht.1,
    by dsimp [b] at ht; linarith [ht.2]⟩

theorem old_integrable :
    IntervalIntegrable (fun t => Real.log (2-3*t)/(t*(1-t))) volume a b := by
  have hi := weighted_integrable.mul_continuousOn
    (show ContinuousOn (fun t : ℝ => 1-t) (uIcc a b) by fun_prop)
  apply hi.congr
  intro t ht
  rw [uIoc_of_le a_lt_b.le] at ht
  obtain ⟨ht0,ht1,_⟩ := domain ⟨ht.1.le,ht.2⟩
  dsimp only
  field_simp [ht0.ne',ht1.ne']

theorem gain_integrable :
    IntervalIntegrable (fun t => (b-t)*Real.log (2-3*t)/(t*(1-t)^2)) volume a b := by
  have hi := weighted_integrable.mul_continuousOn
    (show ContinuousOn (fun t : ℝ => b-t) (uIcc a b) by fun_prop)
  apply hi.congr
  intro t _
  dsimp only
  ring

/-- Exact replacement coefficient, with the normalization applied once. -/
theorem gain_identity : 2*(L-Weighted.originalSmallIntegral) =
    2 * ∫ t in a..b, (b-t)*Real.log (2-3*t)/(t*(1-t)^2) := by
  rw [I_literal,L,← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_sub old_integrable (weighted_integrable.const_mul (9/10))]
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le a_lt_b.le] at ht
  exact integrand_identity ht

/-- Universal logarithmic tangent bound; no numerical logarithm is evaluated. -/
theorem log_lower {t : ℝ} (ht : t ∈ Icc a b) :
    (7/17 : ℝ) ≤ Real.log (2-3*t) := by
  have hu := (domain ht).2.2
  have hu0 : 0 < 2-3*t := by linarith
  have hinv : (2-3*t)⁻¹ ≤ (10/17 : ℝ) := by
    rw [inv_eq_one_div]
    apply (div_le_iff₀ hu0).mpr
    linarith
  have hlog := Real.one_sub_inv_le_log_of_pos hu0
  linarith

theorem denominator_bounds {t : ℝ} (ht : t ∈ Icc a b) :
    0 < t*(1-t)^2 ∧ t*(1-t)^2 ≤ (1/10 : ℝ) := by
  obtain ⟨ht0,ht1,_⟩ := domain ht
  have htub : t ≤ (1/10 : ℝ) := ht.2
  have hs : (1-t)^2 ≤ 1 := by nlinarith
  exact ⟨mul_pos ht0 (sq_pos_of_pos ht1),
    (mul_le_mul_of_nonneg_left hs ht0.le).trans (by simpa using htub)⟩

theorem quotient_lower {t : ℝ} (ht : t ∈ Icc a b) :
    (70/17 : ℝ) ≤ Real.log (2-3*t)/(t*(1-t)^2) := by
  obtain ⟨hd0,hd⟩ := denominator_bounds ht
  apply (le_div_iff₀ hd0).mpr
  have hl := log_lower ht
  linarith

theorem gain_integrand_lower {t : ℝ} (ht : t ∈ Icc a b) :
    (70/17 : ℝ)*(b-t) ≤ (b-t)*Real.log (2-3*t)/(t*(1-t)^2) := by
  have h := mul_le_mul_of_nonneg_right (quotient_lower ht) (sub_nonneg.mpr ht.2)
  calc
    _ ≤ (Real.log (2-3*t)/(t*(1-t)^2))*(b-t) := h
    _ = _ := by ring

/-- The triangular affine weight is integrated exactly by library identities. -/
theorem affine_integral : (∫ t in a..b, (70/17 : ℝ)*(b-t)) =
    (35/17 : ℝ)*(b-a)^2 := by
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub (f := fun _ : ℝ => b) (g := fun t : ℝ => t)
      intervalIntegrable_const (continuous_id.intervalIntegrable a b),
    intervalIntegral.integral_const, integral_id]
  simp only [smul_eq_mul]
  ring

theorem gain_lower_bound : (70/17 : ℝ)*(b-a)^2 ≤
    2*(L-Weighted.originalSmallIntegral) := by
  have hm := intervalIntegral.integral_mono_on a_lt_b.le
    (show IntervalIntegrable (fun t : ℝ => (70/17 : ℝ)*(b-t)) volume a b from
      (by fun_prop : Continuous (fun t : ℝ => (70/17 : ℝ)*(b-t))).intervalIntegrable a b)
    gain_integrable (fun t ht => gain_integrand_lower ht)
  rw [affine_integral] at hm
  rw [gain_identity]
  linarith

theorem rational_lower_bound_pos : 0 < (70/17 : ℝ)*(b-a)^2 := by
  exact mul_pos (by norm_num) (sq_pos_of_pos (sub_pos.mpr a_lt_b))

theorem gain_pos : 0 < 2*(L-Weighted.originalSmallIntegral) :=
  rational_lower_bound_pos.trans_le gain_lower_bound

/-- Nonconditional literal endpoint for consumers in this modern environment. -/
theorem literal_gain_certificate :
    2*((∫ t in (100/1327 : ℝ)..(1/10), Real.log (2-3*t)/(t*(1-t))) -
      Weighted.originalSmallIntegral) =
      2*∫ t in (100/1327 : ℝ)..(1/10),
        ((1/10 : ℝ)-t)*Real.log (2-3*t)/(t*(1-t)^2) ∧
    (70/17 : ℝ)*((1/10 : ℝ)-(100/1327))^2 ≤
      2*((∫ t in (100/1327 : ℝ)..(1/10), Real.log (2-3*t)/(t*(1-t))) -
        Weighted.originalSmallIntegral) ∧
    0 < 2*((∫ t in (100/1327 : ℝ)..(1/10), Real.log (2-3*t)/(t*(1-t))) -
      Weighted.originalSmallIntegral) :=
  ⟨gain_identity,gain_lower_bound,gain_pos⟩

end OriginalU8.SymbolicSmallGain
