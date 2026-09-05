import MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLConditionalValueSeries
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# A logarithmic conductor-height bound for nonprincipal Dirichlet L-values

The natural-order conditional series is cut at
`q * (⌊|t|⌋₊ + 1)`.  The finite part is bounded by a harmonic sum, while the
factor `q / m` in the Abel tail pays for the height of `s`.
-/

open Complex Finset

namespace DirichletLGlobalConductorLogValueBound

open DirichletLAbelWeightVariation
open DirichletLConditionalValueSeries

variable {q : ℕ} [NeZero q]

/-- The integral block which strictly dominates the analytic height. -/
noncomputable def dirichletLHeightBlock (t : ℝ) : ℕ := ⌊|t|⌋₊ + 1

/-- The natural conductor-height truncation point. -/
noncomputable def dirichletLConductorHeightCutoff (q : ℕ) (t : ℝ) : ℕ :=
  q * dirichletLHeightBlock t

private lemma character_nat_zero_of_ne_one
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) : χ (0 : ℕ) = 0 := by
  have hq1 : q ≠ 1 := by
    intro h
    subst q
    exact hχ (Subsingleton.elim _ _)
  letI : Fact (1 < q) :=
    ⟨Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨NeZero.ne q, hq1⟩⟩
  simpa only [Nat.cast_zero] using
    (MulChar.map_nonunit χ (a := (0 : ZMod q)) not_isUnit_zero)

/-- A nonprincipal character cannot have modulus zero or one. -/
lemma two_le_modulus_of_ne_one
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) : 2 ≤ q := by
  have hq1 : q ≠ 1 := by
    intro h
    subst q
    exact hχ (Subsingleton.elim _ _)
  exact (Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨NeZero.ne q, hq1⟩)

lemma abs_lt_heightBlock (t : ℝ) : |t| < dirichletLHeightBlock t := by
  simpa [dirichletLHeightBlock, Nat.cast_add, Nat.cast_one] using
    (Nat.lt_floor_add_one |t|)

lemma one_le_heightBlock (t : ℝ) : 1 ≤ dirichletLHeightBlock t := by
  simp [dirichletLHeightBlock]

lemma two_le_conductorHeightCutoff
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (t : ℝ) :
    2 ≤ dirichletLConductorHeightCutoff q t := by
  unfold dirichletLConductorHeightCutoff
  calc
    2 ≤ q := two_le_modulus_of_ne_one χ hχ
    _ = q * 1 := by simp
    _ ≤ q * dirichletLHeightBlock t := Nat.mul_le_mul_left q (one_le_heightBlock t)

lemma log_conductorHeightCutoff_pos
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (t : ℝ) :
    0 < Real.log (dirichletLConductorHeightCutoff q t) := by
  apply Real.log_pos
  exact_mod_cast (two_le_conductorHeightCutoff χ hχ t)

private lemma rpow_one_sub_le_exp_one
    {m k : ℕ} {σ : ℝ} (hm : 2 ≤ m) (hk1 : 1 ≤ k) (hkm : k ≤ m)
    (hnear : 1 - 1 / Real.log m ≤ σ) :
    (k : ℝ) ^ (1 - σ) ≤ Real.exp 1 := by
  have hlogm : 0 < Real.log (m : ℝ) := by
    apply Real.log_pos
    exact_mod_cast hm
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk1)
  rw [Real.rpow_def_of_pos hkpos]
  apply Real.exp_le_exp.mpr
  have hlogk0 : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg (by exact_mod_cast hk1)
  by_cases he : 1 - σ ≤ 0
  · nlinarith
  · have hepos : 0 < 1 - σ := lt_of_not_ge he
    have hlogle : Real.log (k : ℝ) ≤ Real.log (m : ℝ) := by
      exact Real.strictMonoOn_log.monotoneOn hkpos
        (show (0 : ℝ) < (m : ℝ) by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hm))
        (by exact_mod_cast hkm)
    have hene : 1 - σ ≤ 1 / Real.log (m : ℝ) := by linarith
    have hfirst : Real.log (k : ℝ) * (1 - σ) ≤
        Real.log (k : ℝ) * (1 / Real.log (m : ℝ)) :=
      mul_le_mul_of_nonneg_left hene hlogk0
    have hsecond : Real.log (k : ℝ) * (1 / Real.log (m : ℝ)) ≤
        Real.log (m : ℝ) * (1 / Real.log (m : ℝ)) :=
      mul_le_mul_of_nonneg_right hlogle (by positivity)
    have hprod := hfirst.trans hsecond
    rw [mul_one_div_cancel (ne_of_gt hlogm)] at hprod
    nlinarith

private lemma norm_prefix_le
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {σ t : ℝ} {m : ℕ}
    (hm : 2 ≤ m) (hnear : 1 - 1 / Real.log m ≤ σ) :
    ‖∑ k ∈ range m, cpowWeight (σ + I * t) k * χ k‖ ≤
      2 * Real.exp 1 * (1 + Real.log m) := by
  calc
    _ ≤ ∑ k ∈ range m, ‖cpowWeight (σ + I * t) k * χ k‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ range m, 2 * Real.exp 1 * ((k + 1 : ℕ) : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro k hk
      by_cases hk0 : k = 0
      · subst k
        rw [character_nat_zero_of_ne_one χ hχ]
        simp
        exact Real.exp_pos 1 |>.le
      · have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
        have hkm : k < m := Finset.mem_range.mp hk
        have hkpos : (0 : ℝ) < k := by exact_mod_cast (Nat.zero_lt_of_ne_zero hk0)
        have hpow := rpow_one_sub_le_exp_one hm hk1 hkm.le hnear
        have hinv : (k : ℝ)⁻¹ ≤ 2 * ((k + 1 : ℕ) : ℝ)⁻¹ := by
          rw [inv_eq_one_div, show 2 * ((k + 1 : ℕ) : ℝ)⁻¹ =
            2 / ((k + 1 : ℕ) : ℝ) by rw [div_eq_mul_inv]]
          rw [div_le_div_iff₀ hkpos (by positivity)]
          push_cast
          have hk1R : (1 : ℝ) ≤ k := by exact_mod_cast hk1
          nlinarith
        calc
          ‖cpowWeight (σ + I * t) k * χ k‖
              = ‖cpowWeight (σ + I * t) k‖ * ‖χ k‖ := norm_mul _ _
          _ ≤ ‖cpowWeight (σ + I * t) k‖ := by
            exact mul_le_of_le_one_right (norm_nonneg _) (χ.norm_le_one k)
          _ = (k : ℝ) ^ (-σ) := by
            rw [cpowWeight, Complex.norm_cpow_eq_rpow_re_of_pos hkpos]
            simp
          _ = (k : ℝ) ^ (1 - σ) * (k : ℝ)⁻¹ := by
            rw [← Real.rpow_neg_one, ← Real.rpow_add hkpos]
            congr 1
            ring
          _ ≤ Real.exp 1 * (k : ℝ)⁻¹ := by gcongr
          _ ≤ Real.exp 1 * (2 * ((k + 1 : ℕ) : ℝ)⁻¹) := by gcongr
          _ = 2 * Real.exp 1 * ((k + 1 : ℕ) : ℝ)⁻¹ := by ring
    _ = 2 * Real.exp 1 * (harmonic m : ℝ) := by
      simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
      rw [Finset.mul_sum]
    _ ≤ 2 * Real.exp 1 * (1 + Real.log m) := by
      gcongr
      exact_mod_cast harmonic_le_one_add_log m

private lemma norm_tail_le
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {σ t : ℝ}
    (hσlower : 1 / 2 ≤ σ) (hσupper : σ ≤ 2)
    (hnear : 1 - 1 / Real.log (dirichletLConductorHeightCutoff q t) ≤ σ) :
    ‖orderedValueSeries χ hχ (σ + I * t)
        (by have hσpos : 0 < σ := lt_of_lt_of_le (by norm_num) hσlower
            simpa using hσpos) -
        ∑ k ∈ range (dirichletLConductorHeightCutoff q t),
          cpowWeight (σ + I * t) k * χ k‖ ≤ 7 * Real.exp 1 := by
  let H := dirichletLHeightBlock t
  let m := dirichletLConductorHeightCutoff q t
  have hm : 2 ≤ m := two_le_conductorHeightCutoff χ hχ t
  have hH1 : (1 : ℝ) ≤ H := by exact_mod_cast one_le_heightBlock t
  have hHpos : (0 : ℝ) < H := lt_of_lt_of_le zero_lt_one hH1
  have htH : |t| < (H : ℝ) := by simpa [H] using abs_lt_heightBlock t
  have hσpos : 0 < σ := lt_of_lt_of_le (by norm_num) hσlower
  have hsre : (σ + I * t : ℂ).re = σ := by simp
  have hnorm : ‖(σ + I * t : ℂ)‖ ≤ σ + |t| := by
    calc
      _ ≤ ‖(σ : ℂ)‖ + ‖I * (t : ℂ)‖ := norm_add_le _ _
      _ = |σ| + |t| := by simp
      _ = σ + |t| := by rw [abs_of_pos hσpos]
  have hratio : ‖(σ + I * t : ℂ)‖ / σ ≤ 4 + 2 * |t| := by
    rw [div_le_iff₀ hσpos]
    nlinarith [abs_nonneg t]
  have hheightpay : (1 + ‖(σ + I * t : ℂ)‖ / σ) / (H : ℝ) ≤ 7 := by
    rw [div_le_iff₀ hHpos]
    nlinarith
  have hpow : (m : ℝ) ^ (1 - σ) ≤ Real.exp 1 :=
    rpow_one_sub_le_exp_one hm (by omega) (le_refl m) (by simpa [m] using hnear)
  have htail := norm_orderedValueSeries_sub_sum_range_le
    χ hχ (σ + I * t) (by simpa using hσpos) (m := m) (by omega)
  have hfactor : (q : ℝ) * (m : ℝ) ^ (-σ) = (m : ℝ) ^ (1 - σ) / H := by
    have hqpos : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
    have hmcast : (m : ℝ) = (q : ℝ) * (H : ℝ) := by
      simp [m, H, dirichletLConductorHeightCutoff]
    rw [show -σ = (1 - σ) + (-1) by ring, Real.rpow_add (by positivity),
      Real.rpow_neg_one, hmcast, div_eq_mul_inv]
    field_simp
  calc
    _ ≤ (q : ℝ) * ((m : ℝ) ^ (-σ) +
        (‖(σ + I * t : ℂ)‖ / σ) * (m : ℝ) ^ (-σ)) := by
          simpa [m, hsre] using htail
    _ = ((m : ℝ) ^ (1 - σ) / H) *
        (1 + ‖(σ + I * t : ℂ)‖ / σ) := by rw [← hfactor]; ring
    _ = (m : ℝ) ^ (1 - σ) *
        ((1 + ‖(σ + I * t : ℂ)‖ / σ) / H) := by ring
    _ ≤ Real.exp 1 * 7 := by gcongr
    _ = 7 * Real.exp 1 := by ring

/-- Sharp logarithmic growth in the conductor-height cutoff throughout the
near-one strip. -/
theorem norm_LFunction_le_thirtytwo_mul_one_add_log_conductorHeightCutoff
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {σ t : ℝ}
    (hσlower : 1 / 2 ≤ σ) (hσupper : σ ≤ 2)
    (hnear : 1 - 1 / Real.log (dirichletLConductorHeightCutoff q t) ≤ σ) :
    ‖χ.LFunction (σ + I * t)‖ ≤
      32 * (1 + Real.log (dirichletLConductorHeightCutoff q t)) := by
  let m := dirichletLConductorHeightCutoff q t
  have hm : 2 ≤ m := two_le_conductorHeightCutoff χ hχ t
  have hlog0 : 0 ≤ Real.log (m : ℝ) :=
    (log_conductorHeightCutoff_pos χ hχ t).le
  have hσpos : 0 < σ := lt_of_lt_of_le (by norm_num) hσlower
  have hseries := orderedValueSeries_eq_LFunction_of_re_pos
    χ hχ (σ + I * t) (by simpa using hσpos)
  have hprefix := norm_prefix_le χ hχ (σ := σ) (t := t) (m := m)
    hm (by simpa [m] using hnear)
  have htail := norm_tail_le χ hχ hσlower hσupper hnear
  change ‖χ.LFunction (σ + I * t)‖ ≤ 32 * (1 + Real.log (m : ℝ))
  rw [← hseries]
  calc
    _ ≤ ‖orderedValueSeries χ hχ (σ + I * t) (by simpa using hσpos) -
          ∑ k ∈ range m, cpowWeight (σ + I * t) k * χ k‖ +
        ‖∑ k ∈ range m, cpowWeight (σ + I * t) k * χ k‖ := by
          simpa only [sub_add_cancel] using norm_add_le
            (orderedValueSeries χ hχ (σ + I * t) (by simpa using hσpos) -
              ∑ k ∈ range m, cpowWeight (σ + I * t) k * χ k)
            (∑ k ∈ range m, cpowWeight (σ + I * t) k * χ k)
    _ ≤ 7 * Real.exp 1 + 2 * Real.exp 1 * (1 + Real.log m) := by
      gcongr
    _ ≤ 32 * (1 + Real.log m) := by
      have he : Real.exp 1 < 3 := Real.exp_one_lt_three
      nlinarith

end DirichletLGlobalConductorLogValueBound