import MathlibNt.SieveTheory.LiLiuBuchstabSharpLog

set_option autoImplicit false

open Set MeasureTheory
open scoped BigOperators

namespace LiLiuBuchstabSharp

/-- An everywhere-continuous rational seed; its relevant domain is `[2,3]`. -/
noncomputable def rationalSeed (n : ℕ) (u : ℝ) : ℝ :=
  (1 + 2 * ∑ i ∈ Finset.range n,
    ((max 2 u - 2) / max 2 u) ^ (2 * i + 1) / (2 * i + 1)) / max 2 u

theorem continuous_rationalSeed (n : ℕ) : Continuous (rationalSeed n) := by
  have hd : ∀ u : ℝ, max 2 u ≠ 0 := by
    intro u
    have h := le_max_left (2 : ℝ) u
    linarith
  unfold rationalSeed
  fun_prop (disch := exact hd _)

theorem rationalSeed_eq {u : ℝ} (hu : 2 ≤ u) (n : ℕ) :
    rationalSeed n u = (1 + logLower n (u - 1)) / u := by
  unfold rationalSeed logLower
  rw [max_eq_right hu]
  congr 2
  congr 1
  apply Finset.sum_congr rfl
  intro i _hi
  congr 2
  congr 1 <;> ring

/-- This error estimate is uniform in the real parameter, not a finite-point test. -/
theorem rationalSeed_error {u : ℝ} (hu : 2 ≤ u) (hu₃ : u ≤ 3) :
    0 ≤ LiLiuPrereqBuchstab.buchstab u - rationalSeed 12 u ∧
      LiLiuPrereqBuchstab.buchstab u - rationalSeed 12 u ≤
        (1 / 200000000000 : ℝ) := by
  have h := logLower_twelve_error (x := u - 1) (by linarith) (by linarith)
  rw [LiLiuPrereqBuchstab.buchstab_eq_log_div hu hu₃, rationalSeed_eq hu]
  have hup : 0 < u := by linarith
  constructor
  · apply sub_nonneg.mpr
    exact div_le_div_of_nonneg_right (by linarith) hup.le
  · rw [← sub_div]
    apply (div_le_iff₀ hup).mpr
    nlinarith [h.2]

/-- One analytic method-of-steps extension, clamped only outside its use interval. -/
noncomputable def rationalStep (a : ℝ) (f : ℝ → ℝ) (u : ℝ) : ℝ :=
  (a * f a + ∫ t in a..max a u, f (t - 1)) / max a u

theorem continuous_rationalStep {a : ℝ} (ha : 0 < a) {f : ℝ → ℝ}
    (hf : Continuous f) : Continuous (rationalStep a f) := by
  have hc : Continuous (fun t : ℝ => f (t - 1)) :=
    hf.comp (continuous_id.sub continuous_const)
  have hp : Continuous (fun u : ℝ => ∫ t in a..u, f (t - 1)) :=
    continuous_iff_continuousAt.mpr
      (fun u => (hc.integral_hasStrictDerivAt a u).hasDerivAt.continuousAt)
  have hd : ∀ u : ℝ, max a u ≠ 0 := by
    intro u
    have h := le_max_left a u
    linarith
  exact (continuous_const.add (hp.comp (continuous_const.max continuous_id))).div
    (continuous_const.max continuous_id) hd

/-- Error does not grow under a full analytic delay step. The hypotheses here are
    used only internally to construct the unconditional `rationalStage_error`. -/
private theorem rationalStep_error {a E : ℝ} (ha : 2 ≤ a) {f : ℝ → ℝ}
    (hf : Continuous f)
    (he : ∀ v ∈ Icc (a - 1) a,
      0 ≤ LiLiuPrereqBuchstab.buchstab v - f v ∧
        LiLiuPrereqBuchstab.buchstab v - f v ≤ E)
    {u : ℝ} (hu : a ≤ u) (hu₁ : u ≤ a + 1) :
    0 ≤ LiLiuPrereqBuchstab.buchstab u - rationalStep a f u ∧
      LiLiuPrereqBuchstab.buchstab u - rationalStep a f u ≤ E := by
  have hb := he a ⟨by linarith, le_rfl⟩
  have hc : Continuous (fun t : ℝ => LiLiuPrereqBuchstab.buchstab (t - 1)) :=
    LiLiuPrereqBuchstab.continuous_buchstab.comp (continuous_id.sub continuous_const)
  have hfc : Continuous (fun t : ℝ => f (t - 1)) :=
    hf.comp (continuous_id.sub continuous_const)
  have hd := hc.sub hfc
  have hpt : ∀ t ∈ Icc a u,
      0 ≤ LiLiuPrereqBuchstab.buchstab (t - 1) - f (t - 1) ∧
        LiLiuPrereqBuchstab.buchstab (t - 1) - f (t - 1) ≤ E := by
    intro t ht
    exact he (t - 1) ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hlo := intervalIntegral.integral_nonneg (μ := volume) hu (fun t ht => (hpt t ht).1)
  have hhi := intervalIntegral.integral_mono_on hu (hd.intervalIntegrable a u)
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => E) volume a u)
    (fun t ht => (hpt t ht).2)
  rw [intervalIntegral.integral_const, smul_eq_mul] at hhi
  change (∫ t in a..u, LiLiuPrereqBuchstab.buchstab (t - 1) - f (t - 1)) ≤
    (u - a) * E at hhi
  rw [intervalIntegral.integral_sub (hc.intervalIntegrable a u)
    (hfc.intervalIntegrable a u)] at hlo hhi
  have hwe := LiLiuPrereqBuchstab.buchstab_weighted_sub_eq_integral ha hu
  have hup : 0 < u := by linarith
  have heq : u * rationalStep a f u = a * f a + ∫ t in a..u, f (t - 1) := by
    unfold rationalStep
    rw [max_eq_right hu]
    field_simp
  constructor
  · nlinarith [hb.1]
  · nlinarith [hb.2]

/-- Exact finite-integral expressions, starting from the twelve-term rational seed.
    Stage `n` is used only on `[n+2,n+3]`. -/
noncomputable def rationalStage : ℕ → ℝ → ℝ
  | 0 => rationalSeed 12
  | n + 1 => rationalStep ((n : ℝ) + 3) (rationalStage n)

theorem continuous_rationalStage (n : ℕ) : Continuous (rationalStage n) := by
  induction n with
  | zero => exact continuous_rationalSeed 12
  | succ n ih =>
    exact continuous_rationalStep (by positivity) ih

/-- An unconditional enclosure for the actual Buchstab function, at every stage.
    No smallness property of a certificate or of Buchstab is an input. -/
theorem rationalStage_error (n : ℕ) {u : ℝ}
    (hu : (n : ℝ) + 2 ≤ u) (hub : u ≤ (n : ℝ) + 3) :
    0 ≤ LiLiuPrereqBuchstab.buchstab u - rationalStage n u ∧
      LiLiuPrereqBuchstab.buchstab u - rationalStage n u ≤
        (1 / 200000000000 : ℝ) := by
  induction n generalizing u with
  | zero => exact rationalSeed_error (by simpa using hu) (by simpa using hub)
  | succ n ih =>
    apply rationalStep_error (by have h := Nat.cast_nonneg (α := ℝ) n; linarith : (2 : ℝ) ≤ (n : ℝ) + 3)
      (continuous_rationalStage n)
    · intro v hv
      exact ih (by linarith [hv.1]) hv.2
    · push_cast at hu
      linarith
    · push_cast at hub
      linarith

/-- First half of the required starting window: the remaining expression is explicit. -/
theorem buchstab_sharp_window_left_enclosure {u : ℝ}
    (hu : (17 / 4 : ℝ) ≤ u) (hu₅ : u ≤ 5) :
    rationalStage 2 u ≤ LiLiuPrereqBuchstab.buchstab u ∧
      LiLiuPrereqBuchstab.buchstab u ≤ rationalStage 2 u +
        (1 / 200000000000 : ℝ) := by
  have h := rationalStage_error 2 (u := u) (by norm_num; linarith) (by norm_num; exact hu₅)
  constructor <;> linarith [h.1, h.2]

/-- Second half of the required starting window. This is an enclosure, not the sharp bound. -/
theorem buchstab_sharp_window_right_enclosure {u : ℝ}
    (hu : (5 : ℝ) ≤ u) (hu₅ : u ≤ (21 / 4 : ℝ)) :
    rationalStage 3 u ≤ LiLiuPrereqBuchstab.buchstab u ∧
      LiLiuPrereqBuchstab.buchstab u ≤ rationalStage 3 u +
        (1 / 200000000000 : ℝ) := by
  have h := rationalStage_error 3 (u := u) (by norm_num; exact hu) (by norm_num; linarith)
  constructor <;> linarith [h.1, h.2]

end LiLiuBuchstabSharp