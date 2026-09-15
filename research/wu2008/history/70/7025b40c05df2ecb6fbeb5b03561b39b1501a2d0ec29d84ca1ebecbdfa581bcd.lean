import MathlibNt.Wu2008DoubleSieve.BoxMassUpper

/-!
# Uniform prime mass in the actual boundary windows

Wu04 (3.17)--(3.19), source lines 1113--1149. The frozen true-li PNT
is the only prime-distribution input. A single threshold precedes both
real endpoints; in particular they may depend on a convolution atom.
-/

namespace Wu2008DoubleSieve

open Finset Filter Real
open scoped Classical Topology

theorem reboxing_relative_width_of_log {Y V κ : ℝ}
    (hY : 0 < Y) (hYV : Y ≤ V) (hκ : κ ≤ 1 / 2)
    (hlog : log (V / Y) ≤ κ) :
    V ≤ 2 * Y ∧ V - Y ≤ 2 * κ * Y := by
  have hV : 0 < V := hY.trans_le hYV
  have hh := one_sub_inv_le_log_of_pos (div_pos hV hY)
  have hi : (V / Y)⁻¹ = Y / V := by simp [div_eq_mul_inv]
  rw [hi] at hh
  have hm := mul_le_mul_of_nonneg_right (hh.trans hlog) hV.le
  have he : (1 - Y / V) * V = V - Y := by field_simp
  rw [he] at hm
  have hhalf := mul_le_mul_of_nonneg_right hκ hV.le
  have hκ0 : 0 ≤ κ := by
    have := log_nonneg ((one_le_div hY).2 hYV)
    linarith
  have hVY : V ≤ 2 * Y := by linarith
  refine ⟨hVY, hm.trans ?_⟩
  nlinarith

/-- Uniform finite-endpoint consequence of the strong PNT. There is no
restriction `V ≤ N`, no nonemptiness premise, and no primality assumption
on either real endpoint. -/
theorem reboxing_short_prime_mass_linear {α K : ℝ} (hα : 0 < α) (hK : 0 < K) :
    ∃ T : ℕ, ∀ N : ℕ, T ≤ N → ∀ Y V : ℝ,
      (N : ℝ) ^ α ≤ Y → Y ≤ V → V ≤ 2 * Y →
      V - Y ≤ K * Y / log (N : ℝ) ^ (4 : ℕ) →
      (∑ p ∈ primeWindow N Y V, (1 : ℝ) / p) ≤
        (K / α + 2) / log (N : ℝ) ^ (5 : ℕ) := by
  obtain ⟨C, hC, X₀, hfinite⟩ := box_reciprocal_mass_trueLi_upper 8 (by norm_num)
  have hlogt : Tendsto (fun N : ℕ => log (N : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hgrowth : ∀ᶠ N : ℕ in atTop, 8 * C ≤ α ^ 8 * log (N : ℝ) ^ (3 : ℕ) :=
    (Tendsto.const_mul_atTop (pow_pos hα 8)
      ((tendsto_pow_atTop (by decide : 3 ≠ 0)).comp hlogt)).eventually
        (eventually_ge_atTop (8 * C))
  have hαlog : ∀ᶠ N : ℕ in atTop, 1 ≤ α * log (N : ℝ) :=
    (Tendsto.const_mul_atTop hα hlogt).eventually (eventually_ge_atTop 1)
  have hX : ∀ᶠ N : ℕ in atTop, (X₀ : ℝ) ≤ (N : ℝ) ^ α :=
    ((tendsto_rpow_atTop hα).comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (X₀ : ℝ))
  have htwo : ∀ᶠ N : ℕ in atTop, (2 : ℝ) ≤ (N : ℝ) ^ α :=
    ((tendsto_rpow_atTop hα).comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop 2)
  apply eventually_atTop.mp
  filter_upwards [hgrowth, hαlog, hX, htwo,
    box_eventually_log_power_budget 5 (show (0 : ℝ) < 2 by norm_num) hα,
    hlogt.eventually (eventually_ge_atTop 1),
    eventually_ge_atTop (2 : ℕ)] with N hg hαL hNX hNtwo hbud hL hN
  intro Y V hYlo hYV hVY hwidth
  let L := log (N : ℝ)
  let X := (⌈V⌉₊ : ℝ)
  let Z := (⌈Y⌉₊ : ℝ)
  have hL0 : 0 < L := by dsimp [L]; linarith
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hY2 : 2 ≤ Y := hNtwo.trans hYlo
  have hY0 : 0 < Y := by linarith
  have hV0 : 0 < V := hY0.trans_le hYV
  have hVX : V ≤ X := Nat.le_ceil V
  have hYZ : Y ≤ Z := Nat.le_ceil Y
  have hX4Y : X ≤ 4 * Y := by
    have := Nat.ceil_lt_add_one hV0.le
    dsimp [X]
    linarith
  have hlogX : α * L ≤ log X := by
    rw [← log_rpow hN0]
    exact log_le_log (rpow_pos_of_pos hN0 α) (hYlo.trans (hYV.trans hVX))
  have hlogZ : α * L ≤ log Z := by
    rw [← log_rpow hN0]
    exact log_le_log (rpow_pos_of_pos hN0 α) (hYlo.trans hYZ)
  have hlogZ1 : 1 ≤ log Z := hαL.trans hlogZ
  have hlogZ0 : 0 < log Z := by linarith
  have hlogX0 : 0 < log X := (mul_pos hα hL0).trans_le hlogX
  have hcX : X₀ ≤ ⌈V⌉₊ := by
    have ht : (X₀ : ℝ) ≤ (⌈V⌉₊ : ℝ) := hNX.trans (hYlo.trans (hYV.trans hVX))
    exact_mod_cast ht
  have hf := hfinite N Y V hY2 hYV hcX
  change Y * (∑ p ∈ primeWindow N Y V, (1 : ℝ) / p) ≤
    (V - Y + 1) / log Z + 2 * (C * X / log X ^ (8 : ℝ)) + 1 at hf
  rw [show (8 : ℝ) = (8 : ℕ) by norm_num, rpow_natCast] at hf
  have hmain : (V - Y) / log Z ≤ Y * (K / α) / L ^ (5 : ℕ) := by
    calc
      _ ≤ (K * Y / L ^ (4 : ℕ)) / (α * L) := by gcongr
      _ = _ := by ring
  have hE : 2 * (C * X / log X ^ (8 : ℕ)) ≤ Y / L ^ (5 : ℕ) := by
    calc
      _ = (2 * C) * X / log X ^ (8 : ℕ) := by ring
      _ ≤ (2 * C) * (4 * Y) / (α * L) ^ (8 : ℕ) := by gcongr
      _ = 8 * C * Y / (α ^ (8 : ℕ) * L ^ (8 : ℕ)) := by ring
      _ ≤ Y / L ^ (5 : ℕ) := by
        apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
        have ht := mul_le_mul_of_nonneg_right hg (show 0 ≤ Y * L ^ (5 : ℕ) by positivity)
        dsimp [L] at *
        nlinarith
  have hround : 2 ≤ Y / L ^ (5 : ℕ) := by
    apply (le_div_iff₀ (by positivity)).mpr
    exact hbud.trans hYlo
  have hone : 1 / log Z ≤ 1 := (div_le_one hlogZ0).mpr hlogZ1
  have heq : (V - Y + 1) / log Z = (V - Y) / log Z + 1 / log Z := by ring
  have hm : Y * (∑ p ∈ primeWindow N Y V, (1 : ℝ) / p) ≤
      Y * ((K / α + 2) / L ^ (5 : ℕ)) := by
    have heq' : Y * ((K / α + 2) / L ^ (5 : ℕ)) =
        Y * (K / α) / L ^ (5 : ℕ) + 2 * (Y / L ^ (5 : ℕ)) := by ring
    linarith
  exact (mul_le_mul_iff_right₀ hY0).mp hm

/-- A logarithmic width `K/log(N)^4` at polynomial height has reciprocal
prime mass at most `(2K/α+2)/log(N)^5`, uniformly over all endpoints. -/
theorem reboxing_short_prime_mass {α K : ℝ} (hα : 0 < α) (hK : 0 < K) :
    ∃ T : ℕ, ∀ N : ℕ, T ≤ N → ∀ Y V : ℝ,
      (N : ℝ) ^ α ≤ Y → Y ≤ V →
      log (V / Y) ≤ K / log (N : ℝ) ^ (4 : ℕ) →
      (∑ p ∈ primeWindow N Y V, (1 : ℝ) / p) ≤
        (2 * K / α + 2) / log (N : ℝ) ^ (5 : ℕ) := by
  obtain ⟨T, hT⟩ := reboxing_short_prime_mass_linear hα
    (show 0 < 2 * K by positivity)
  have hlogt : Tendsto (fun N : ℕ => log (N : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hbudget : ∀ᶠ N : ℕ in atTop, 2 * K ≤ log (N : ℝ) ^ (4 : ℕ) :=
    ((tendsto_pow_atTop (by decide : 4 ≠ 0)).comp hlogt).eventually
      (eventually_ge_atTop (2 * K))
  apply eventually_atTop.mp
  filter_upwards [eventually_ge_atTop T, eventually_ge_atTop (2 : ℕ), hbudget]
    with N hN hN2 hbud
  intro Y V hY hYV hwidth
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hY0 : 0 < Y := (rpow_pos_of_pos hN0 α).trans_le hY
  have hL : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  have hκ : K / log (N : ℝ) ^ (4 : ℕ) ≤ 1 / 2 := by
    apply (div_le_iff₀ (by positivity)).2
    linarith
  obtain ⟨hVY, hlinear⟩ := reboxing_relative_width_of_log hY0 hYV hκ hwidth
  apply hT N hN Y V hY hYV hVY
  convert hlinear using 1
  ring

end Wu2008DoubleSieve
