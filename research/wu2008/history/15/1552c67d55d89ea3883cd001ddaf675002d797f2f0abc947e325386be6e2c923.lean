import MathlibNt.Wu2008DoubleSieve.BoxMassFinite

/-!
# A genuine uniform lower bound in Wu's shrinking boxes

For each fixed positive lower-prime exponent, one threshold works for all
real `N^α ≤ V ≤ N` and all of Wu's permitted `Δ`. In particular no
nonemptiness premise is imposed on a prime window.
-/

namespace Wu2008DoubleSieve

open Finset Filter
open scoped Classical Topology

theorem box_eventually_log_power_budget (m : ℕ) {c α : ℝ}
    (hc : 0 < c) (hα : 0 < α) :
    ∀ᶠ N : ℕ in atTop, c * Real.log (N : ℝ) ^ m ≤ (N : ℝ) ^ α := by
  have h := (isLittleO_log_rpow_rpow_atTop (m : ℝ) hα).bound (one_div_pos.mpr hc)
  have hr : ∀ᶠ x : ℝ in atTop, c * Real.log x ^ m ≤ x ^ α := by
    filter_upwards [h, eventually_ge_atTop (1 : ℝ)] with x hx hx1
    have hlog : 0 ≤ Real.log x := Real.log_nonneg hx1
    simp only [Real.rpow_natCast, Real.norm_of_nonneg (pow_nonneg hlog m),
      Real.norm_of_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ x) α)] at hx
    have hm := mul_le_mul_of_nonneg_left hx hc.le
    simpa only [← mul_assoc, mul_one_div_cancel (ne_of_gt hc), one_mul] using hm
  exact tendsto_natCast_atTop_atTop.eventually hr

/-- The actual shrinking-box mass is at least `1/(12 log(N)^5)`.
The threshold depends only on the fixed positive `α` and precedes every
real endpoint and every permitted `Δ`. The `V ≤ N` restriction is genuine. -/
theorem wu_primeWindow_reciprocal_mass_lower {α : ℝ} (hα : 0 < α) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ Δ V : ℝ,
      1 + Real.log (N : ℝ) ^ (-4 : ℝ) ≤ Δ →
      Δ < 1 + 2 * Real.log (N : ℝ) ^ (-4 : ℝ) →
      (N : ℝ) ^ α ≤ V → V ≤ N →
      1 / (12 * Real.log (N : ℝ) ^ 5) ≤
        ∑ p ∈ primeWindow N (V / Δ) V, (1 : ℝ) / p := by
  obtain ⟨C, hC, X₀, hfinite⟩ :=
    box_reciprocal_mass_trueLi_lower 8 (by norm_num)
  have hlogt : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hgrowth : ∀ᶠ N : ℕ in atTop,
      96 * C ≤ α ^ 8 * Real.log (N : ℝ) ^ 3 :=
    (Tendsto.const_mul_atTop (pow_pos hα 8)
      ((tendsto_pow_atTop (by decide : 3 ≠ 0)).comp hlogt)).eventually
        (eventually_ge_atTop (96 * C))
  have hαlog : ∀ᶠ N : ℕ in atTop, 1 ≤ α * Real.log (N : ℝ) :=
    (Tendsto.const_mul_atTop hα hlogt).eventually (eventually_ge_atTop 1)
  have hX : ∀ᶠ N : ℕ in atTop, (X₀ : ℝ) ≤ (N : ℝ) ^ α :=
    ((tendsto_rpow_atTop hα).comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (X₀ : ℝ))
  have htwo : ∀ᶠ N : ℕ in atTop, (2 : ℝ) ≤ (N : ℝ) ^ (α / 2) :=
    ((tendsto_rpow_atTop (show 0 < α / 2 by positivity)).comp
      tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 2)
  have hbudget := box_eventually_log_power_budget 5
    (show 0 < 24 * (1 / (α / 2) + 2) by positivity) hα
  apply eventually_atTop.mp
  filter_upwards [hgrowth, hαlog, hX, htwo, hbudget,
    convolutionWuWindows_eventually_lower_cutoff hα,
    hlogt.eventually (eventually_ge_atTop 1),
    eventually_ge_atTop (2 : ℕ)] with N hg hαL hNX hNtwo hbud hcut hL hN
  intro Δ V hΔlo hΔhi hVlo hVN
  let L := Real.log (N : ℝ)
  let X := (⌈V⌉₊ : ℝ)
  have hL0 : 0 < L := by dsimp [L]; linarith
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hYlow := hcut Δ hΔlo hΔhi V hVlo
  have hY2 : 2 ≤ V / Δ := hNtwo.trans hYlow
  have hΔ1 : 1 ≤ Δ := by
    have := Real.rpow_nonneg (le_of_lt hL0) (-4)
    dsimp [L] at this
    linarith
  have hΔ0 : 0 < Δ := by linarith
  have hsmall : Real.log (N : ℝ) ^ (-4 : ℝ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hL (by norm_num)
  have hΔ3 : Δ ≤ 3 := by linarith
  have hV0 : 0 < V := (Real.rpow_pos_of_pos hN0 α).trans_le hVlo
  have hYV : V / Δ ≤ V := (div_le_iff₀ hΔ0).mpr (by nlinarith)
  have hV2 : 2 ≤ V := hY2.trans hYV
  have hVX : V ≤ X := Nat.le_ceil V
  have hX2V : X ≤ 2 * V := by
    have := Nat.ceil_lt_add_one hV0.le
    dsimp [X]
    linarith
  have hX0 : 0 < X := hV0.trans_le hVX
  have hloglow : α * L ≤ Real.log X := by
    rw [← Real.log_rpow hN0]
    exact Real.log_le_log (Real.rpow_pos_of_pos hN0 α) (hVlo.trans hVX)
  have hlogone : 1 ≤ Real.log X := hαL.trans hloglow
  have hlog0 : 0 < Real.log X := by linarith
  have hlogup : Real.log X ≤ 2 * L := by
    have hXNN : X ≤ (N : ℝ) ^ 2 := by
      have hc := Nat.ceil_lt_add_one hV0.le
      have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
      dsimp [X]
      nlinarith
    calc
      _ ≤ Real.log ((N : ℝ) ^ 2) := Real.log_le_log hX0 hXNN
      _ = 2 * L := by simp [Real.log_pow, L]
  have hcX : X₀ ≤ ⌈V⌉₊ := by
    have ht : (X₀ : ℝ) ≤ (⌈V⌉₊ : ℝ) := hNX.trans (hVlo.trans hVX)
    exact_mod_cast ht
  have hf := hfinite N (by omega) (α / 2) (by positivity) (V / Δ) V
    hY2 hYV hYlow hcX
  change (V - V / Δ - 1) / Real.log X ≤
    V * (∑ p ∈ primeWindow N (V / Δ) V, (1 : ℝ) / p) +
      1 / (α / 2) + 1 + 2 * (C * X / Real.log X ^ (8 : ℝ)) at hf
  rw [show (8 : ℝ) = (8 : ℕ) by norm_num, Real.rpow_natCast] at hf
  have hwidth : V / (3 * L ^ 4) ≤ V - V / Δ := by
    have hΔL : 1 / L ^ 4 ≤ Δ - 1 := by
      have he : Real.log (N : ℝ) ^ (-4 : ℝ) = 1 / L ^ 4 := by
        rw [Real.rpow_neg hL0.le, show (4 : ℝ) = (4 : ℕ) by norm_num,
          Real.rpow_natCast]
        simp only [one_div]
      rw [he] at hΔlo
      linarith
    calc
      _ ≤ V / (Δ * L ^ 4) := by gcongr
      _ = V * (1 / L ^ 4) / Δ := by ring
      _ ≤ V * (Δ - 1) / Δ := by gcongr
      _ = V - V / Δ := by field_simp
  have hmain : V / (6 * L ^ 5) ≤ (V - V / Δ) / Real.log X := by
    calc
      _ = (V / (3 * L ^ 4)) / (2 * L) := by ring
      _ ≤ (V - V / Δ) / Real.log X := by gcongr
  have hE : 2 * (C * X / Real.log X ^ 8) ≤ V / (24 * L ^ 5) := by
    calc
      _ = (2 * C) * X / Real.log X ^ 8 := by ring
      _ ≤ (2 * C) * (2 * V) / (α * L) ^ 8 := by gcongr
      _ = 4 * C * V / (α ^ 8 * L ^ 8) := by ring
      _ ≤ V / (24 * L ^ 5) := by
        apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
        have ht := mul_le_mul_of_nonneg_right hg (show 0 ≤ V * L ^ 5 by positivity)
        dsimp [L] at *
        nlinarith
  have hD : 1 / (α / 2) + 2 ≤ V / (24 * L ^ 5) := by
    apply (le_div_iff₀ (by positivity)).mpr
    exact (by nlinarith [hbud] : (1 / (α / 2) + 2) * (24 * L ^ 5) ≤ (N : ℝ) ^ α)
      |>.trans hVlo
  have hround : 1 / Real.log X ≤ 1 := (div_le_one hlog0).mpr hlogone
  have hsplit : (V - V / Δ) / Real.log X =
      (V - V / Δ - 1) / Real.log X + 1 / Real.log X := by ring
  have hresult : V / (12 * L ^ 5) ≤
      V * (∑ p ∈ primeWindow N (V / Δ) V, (1 : ℝ) / p) := by
    have heq : V / (6 * L ^ 5) - 2 * (V / (24 * L ^ 5)) =
        V / (12 * L ^ 5) := by ring
    linarith
  apply (mul_le_mul_iff_right₀ hV0).mp
  simpa only [mul_one_div, mul_comm, one_div_mul_eq_div] using hresult

end Wu2008DoubleSieve
