import MathlibNt.SieveTheory.LiLiuGoldbachG12LocalScaleUniform

namespace G12LocalScale
open Real Filter
open scoped Topology

/-- The endpoint can vary independently after the local scale is admitted. -/
theorem coefficient_of_logs {N x T r ζ δ : ℝ}
    (hN : 1 < N) (hx : 1 < x) (hT : 0 < T) (hTr : T ≤ r)
    (hr : r ≤ N ^ (1 / 10 : ℝ))
    (hz : 0 < ζ) (hzsmall : ζ ≤ 1 / 100)
    (hsmall : 48 * ζ ≤ δ)
    (hxl : (1 - ζ / 4) * log N ≤ log x)
    (hQl : log N / 3 ≤ log (level x T ζ)) :
    4 * log N / log (level x T ζ) ≤
      36 / (5 * (1 - log r / log N)) + δ := by
  have hL : 0 < log N := Real.log_pos hN
  have hNp : 0 < N := by linarith
  have hrp : 0 < r := lt_of_lt_of_le hT hTr
  have hR := Real.log_le_log hrp hr
  rw [Real.log_rpow hNp] at hR
  have hYR := Real.log_le_log hT hTr
  have ha : 1 / 2 ≤ (5 / 9) * (1 - log r / log N) := by
    have hh : log r / log N ≤ 1 / 10 := (div_le_iff₀ hL).2 hR
    linarith
  have hb : 1 / 3 ≤ log (level x T ζ) / log N := by
    apply (le_div_iff₀ hL).2
    linarith
  have hprod := mul_le_mul_of_nonneg_left hxl (show 0 ≤ 5 / 9 - ζ by linarith)
  have hζL : 0 ≤ ζ * (ζ * log N) := mul_nonneg hz.le (mul_nonneg hz.le hL.le)
  have hcompare : (5 / 9) * (log N - log r) - 2 * ζ * log N ≤ log (level x T ζ) := by
    rw [log_level hx]
    nlinarith
  have hab : (5 / 9) * (1 - log r / log N) - 2 * ζ ≤ log (level x T ζ) / log N := by
    apply (le_div_iff₀ hL).2
    calc
      ((5 / 9) * (1 - log r / log N) - 2 * ζ) * log N =
          (5 / 9) * (log N - log r) - 2 * ζ * log N := by field_simp
      _ ≤ _ := hcompare
  have hbridge := reciprocal_bridge ha hb hab (by linarith : 0 ≤ δ) hsmall
  have heq1 : 4 / (log (level x T ζ) / log N) = 4 * log N / log (level x T ζ) := by field_simp
  have heq2 : 4 / ((5 / 9) * (1 - log r / log N)) = 36 / (5 * (1 - log r / log N)) := by
    rw [div_mul_eq_div_div, div_mul_eq_div_div]
    norm_num
  rw [heq1, heq2] at hbridge
  exact hbridge

/-- Any requested coefficient slack is fixed before all scales and endpoints. -/
theorem uniform_coefficient (δ : ℝ) (hδ : 0 < δ) :
    ∃ ζ : ℝ, 0 < ζ ∧ ζ ≤ 1 / 100 ∧
      ∀ e : ℝ, 0 < e → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ x T r : ℝ,
      e * N ≤ x → x ≤ 4 * N →
      (N : ℝ) ^ (4 / 53 : ℝ) / 2 ≤ T → T ≤ r →
      r ≤ (N : ℝ) ^ (1 / 10 : ℝ) →
      4 * log (N : ℝ) / log (level x T ζ) ≤
        36 / (5 * (1 - log r / log (N : ℝ))) + δ := by
  let ζ := min (1 / 100 : ℝ) (δ / 48)
  have hz : 0 < ζ := lt_min (by norm_num) (by positivity)
  have hzs : ζ ≤ 1 / 100 := min_le_left _ _
  have hsmall : 48 * ζ ≤ δ := by have h := min_le_right (1 / 100 : ℝ) (δ / 48); dsimp [ζ]; linarith
  refine ⟨ζ, hz, hzs, ?_⟩
  intro e he
  have hev : ∀ᶠ N : ℕ in atTop, ∀ x T r : ℝ,
      e * N ≤ x → x ≤ 4 * N →
      (N : ℝ) ^ (4 / 53 : ℝ) / 2 ≤ T → T ≤ r →
      r ≤ (N : ℝ) ^ (1 / 10 : ℝ) →
      4 * log (N : ℝ) / log (level x T ζ) ≤
        36 / (5 * (1 - log r / log (N : ℝ))) + δ := by
    filter_upwards [eventually_offset (|log e|) ζ hz, eventually_offset (log 4) ζ hz,
      eventually_offset (log 2) ζ hz, eventually_ge_atTop (2 : ℕ)] with N heo h4 h2 hN
    intro x T r hxlo hxhi hTlo hTr hr
    have hNr : 1 < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
    obtain ⟨hxp, hTp, hxl, hxh, htl, hth⟩ := endpoint_logs hNr he heo h4 h2 hxlo hxhi hTlo (hTr.trans hr)
    obtain ⟨hlogx, _, _, hQl, _⟩ := logarithmic_geometry (Real.log_pos hNr) hz hzs hxl hxh htl hth
    have hx : 1 < x := (Real.log_pos_iff hxp.le).mp hlogx
    rw [← log_level hx] at hQl
    exact coefficient_of_logs hNr hx hTp hTr hr hz hzs hsmall hxl hQl
  exact eventually_atTop.mp hev
end G12LocalScale
