import MathlibNt.SieveTheory.LiLiuGoldbachG12LocalScale

namespace G12LocalScale
open Real Filter
open scoped Topology
open MathlibNt.SieveTheory.LiLiuPrereqWF

/-- All fixed logarithmic offsets are absorbed before introducing local cells. -/
theorem eventually_offset (c ζ : ℝ) (hz : 0 < ζ) :
    ∀ᶠ N : ℕ in atTop, c ≤ ζ / 4 * log (N : ℝ) := by
  have h := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
    (eventually_ge_atTop (c / (ζ / 4)))
  filter_upwards [h] with N hN
  exact (div_le_iff₀ (by positivity : 0 < ζ / 4)).mp hN |>.trans_eq (mul_comm _ _)

/-- Source endpoints give uniform logarithmic coordinates without setting `x=N`. -/
theorem endpoint_logs {N e x T ζ : ℝ}
    (hN : 1 < N) (he : 0 < e)
    (heoff : |log e| ≤ ζ / 4 * log N)
    (h4off : log 4 ≤ ζ / 4 * log N)
    (h2off : log 2 ≤ ζ / 4 * log N)
    (hxlo : e * N ≤ x) (hxhi : x ≤ 4 * N)
    (hTlo : N ^ (4 / 53 : ℝ) / 2 ≤ T) (hThi : T ≤ N ^ (1 / 10 : ℝ)) :
    0 < x ∧ 0 < T ∧
    (1 - ζ / 4) * log N ≤ log x ∧ log x ≤ (1 + ζ / 4) * log N ∧
    (4 / 53 - ζ / 4) * log N ≤ log T ∧ log T ≤ (1 / 10) * log N := by
  have hNp : 0 < N := by linarith
  have hxp : 0 < x := lt_of_lt_of_le (mul_pos he hNp) hxlo
  have hTp : 0 < T := lt_of_lt_of_le (by positivity) hTlo
  have hxl := Real.log_le_log (mul_pos he hNp) hxlo
  have hxh := Real.log_le_log hxp hxhi
  have htl := Real.log_le_log (show 0 < N ^ (4 / 53 : ℝ) / 2 by positivity) hTlo
  have hth := Real.log_le_log hTp hThi
  rw [Real.log_mul he.ne' hNp.ne'] at hxl
  rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hNp.ne'] at hxh
  rw [Real.log_div (by positivity) (by norm_num), Real.log_rpow hNp] at htl
  rw [Real.log_rpow hNp] at hth
  refine ⟨hxp, hTp, ?_, ?_, ?_, hth⟩
  · linarith [neg_abs_le (log e)]
  · nlinarith
  · nlinarith

/-- Uniform local admission, with one cutoff before `x,T` and every later cell. -/
theorem uniform_admission (e ζ η : ℝ) (he : 0 < e)
    (hz : 0 < ζ) (hzsmall : ζ ≤ 1 / 100)
    (hη : 0 < η) (hηsmall : η < 1 / 8) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ x T : ℝ,
      e * N ≤ x → x ≤ 4 * N →
      (N : ℝ) ^ (4 / 53 : ℝ) / 2 ≤ T → T ≤ (N : ℝ) ^ (1 / 10 : ℝ) →
      1 < x ∧ 0 < T ∧ x ^ nu x T = T ∧
      ζ ≤ nu x T ∧ nu x T ≤ 1 / 10 + ζ / 10 ∧
      (N : ℝ) ^ (1 / 3 : ℝ) ≤ level x T ζ ∧ level x T ζ ≤ N ∧
      2 ≤ externalInternalLevel (level x T ζ) η := by
  have hlog := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
    (eventually_ge_atTop (3 * ((1 + η + η ^ 9) * log 2)))
  have hev : ∀ᶠ N : ℕ in atTop, ∀ x T : ℝ,
      e * N ≤ x → x ≤ 4 * N →
      (N : ℝ) ^ (4 / 53 : ℝ) / 2 ≤ T → T ≤ (N : ℝ) ^ (1 / 10 : ℝ) →
      1 < x ∧ 0 < T ∧ x ^ nu x T = T ∧
      ζ ≤ nu x T ∧ nu x T ≤ 1 / 10 + ζ / 10 ∧
      (N : ℝ) ^ (1 / 3 : ℝ) ≤ level x T ζ ∧ level x T ζ ≤ N ∧
      2 ≤ externalInternalLevel (level x T ζ) η := by
    filter_upwards [eventually_offset (|log e|) ζ hz, eventually_offset (log 4) ζ hz,
      eventually_offset (log 2) ζ hz, hlog, eventually_ge_atTop (2 : ℕ)] with N heo h4 h2 hd hN
    dsimp only [Function.comp_apply] at hd
    intro x T hxlo hxhi htlo hthi
    have hNr : 1 < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
    have hNp : 0 < (N : ℝ) := by linarith
    obtain ⟨hxp, htp, hxl, hxh, htl, hth⟩ := endpoint_logs hNr he heo h4 h2 hxlo hxhi htlo hthi
    obtain ⟨hlogx, hνlo, hνhi, hQl, hQh⟩ := logarithmic_geometry (Real.log_pos hNr) hz hzsmall hxl hxh htl hth
    have hx : 1 < x := (Real.log_pos_iff hxp.le).mp hlogx
    have hQp : 0 < level x T ζ := Real.rpow_pos_of_pos hxp _
    rw [← log_level hx] at hQl hQh
    have hlower : (N : ℝ) ^ (1 / 3 : ℝ) ≤ level x T ζ := by
      apply (Real.log_le_log_iff (by positivity) hQp).mp
      rw [Real.log_rpow hNp]
      linarith
    have hupper : level x T ζ ≤ N := (Real.log_le_log_iff hQp hNp).mp hQh
    refine ⟨hx, htp, recover_T hx htp, hνlo, hνhi, hlower, hupper, ?_⟩
    apply externalInternalLevel_ge_threshold (by norm_num) hη hηsmall
    apply (Real.log_le_log_iff (by positivity) hQp).mp
    rw [Real.log_rpow (by norm_num : (0 : ℝ) < 2)]
    linarith
  exact eventually_atTop.mp hev
end G12LocalScale
