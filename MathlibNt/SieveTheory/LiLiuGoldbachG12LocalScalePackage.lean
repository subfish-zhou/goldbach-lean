import MathlibNt.SieveTheory.LiLiuGoldbachG12LocalScaleCoefficient

namespace G12LocalScale
open Real
open MathlibNt.SieveTheory.LiLiuPrereqWF

/-- The actual prime endpoint retains its original lower and upper coordinates. -/
theorem endpoint_coordinate {N r : ℝ} (hN : 1 < N)
    (hlo : N ^ (4 / 53 : ℝ) ≤ r) (hhi : r ≤ N ^ (1 / 10 : ℝ)) :
    4 / 53 ≤ log r / log N ∧ log r / log N ≤ 1 / 10 := by
  have hNp : 0 < N := by linarith
  have hrp : 0 < r := lt_of_lt_of_le (Real.rpow_pos_of_pos hNp _) hlo
  have hl := Real.log_le_log (Real.rpow_pos_of_pos hNp (4 / 53)) hlo
  have hh := Real.log_le_log hrp hhi
  rw [Real.log_rpow hNp] at hl hh
  exact ⟨(le_div_iff₀ (Real.log_pos hN)).2 hl, (div_le_iff₀ (Real.log_pos hN)).2 hh⟩

/-- A concrete witness rules out empty-domain admission for every source epsilon. -/
theorem source_domain_nonempty {N e : ℝ} (hN : 1 ≤ N) (he : e ≤ 1) :
    ∃ x T r : ℝ, e * N ≤ x ∧ x ≤ 4 * N ∧
      N ^ (4 / 53 : ℝ) / 2 ≤ T ∧ T ≤ r ∧
      N ^ (4 / 53 : ℝ) ≤ r ∧ r ≤ N ^ (1 / 10 : ℝ) := by
  have hNp : 0 ≤ N := by linarith
  have hp : 0 ≤ N ^ (4 / 53 : ℝ) := Real.rpow_nonneg hNp _
  refine ⟨N, N ^ (4 / 53 : ℝ), N ^ (4 / 53 : ℝ), ?_, ?_, ?_, le_rfl, le_rfl, ?_⟩
  · nlinarith
  · linarith
  · linarith
  · exact Real.rpow_le_rpow_of_exponent_le hN (by norm_num)

/-- One source-faithful cutoff controls admission, internal level and the main
coefficient simultaneously. In particular `x` may be the physical value `4*M*T`;
no equality between the local and ambient scales is assumed. -/
theorem uniform_source_package (δ : ℝ) (hδ : 0 < δ) :
    ∃ ζ : ℝ, 0 < ζ ∧ ζ ≤ 1 / 100 ∧
      ∀ e η : ℝ, 0 < e → 0 < η → η < 1 / 8 →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ x T r : ℝ,
      e * N ≤ x → x ≤ 4 * N →
      (N : ℝ) ^ (4 / 53 : ℝ) / 2 ≤ T → T ≤ r →
      (N : ℝ) ^ (4 / 53 : ℝ) ≤ r → r ≤ (N : ℝ) ^ (1 / 10 : ℝ) →
      1 < x ∧ 0 < T ∧ x ^ nu x T = T ∧
      ζ ≤ nu x T ∧ nu x T ≤ 1 / 10 + ζ / 10 ∧
      (N : ℝ) ^ (1 / 3 : ℝ) ≤ level x T ζ ∧ level x T ζ ≤ N ∧
      2 ≤ externalInternalLevel (level x T ζ) η ∧
      4 / 53 ≤ log r / log (N : ℝ) ∧ log r / log (N : ℝ) ≤ 1 / 10 ∧
      4 * log (N : ℝ) / log (level x T ζ) ≤
        36 / (5 * (1 - log r / log (N : ℝ))) + δ := by
  obtain ⟨ζ, hz, hzs, hcoeff⟩ := uniform_coefficient δ hδ
  refine ⟨ζ, hz, hzs, ?_⟩
  intro e η he hη hηs
  obtain ⟨A, hA⟩ := uniform_admission e ζ η he hz hzs hη hηs
  obtain ⟨B, hB⟩ := hcoeff e he
  refine ⟨max 2 (max A B), ?_⟩
  intro N hN x T r hxlo hxhi htlo hTr hrlo hrhi
  have hNA : A ≤ N := (le_trans (le_max_left A B) (le_max_right 2 (max A B))).trans hN
  have hNB : B ≤ N := (le_trans (le_max_right A B) (le_max_right 2 (max A B))).trans hN
  have hN2 : 2 ≤ N := (le_max_left 2 (max A B)).trans hN
  have hNr : 1 < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
  obtain ⟨hx, ht, hrep, hνl, hνu, hQl, hQu, hD⟩ := hA N hNA x T hxlo hxhi htlo (hTr.trans hrhi)
  obtain ⟨hul, huu⟩ := endpoint_coordinate hNr hrlo hrhi
  exact ⟨hx, ht, hrep, hνl, hνu, hQl, hQu, hD, hul, huu,
    hB N hNB x T r hxlo hxhi htlo hTr hrhi⟩
end G12LocalScale
