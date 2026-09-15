import MathlibNt.Wu2008DoubleSieve.Omega3SourceSieveFactor

/-!
# Actual upper Rosser density at the switched source level

Both the canonical upper density and the local-product normalization are
proved producers. Their errors multiply X when this factor is consumed;
no estimate of X, or conversion of those errors to Theta, is asserted.
-/

namespace Wu2008DoubleSieve

open Finset Real Filter
open scoped Classical Topology
open MathlibNt.SieveTheory.SwitchingPrinciple
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne
open MathlibNt.SieveTheory.SingularSeries

theorem omega3_source_sqrt_tendsto {δ : ℝ} (hδhi : δ < 1 / 2) :
    Tendsto (fun N : ℕ => sqrt ((N : ℝ) ^ (1 / 2 - δ))) atTop atTop := by
  have heq : (fun N : ℕ => sqrt ((N : ℝ) ^ (1 / 2 - δ))) =
      (fun N : ℕ => (N : ℝ) ^ ((1 / 2 - δ) / 2)) := by
    funext N
    rw [sqrt_eq_rpow, ← rpow_mul (Nat.cast_nonneg N)]
    congr 1
    ring
  rw [heq]
  exact (tendsto_rpow_atTop (by linarith : 0 < (1 / 2 - δ) / 2)).comp
    tendsto_natCast_atTop_atTop

theorem omega3_source_rosser_density {δ ρ : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hρ : 0 < ρ) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ordinaryRosserMainSum true N 1 (⌊(N : ℝ) ^ (1 / 2 - δ)⌋₊ + 1)
        (sqrt ((N : ℝ) ^ (1 / 2 - δ))) ≤
      ((1 + ρ) * (1 + ρ * exp (-eulerMascheroniConstant)) *
        (8 / (1 - 2 * δ))) * wuSingularSeries N / log N := by
  obtain ⟨z0, hdensity⟩ := ordinaryRosser_upper_density_canonical hρ
  have hZTop := omega3_source_sqrt_tendsto hδhi
  have hlocal := hZTop.eventually
    (eventually_localSieveProduct_relative (2 / (1 / 2 - δ)) ρ
      (by
        have : 0 < 1 / 2 - δ := by linarith
        positivity) hρ)
  obtain ⟨T, hT⟩ := eventually_atTop.mp
    (show ∀ᶠ N : ℕ in atTop, 4 ≤ N ∧
      (sqrt ((N : ℝ) ^ (1 / 2 - δ)) ≥ max z0 3) ∧
      (∀ M : ℕ, 0 < M → Even M →
        (M : ℝ) ≤ (sqrt ((N : ℝ) ^ (1 / 2 - δ))) ^ (2 / (1 / 2 - δ)) →
        |localSieveProduct M (sqrt ((N : ℝ) ^ (1 / 2 - δ))) /
          (2 * exp (-eulerMascheroniConstant) * wuSingularSeries M /
            log (sqrt ((N : ℝ) ^ (1 / 2 - δ)))) - 1| ≤ ρ) from
      (eventually_ge_atTop 4).and
        ((hZTop.eventually (eventually_ge_atTop (max z0 3))).and hlocal))
  refine ⟨max 4 T, le_max_left _ _, ?_⟩
  intro N hN heven
  obtain ⟨hN4, hZ, hloc⟩ := hT N ((le_max_right _ _).trans hN)
  have hgeom := omega3_source_sieve_geometry (show 2 ≤ N by omega) hδ hδhi
  have hlog : 0 < log (sqrt ((N : ℝ) ^ (1 / 2 - δ))) := log_pos hgeom.2.1
  have hC : 0 < wuSingularSeries N := by
    rw [wuSingularSeries_eq_liu N (by omega)]
    exact liuUniversalProduct_pos.trans_le (liuUniversalProduct_le_liuSingularSeries N)
  have hmainpos :
      0 < 2 * exp (-eulerMascheroniConstant) * wuSingularSeries N /
        log (sqrt ((N : ℝ) ^ (1 / 2 - δ))) := by positivity
  have hlocalBound := (abs_le.mp
    (hloc N (by omega) heven (omega3_source_le_sqrt_power (by omega) hδhi).le)).2
  have hproduct :
      localSieveProduct N (sqrt ((N : ℝ) ^ (1 / 2 - δ))) ≤
        (1 + ρ) * (2 * exp (-eulerMascheroniConstant) * wuSingularSeries N /
          log (sqrt ((N : ℝ) ^ (1 / 2 - δ)))) := by
    apply (div_le_iff₀ hmainpos).mp
    linarith
  have hden := hdensity N 1 heven (sqrt ((N : ℝ) ^ (1 / 2 - δ)))
    ((N : ℝ) ^ (1 / 2 - δ)) 2 ((le_max_left _ _).trans hZ)
    (by have := (le_max_right _ _).trans hZ; linarith) (by positivity)
    hgeom.2.2.2.2.2.2.2.symm (by norm_num) (by norm_num)
  have hF : jr1965F 2 = exp eulerMascheroniConstant := by
    rw [jr1965F_eq_of_le_three (by norm_num : (2 : ℝ) ≤ 3)]
    ring
  rw [hF, one_mul, ← localSievePrimes_eq_primeWindow, ← localSieveProduct] at hden
  calc
    _ ≤ (exp eulerMascheroniConstant + ρ) *
        localSieveProduct N (sqrt ((N : ℝ) ^ (1 / 2 - δ))) := hden
    _ ≤ (exp eulerMascheroniConstant + ρ) *
        ((1 + ρ) * (2 * exp (-eulerMascheroniConstant) * wuSingularSeries N /
          log (sqrt ((N : ℝ) ^ (1 / 2 - δ))))) :=
      mul_le_mul_of_nonneg_left hproduct (by positivity)
    _ = _ := omega3_source_density_factor (by omega) hδhi

end Wu2008DoubleSieve
