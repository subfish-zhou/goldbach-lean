import MathlibNt.SieveTheory.LiLiuGoldbachS3LevelGeometry
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Filter

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

noncomputable def goldbachS3_sieveRatio (N : ℕ) (B : ℝ) (p : ℕ) : ℝ :=
  Real.log ((LiuWeight.panModulusCutoff N B / p : ℕ) : ℝ) /
    Real.log ((N : ℝ) ^ (4 / 53 : ℝ))

private theorem S3Ratio_quotient_bounds
    {N p : ℕ} {B : ℝ} (hN : 4 ≤ N) (hp : 1 ≤ p)
    (hD : 1 ≤ LiuWeight.panModulusCutoff N B / p)
    (hlog : 1 ≤ Real.log (N : ℝ)) (hB : 0 ≤ B) :
    (N : ℝ) ^ (1 / 2 : ℝ) / Real.log (N : ℝ) ^ B / (4 * (p : ℝ)) ≤
        ((LiuWeight.panModulusCutoff N B / p : ℕ) : ℝ) ∧
      ((LiuWeight.panModulusCutoff N B / p : ℕ) : ℝ) ≤
        (N : ℝ) ^ (1 / 2 : ℝ) / (p : ℝ) := by
  let q : ℝ := (N : ℝ) ^ (1 / 2 : ℝ) / Real.log (N : ℝ) ^ B
  let d : ℝ := ((LiuWeight.panModulusCutoff N B / p : ℕ) : ℝ)
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hq0 : 0 < q := div_pos (Real.rpow_pos_of_pos hN0 _)
    (Real.rpow_pos_of_pos (by linarith) _)
  have hd1 : 1 ≤ d := by
    dsimp [d]
    exact_mod_cast hD
  -- Natural division of the first floor is exactly the floor of the real quotient.
  have hfloor : (Nat.floor (q / (p : ℝ)) : ℝ) = d := by
    rw [Nat.floor_div_natCast]
    rfl
  have hround : q / (p : ℝ) < d + 1 := by
    simpa only [hfloor] using Nat.lt_floor_add_one (q / (p : ℝ))
  constructor
  · change q / (4 * (p : ℝ)) ≤ d
    have heq : q / (4 * (p : ℝ)) = (q / (p : ℝ)) / 4 := by ring
    rw [heq]
    linarith
  · have hdq : d ≤ q / (p : ℝ) := by
      rw [← hfloor]
      exact Nat.floor_le (div_nonneg hq0.le hp0.le)
    apply hdq.trans
    apply div_le_div_of_nonneg_right _ hp0.le
    exact div_le_self (Real.rpow_nonneg hN0.le _)
      (Real.one_le_rpow hlog hB)

private theorem S3Ratio_model_bounds
    {N p : ℕ} (hN : 4 ≤ N) (hp : 1 ≤ p)
    (hpl : (N : ℝ) ^ (4 / 53 : ℝ) ≤ (p : ℝ))
    (hpu : (p : ℝ) ≤ (N : ℝ) ^ (1 / 3 : ℝ)) :
    (53 / 24 : ℝ) ≤ ((1 / 2 : ℝ) - Real.log (p : ℝ) / Real.log (N : ℝ)) /
        (4 / 53 : ℝ) ∧
      ((1 / 2 : ℝ) - Real.log (p : ℝ) / Real.log (N : ℝ)) /
        (4 / 53 : ℝ) ≤ (45 / 8 : ℝ) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hL : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hl := Real.log_le_log (Real.rpow_pos_of_pos hN0 _) hpl
  have hu := Real.log_le_log hp0 hpu
  rw [Real.log_rpow hN0] at hl hu
  have hl' : (4 / 53 : ℝ) ≤ Real.log (p : ℝ) / Real.log (N : ℝ) :=
    (le_div_iff₀ hL).2 hl
  have hu' : Real.log (p : ℝ) / Real.log (N : ℝ) ≤ (1 / 3 : ℝ) :=
    (div_le_iff₀ hL).2 hu
  constructor <;> linarith

private theorem S3Ratio_error_tendsto (B : ℝ) :
    Tendsto (fun N : ℕ =>
      (Real.log 4 + B * Real.log (Real.log (N : ℝ))) /
        ((4 / 53 : ℝ) * Real.log (N : ℝ))) atTop (nhds 0) := by
  have hL : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hconst : Tendsto (fun N : ℕ => Real.log 4 / Real.log (N : ℝ))
      atTop (nhds 0) := tendsto_const_nhds.div_atTop hL
  have hloglog : Tendsto (fun N : ℕ =>
      Real.log (Real.log (N : ℝ)) / Real.log (N : ℝ)) atTop (nhds 0) := by
    simpa [Function.comp_def] using
      (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp hL
  have ht := (hconst.add (hloglog.const_mul B)).div_const (4 / 53 : ℝ)
  convert ht using 1
  · funext N
    ring
  · norm_num

private theorem S3Ratio_error_bound
    {N p : ℕ} {B : ℝ} (hN : 4 ≤ N) (hp : 1 ≤ p)
    (hD : 1 ≤ LiuWeight.panModulusCutoff N B / p)
    (hlog : 1 ≤ Real.log (N : ℝ)) (hB : 0 ≤ B) :
    |goldbachS3_sieveRatio N B p -
      ((1 / 2 : ℝ) - Real.log (p : ℝ) / Real.log (N : ℝ)) / (4 / 53 : ℝ)| ≤
        (Real.log 4 + B * Real.log (Real.log (N : ℝ))) /
          ((4 / 53 : ℝ) * Real.log (N : ℝ)) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hL : 0 < Real.log (N : ℝ) := by linarith
  have hden : 0 < (4 / 53 : ℝ) * Real.log (N : ℝ) := by positivity
  have hD0 : (0 : ℝ) < ((LiuWeight.panModulusCutoff N B / p : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < LiuWeight.panModulusCutoff N B / p by omega)
  obtain ⟨hl, hu⟩ := S3Ratio_quotient_bounds hN hp hD hlog hB
  have hlow0 : 0 < (N : ℝ) ^ (1 / 2 : ℝ) /
      Real.log (N : ℝ) ^ B / (4 * (p : ℝ)) := by positivity
  have hll := Real.log_le_log hlow0 hl
  have hlu := Real.log_le_log hD0 hu
  rw [Real.log_div (div_pos (Real.rpow_pos_of_pos hN0 _)
      (Real.rpow_pos_of_pos hL _)).ne' (mul_pos (by norm_num) hp0).ne',
    Real.log_div (Real.rpow_pos_of_pos hN0 _).ne' (Real.rpow_pos_of_pos hL _).ne',
    Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hp0.ne',
    Real.log_rpow hN0, Real.log_rpow hL] at hll
  rw [Real.log_div (Real.rpow_pos_of_pos hN0 _).ne' hp0.ne',
    Real.log_rpow hN0] at hlu
  have hmodel :
      ((1 / 2 : ℝ) - Real.log (p : ℝ) / Real.log (N : ℝ)) / (4 / 53 : ℝ) =
        ((1 / 2 : ℝ) * Real.log (N : ℝ) - Real.log (p : ℝ)) /
          ((4 / 53 : ℝ) * Real.log (N : ℝ)) := by
    field_simp
  unfold goldbachS3_sieveRatio
  rw [Real.log_rpow hN0, hmodel, ← sub_div, abs_div, abs_of_pos hden]
  apply (div_le_div_iff_of_pos_right hden).2
  rw [abs_of_nonpos (by linarith : Real.log
    ((LiuWeight.panModulusCutoff N B / p : ℕ) : ℝ) -
      ((1 / 2 : ℝ) * Real.log (N : ℝ) - Real.log (p : ℝ)) ≤ 0)]
  linarith

/-- One threshold controls the genuine rounded ratio and its moving argument
error for every integer in the full S3 window, not just for a fixed prime. -/
theorem goldbachS3_ratio_geometry
    (B ξ : ℝ) (hB : 0 ≤ B) (hξ : 0 < ξ) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → ∀ p : ℕ, 1 ≤ p →
      (N : ℝ) ^ (4 / 53 : ℝ) ≤ (p : ℝ) →
      (p : ℝ) ≤ (N : ℝ) ^ (1 / 3 : ℝ) →
      0 < ((LiuWeight.panModulusCutoff N B / p : ℕ) : ℝ) ∧
      (3 / 2 : ℝ) ≤ goldbachS3_sieveRatio N B p ∧
      goldbachS3_sieveRatio N B p ≤ 6 ∧
      |goldbachS3_sieveRatio N B p -
        ((1 / 2 : ℝ) - Real.log (p : ℝ) / Real.log (N : ℝ)) / (4 / 53 : ℝ)| ≤ ξ := by
  have hclose := (Metric.tendsto_nhds.1 (S3Ratio_error_tendsto B))
    (min ξ (1 / 4)) (lt_min hξ (by norm_num))
  have hlogs : ∀ᶠ N : ℕ in atTop, 1 ≤ Real.log (N : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop 1)
  have he : ∀ᶠ N : ℕ in atTop, 4 ≤ N ∧ ∀ p : ℕ, 1 ≤ p →
      (N : ℝ) ^ (4 / 53 : ℝ) ≤ (p : ℝ) →
      (p : ℝ) ≤ (N : ℝ) ^ (1 / 3 : ℝ) →
      0 < ((LiuWeight.panModulusCutoff N B / p : ℕ) : ℝ) ∧
      (3 / 2 : ℝ) ≤ goldbachS3_sieveRatio N B p ∧
      goldbachS3_sieveRatio N B p ≤ 6 ∧
      |goldbachS3_sieveRatio N B p -
        ((1 / 2 : ℝ) - Real.log (p : ℝ) / Real.log (N : ℝ)) / (4 / 53 : ℝ)| ≤ ξ := by
    filter_upwards [goldbachS3_level_eventually B, hlogs, hclose] with N hN hlog hc
    refine ⟨hN.1, ?_⟩
    intro p hp hpl hpu
    have hD : 1 ≤ LiuWeight.panModulusCutoff N B / p := by
      have := (hN.2 p (by omega) hpu).1
      omega
    have hb := S3Ratio_error_bound hN.1 hp hD hlog hB
    have hm := S3Ratio_model_bounds hN.1 hp hpl hpu
    rw [Real.dist_eq, sub_zero] at hc
    have herr := (le_abs_self _).trans hc.le
    have hquarter := hb.trans (herr.trans (min_le_right _ _))
    have hxi := hb.trans (herr.trans (min_le_left _ _))
    refine ⟨by exact_mod_cast (show 0 < LiuWeight.panModulusCutoff N B / p by omega),
      ?_, ?_, hxi⟩
    · linarith [(abs_le.mp hquarter).1]
    · linarith [(abs_le.mp hquarter).2]
  obtain ⟨M, hM⟩ := eventually_atTop.mp he
  refine ⟨max 4 M, le_max_left _ _, ?_⟩
  intro N hN
  exact (hM N ((le_max_right _ _).trans hN)).2

theorem goldbachS3_ratio_range
    (B : ℝ) (hB : 0 ≤ B) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → ∀ p : ℕ, 1 ≤ p →
      (N : ℝ) ^ (4 / 53 : ℝ) ≤ (p : ℝ) →
      (p : ℝ) ≤ (N : ℝ) ^ (1 / 3 : ℝ) →
      0 < ((LiuWeight.panModulusCutoff N B / p : ℕ) : ℝ) ∧
      (3 / 2 : ℝ) ≤ goldbachS3_sieveRatio N B p ∧ goldbachS3_sieveRatio N B p ≤ 6 := by
  obtain ⟨N₀, hN₀, h⟩ := goldbachS3_ratio_geometry B 1 hB zero_lt_one
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN p hp hl hu
  exact ⟨(h N hN p hp hl hu).1, (h N hN p hp hl hu).2.1,
    (h N hN p hp hl hu).2.2.1⟩

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig