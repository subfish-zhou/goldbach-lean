import MathlibNt.SieveTheory.LiLiuPrereqBuchstabBands

/-!
# Uniform Buchstab asymptotics for the actual rough-integer count

For each fixed natural `M ≥ 2` and `u₀ > 1`, one real threshold works for
every `u ∈ [u₀,M]`. The accepted through-100 APIs remain as corollaries.
The normalization is proved positive, and the count retains the unit, real
floor endpoint, strict small-prime cutoff, and prime-square endpoint.
-/

set_option autoImplicit false

open Filter
open scoped Topology

namespace LiLiuPrereqBuchstab

theorem rpow_cutoff_bounds_fixed (M : ℕ) {x u : ℝ}
    (hx : 1 < x) (hu : 1 ≤ u) (huM : u ≤ M) :
    1 < x ^ (1 / u) ∧ x ^ (1 / M : ℝ) ≤ x ^ (1 / u) ∧
      x ^ (1 / u) ≤ x ∧ x ≤ (x ^ (1 / u)) ^ M ∧
      Real.log x / Real.log (x ^ (1 / u)) = u := by
  have hx0 : 0 < x := by linarith
  have hu0 : 0 < u := by linarith
  have hpow : 1 < x ^ (1 / u) := Real.one_lt_rpow hx (one_div_pos.mpr hu0)
  refine ⟨hpow, Real.rpow_le_rpow_of_exponent_le hx.le
    (one_div_le_one_div_of_le hu0 huM), ?_, ?_, ?_⟩
  · calc
      _ ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx.le
        (by simpa using one_div_le_one_div_of_le zero_lt_one hu)
      _ = x := Real.rpow_one x
  · rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    calc
      x = x ^ (1 : ℝ) := (Real.rpow_one x).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hx.le (by
        have h : 1 ≤ (M : ℝ) / u := (le_div_iff₀ hu0).2 (by linarith)
        convert h using 1
        ring)
  · rw [Real.log_rpow hx0]
    have hlx := (Real.log_pos hx).ne'
    field_simp

theorem rpow_buchstab_main_eq {x u : ℝ} (hx : 1 < x) (hu : 0 < u) :
    x * buchstab u / Real.log (x ^ (1 / u)) =
      u * buchstab u * x / Real.log x := by
  rw [Real.log_rpow (by linarith : 0 < x)]
  field_simp

theorem buchstab_normalization_pos {x u : ℝ} (hx : 1 < x) (hu : 1 ≤ u) :
    0 < u * buchstab u * x / Real.log x := by
  have hw := buchstab_pos hu
  have hl := Real.log_pos hx
  have hu0 : 0 < u := by linarith
  have hx0 : 0 < x := by linarith
  positivity

theorem roughCount_relative_band_error_fixed (M : ℕ) {x y : ℝ}
    (hy : primeErrorStart ≤ y) (hyx : y ≤ x) (hxy : x ≤ y ^ M) :
    |(roughCount x y : ℝ) /
        (x * buchstab (Real.log x / Real.log y) / Real.log y) - 1| ≤
      2 * buchstabBandConstant M * (buchstabRemainder y + y / x) := by
  have hy1 : 1 < y := by linarith [primeErrorStart_spec.1]
  have hx1 : 1 < x := hy1.trans_le hyx
  have hx0 : 0 < x := by linarith
  have hly : 0 < Real.log y := Real.log_pos hy1
  have hu : 1 ≤ Real.log x / Real.log y := by
    apply (le_div_iff₀ hly).2
    simpa using Real.log_le_log (by linarith : 0 < y) hyx
  have hw := one_half_le_buchstab hu
  have hw0 := buchstab_pos hu
  have hmain : 0 < x * buchstab (Real.log x / Real.log y) / Real.log y := by
    positivity
  have hC : 0 < buchstabBandConstant M := by linarith [buchstabBandConstant_ge M]
  have hr := buchstabRemainder_nonneg hy
  have hA : 0 ≤ buchstabRemainder y + y / x := by positivity
  have he : (roughCount x y : ℝ) /
      (x * buchstab (Real.log x / Real.log y) / Real.log y) - 1 =
      ((roughCount x y : ℝ) -
        x * buchstab (Real.log x / Real.log y) / Real.log y) /
          (x * buchstab (Real.log x / Real.log y) / Real.log y) := by
    field_simp
  rw [he, abs_div, abs_of_pos hmain]
  apply (div_le_iff₀ hmain).2
  apply (roughCount_buchstab_band_error_fixed M hy hyx hxy).trans
  have hb : 0 ≤ buchstabBandConstant M *
      (buchstabRemainder y + y / x) * (x / Real.log y) := by positivity
  have hm := mul_le_mul_of_nonneg_left hw hb
  have heq : buchstabBandConstant M *
      (buchstabRemainder y * (x / Real.log y) + y / Real.log y) =
      buchstabBandConstant M * (buchstabRemainder y + y / x) * (x / Real.log y) := by
    field_simp
  rw [heq]
  calc
    _ ≤ 2 * (buchstabBandConstant M * (buchstabRemainder y + y / x) *
        (x / Real.log y) * buchstab (Real.log x / Real.log y)) := by linarith only [hm]
    _ = _ := by ring

/-- A parameter-free upper bound for every normalized error in the compact band. -/
theorem roughCount_uniform_error_bound_fixed (M : ℕ) {x u u₀ : ℝ}
    (hx : 1 < x) (hu₀ : 1 < u₀) (hlo : u₀ ≤ u) (hhi : u ≤ M)
    (hstart : primeErrorStart ≤ x ^ (1 / M : ℝ)) :
    |(roughCount x (x ^ (1 / u)) : ℝ) /
        (u * buchstab u * x / Real.log x) - 1| ≤
      2 * buchstabBandConstant M *
        (buchstabRemainder (x ^ (1 / M : ℝ)) + x ^ (1 / u₀ - 1)) := by
  have hu : 1 ≤ u := (hu₀.trans_le hlo).le
  have hu0 : 0 < u := by linarith
  have hu₀0 : 0 < u₀ := by linarith
  have hx0 : 0 < x := by linarith
  obtain ⟨_, hlower, hyx, hxy, hlog⟩ := rpow_cutoff_bounds_fixed M hx hu hhi
  have h := roughCount_relative_band_error_fixed M (hstart.trans hlower) hyx hxy
  rw [hlog, rpow_buchstab_main_eq hx hu0] at h
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ (by
    have hC : 0 < buchstabBandConstant M := by linarith [buchstabBandConstant_ge M]
    positivity)
  apply add_le_add
  · exact antitoneOn_buchstabRemainder hstart (hstart.trans hlower) hlower
  · rw [Real.rpow_sub hx0, Real.rpow_one]
    apply div_le_div_of_nonneg_right _ hx0.le
    exact Real.rpow_le_rpow_of_exponent_le hx.le (one_div_le_one_div_of_le hu₀0 hlo)

/-- The majorant tends to zero before a value of `u` is chosen. -/
theorem tendsto_uniform_buchstab_majorant_fixed (M : ℕ) (hM : 2 ≤ M)
    {u₀ : ℝ} (hu₀ : 1 < u₀) :
    Tendsto (fun x : ℝ => 2 * buchstabBandConstant M *
      (buchstabRemainder (x ^ (1 / M : ℝ)) + x ^ (1 / u₀ - 1)))
      atTop (𝓝 0) := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hroot : Tendsto (fun x : ℝ => x ^ (1 / M : ℝ)) atTop atTop :=
    tendsto_rpow_atTop (one_div_pos.mpr hM0)
  have hexp : 0 < 1 - 1 / u₀ := by
    have hu₀0 : 0 < u₀ := by linarith
    have h := (div_lt_one hu₀0).2 hu₀
    linarith
  have hp : Tendsto (fun x : ℝ => x ^ (1 / u₀ - 1)) atTop (𝓝 0) := by
    rw [show 1 / u₀ - 1 = -(1 - 1 / u₀) by ring]
    exact tendsto_rpow_neg_atTop hexp
  simpa only [Function.comp_apply, add_zero, mul_zero] using
    (tendsto_const_nhds.mul ((tendsto_buchstabRemainder.comp hroot).add hp))

/-- Uniform asymptotics on every fixed finite band for the actual rough count.
The cap `M` precedes `X`, which precedes `x,u`. No threshold uniform over
growing caps, or through `u = 1`, is asserted. -/
theorem roughCount_uniform_buchstab_fixed (M : ℕ) (hM : 2 ≤ M)
    {u₀ : ℝ} (hu₀ : 1 < u₀)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ X : ℝ, 1 < X ∧ ∀ x ≥ X, ∀ u ∈ Set.Icc u₀ (M : ℝ),
      0 < u * buchstab u * x / Real.log x ∧
      |(roughCount x (x ^ (1 / u)) : ℝ) /
        (u * buchstab u * x / Real.log x) - 1| < ε := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hroot : Tendsto (fun x : ℝ => x ^ (1 / M : ℝ)) atTop atTop :=
    tendsto_rpow_atTop (one_div_pos.mpr hM0)
  have hsmall := (tendsto_uniform_buchstab_majorant_fixed M hM hu₀).eventually
    (gt_mem_nhds hε)
  have hlarge := hroot.eventually (eventually_ge_atTop primeErrorStart)
  obtain ⟨X, hX⟩ := eventually_atTop.1 (hsmall.and hlarge)
  refine ⟨max 2 X, lt_of_lt_of_le (by norm_num) (le_max_left _ _), ?_⟩
  intro x hx u hu
  have hx1 : 1 < x := lt_of_lt_of_le (by norm_num) ((le_max_left _ _).trans hx)
  obtain ⟨hεx, hstart⟩ := hX x ((le_max_right _ _).trans hx)
  exact ⟨buchstab_normalization_pos hx1 ((hu₀.trans_le hu.1).le),
    (roughCount_uniform_error_bound_fixed M hx1 hu₀ hu.1 hu.2 hstart).trans_lt hεx⟩

theorem rpow_cutoff_bounds {x u : ℝ} (hx : 1 < x) (hu : 1 ≤ u) (hu100 : u ≤ 100) :
    1 < x ^ (1 / u) ∧ x ^ (1 / 100 : ℝ) ≤ x ^ (1 / u) ∧
      x ^ (1 / u) ≤ x ∧ x ≤ (x ^ (1 / u)) ^ (100 : ℕ) ∧
      Real.log x / Real.log (x ^ (1 / u)) = u :=
  rpow_cutoff_bounds_fixed 100 hx hu hu100

theorem roughCount_relative_band_error {x y : ℝ}
    (hy : primeErrorStart ≤ y) (hyx : y ≤ x) (hxy : x ≤ y ^ (100 : ℕ)) :
    |(roughCount x y : ℝ) /
        (x * buchstab (Real.log x / Real.log y) / Real.log y) - 1| ≤
      2 * buchstabBandConstant 100 * (buchstabRemainder y + y / x) :=
  roughCount_relative_band_error_fixed 100 hy hyx hxy

theorem roughCount_uniform_error_bound {x u u₀ : ℝ}
    (hx : 1 < x) (hu₀ : 1 < u₀) (hlo : u₀ ≤ u) (hhi : u ≤ 100)
    (hstart : primeErrorStart ≤ x ^ (1 / 100 : ℝ)) :
    |(roughCount x (x ^ (1 / u)) : ℝ) /
        (u * buchstab u * x / Real.log x) - 1| ≤
      2 * buchstabBandConstant 100 *
        (buchstabRemainder (x ^ (1 / 100 : ℝ)) + x ^ (1 / u₀ - 1)) :=
  roughCount_uniform_error_bound_fixed 100 hx hu₀ hlo hhi hstart

theorem tendsto_uniform_buchstab_majorant {u₀ : ℝ} (hu₀ : 1 < u₀) :
    Tendsto (fun x : ℝ => 2 * buchstabBandConstant 100 *
      (buchstabRemainder (x ^ (1 / 100 : ℝ)) + x ^ (1 / u₀ - 1)))
      atTop (𝓝 0) :=
  tendsto_uniform_buchstab_majorant_fixed 100 (by norm_num) hu₀

/-- The accepted through-100 theorem, with its literal public API preserved. -/
theorem roughCount_uniform_buchstab {u₀ : ℝ} (hu₀ : 1 < u₀)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ X : ℝ, 1 < X ∧ ∀ x ≥ X, ∀ u ∈ Set.Icc u₀ 100,
      0 < u * buchstab u * x / Real.log x ∧
      |(roughCount x (x ^ (1 / u)) : ℝ) /
        (u * buchstab u * x / Real.log x) - 1| < ε :=
  roughCount_uniform_buchstab_fixed 100 (by norm_num) hu₀ hε

end LiLiuPrereqBuchstab
