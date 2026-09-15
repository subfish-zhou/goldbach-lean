import MathlibNt.Wu2008DoubleSieve.LocalProductTail

/-!
# Wu's local product at a genuinely real cutoff

Wu04 §2 uses `p < z`, not `p ≤ z`; §3 (3.10) uses the prime set
`P(d N)`. Thus the exact frozen natural cutoff is `⌈z⌉₊`, and the
closed singular-series cutoff is `⌈z⌉₊ - 1`, including when `z` is prime.
-/

namespace Wu2008DoubleSieve

open Finset Real Filter
open MathlibNt.SieveTheory.SingularSeries
open MathlibNt.SieveTheory.MertensTheorem
open scoped Topology

/-- The actual source prime set below a real strict cutoff. -/
noncomputable def localSievePrimes (M : ℕ) (z : ℝ) : Finset ℕ :=
  (range ⌈z⌉₊).filter (fun p => p.Prime ∧ p.Coprime M)

theorem mem_localSievePrimes (M p : ℕ) (z : ℝ) :
    p ∈ localSievePrimes M z ↔ (p : ℝ) < z ∧ p.Prime ∧ p.Coprime M := by
  simp [localSievePrimes, Nat.lt_ceil]

/-- `V(z)` for `P(M)`: here `M` will be `d * N`. -/
noncomputable def localSieveProduct (M : ℕ) (z : ℝ) : ℝ :=
  ∏ p ∈ localSievePrimes M z, (1 - 1 / ((p : ℝ) - 1))

theorem localSieveProduct_eq_goldbach (M : ℕ) (z : ℝ) :
    localSieveProduct M z = goldbachSieveProduct M ⌈z⌉₊ := by
  unfold localSieveProduct localSievePrimes goldbachSieveProduct
  congr 1
  ext p
  simp only [mem_filter, mem_range]
  constructor
  · rintro ⟨hpz, hp, hc⟩
    exact ⟨hpz, hp, hp.coprime_iff_not_dvd.mp hc⟩
  · rintro ⟨hpz, hp, hc⟩
    exact ⟨hpz, hp, hp.coprime_iff_not_dvd.mpr hc⟩

/-- The closed cutoff exactly equivalent to strict sifting at `z`. -/
noncomputable def localClosedCutoff (z : ℝ) : ℕ := ⌈z⌉₊ - 1

theorem localClosedCutoff_bounds (z : ℝ) (hz : 3 ≤ z) :
    2 ≤ localClosedCutoff z ∧
      (localClosedCutoff z : ℝ) < z ∧
      z ≤ (localClosedCutoff z : ℝ) + 1 := by
  have hc : 2 < ⌈z⌉₊ := Nat.lt_ceil.mpr (by norm_num; linarith)
  have hc1 : 1 ≤ ⌈z⌉₊ := by omega
  have hcast : (localClosedCutoff z : ℝ) = (⌈z⌉₊ : ℝ) - 1 := by
    simp only [localClosedCutoff, Nat.cast_sub hc1, Nat.cast_one]
  refine ⟨by unfold localClosedCutoff; omega, ?_, ?_⟩
  · rw [hcast]
    have := Nat.ceil_lt_add_one (by linarith : 0 ≤ z)
    linarith
  · rw [hcast]
    simpa using (Nat.le_ceil z : z ≤ (⌈z⌉₊ : ℝ))

theorem tendsto_localClosedCutoff :
    Tendsto localClosedCutoff atTop atTop := by
  apply tendsto_atTop.2
  intro n
  filter_upwards [eventually_ge_atTop (max 3 ((n : ℝ) + 1))] with z hz
  have h := localClosedCutoff_bounds z ((le_max_left _ _).trans hz)
  have hn : (n : ℝ) + 1 ≤ z := (le_max_right _ _).trans hz
  exact_mod_cast (show (n : ℝ) ≤ localClosedCutoff z by linarith)

/-- Exact factor-two normalization, with the endpoint retained literally. -/
theorem localSieveProduct_identity (M : ℕ) (z : ℝ)
    (hM : Even M) (hz : 3 ≤ z) :
    localSieveProduct M z =
      2 * primeProduct (localClosedCutoff z) *
        liuSingularSeriesTruncated M (localClosedCutoff z) := by
  have hc := (localClosedCutoff_bounds z hz).1
  rw [localSieveProduct_eq_goldbach, sieveProduct_identity M ⌈z⌉₊
    (by unfold localClosedCutoff at hc; omega) hM,
    singularSeriesTruncated_eq_two_mul_liuSingularSeriesTruncated M
      (⌈z⌉₊ - 1) hM hc]
  change _ = 2 * primeProduct (⌈z⌉₊ - 1) *
    liuSingularSeriesTruncated M (⌈z⌉₊ - 1)
  ring

/-- Mertens' frozen quantitative estimate implies its scalar relative limit.
No singular-series normalization is assumed here. -/
theorem tendsto_mertens_relative :
    Tendsto (fun y : ℕ => primeProduct y * log y / exp (-eulerMascheroniConstant))
      atTop (𝓝 1) := by
  obtain ⟨C, hC⟩ := mertens_product_formula
  have hlog : Tendsto (fun y : ℕ => log (y : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hbound : Tendsto
      (fun y : ℕ => C / exp (-eulerMascheroniConstant) / log y) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hlog
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall fun y => norm_nonneg _) _ hbound
  filter_upwards [eventually_ge_atTop 2] with y hy
  have hly : 0 < log (y : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < y))
  have he : 0 < exp (-eulerMascheroniConstant) := exp_pos _
  have hb := mul_le_mul_of_nonneg_right (hC y hy) (div_pos hly he).le
  rw [Real.norm_eq_abs]
  calc
    |primeProduct y * log y / exp (-eulerMascheroniConstant) - 1| =
        |primeProduct y - exp (-eulerMascheroniConstant) / log y| *
          (log y / exp (-eulerMascheroniConstant)) := by
      rw [← abs_of_pos (div_pos hly he), ← abs_mul]
      congr 1
      field_simp
    _ ≤ C / (log y) ^ 2 * (log y / exp (-eulerMascheroniConstant)) := hb
    _ = C / exp (-eulerMascheroniConstant) / log y := by
      field_simp

/-- Rounding a strict real cutoff does not change its logarithmic main term. -/
theorem tendsto_log_div_localClosedCutoff :
    Tendsto (fun z : ℝ => log z / log (localClosedCutoff z : ℝ)) atTop (𝓝 1) := by
  have hlog : Tendsto (fun z : ℝ => log (localClosedCutoff z : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop.comp tendsto_localClosedCutoff)
  have hupper : Tendsto
      (fun z : ℝ => 1 + log 2 / log (localClosedCutoff z : ℝ)) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add
      (tendsto_const_nhds.div_atTop hlog : Tendsto
        (fun z : ℝ => log 2 / log (localClosedCutoff z : ℝ)) atTop (𝓝 0))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
  · filter_upwards [eventually_ge_atTop 3] with z hz
    have hc := localClosedCutoff_bounds z hz
    have hp : (1 : ℝ) < localClosedCutoff z := by exact_mod_cast (by omega : 1 < localClosedCutoff z)
    exact (one_le_div (log_pos hp)).mpr (log_le_log (by linarith) hc.2.1.le)
  · filter_upwards [eventually_ge_atTop 3] with z hz
    have hc := localClosedCutoff_bounds z hz
    have hp : (1 : ℝ) < localClosedCutoff z := by exact_mod_cast (by omega : 1 < localClosedCutoff z)
    have hmul : z ≤ 2 * (localClosedCutoff z : ℝ) := by linarith [hc.2.2]
    have hl := log_le_log (by linarith : 0 < z) hmul
    rw [log_mul (by norm_num) (by positivity)] at hl
    apply (div_le_iff₀ (log_pos hp)).mpr
    have hlogne := ne_of_gt (log_pos hp)
    field_simp
    nlinarith

theorem tendsto_real_mertens_relative :
    Tendsto (fun z : ℝ =>
      primeProduct (localClosedCutoff z) * log z / exp (-eulerMascheroniConstant))
      atTop (𝓝 1) := by
  have h := (tendsto_mertens_relative.comp tendsto_localClosedCutoff).mul
    tendsto_log_div_localClosedCutoff
  simp only [mul_one] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 3] with z hz
  have hc := (localClosedCutoff_bounds z hz).1
  have hl : log (localClosedCutoff z : ℝ) ≠ 0 :=
    ne_of_gt (log_pos (by exact_mod_cast (by omega : 1 < localClosedCutoff z)))
  dsimp
  field_simp

private theorem abs_mul_sub_one_le {a b η : ℝ} (hη : 0 ≤ η) (hη1 : η ≤ 1)
    (ha : |a - 1| ≤ η) (hb : |b - 1| ≤ η) :
    |a * b - 1| ≤ 3 * η := by
  have ha' := abs_le.mp ha
  have habs : |a| ≤ 1 + η := abs_le.mpr ⟨by linarith, by linarith⟩
  calc
    |a * b - 1| = |a * (b - 1) + (a - 1)| := by congr 1; ring
    _ ≤ |a * (b - 1)| + |a - 1| := abs_add_le _ _
    _ = |a| * |b - 1| + |a - 1| := by rw [abs_mul]
    _ ≤ (1 + η) * η + η :=
      add_le_add (mul_le_mul habs hb (abs_nonneg _) (by linarith)) ha
    _ ≤ 3 * η := by nlinarith

/-- Uniform relative normalization at the literal real cutoff for all even
integers in a fixed polynomial envelope. `B` and `ε` choose one threshold,
before `z` and `M`; the bound does not fix `M` before taking a limit. -/
theorem eventually_localSieveProduct_relative
    (B ε : ℝ) (hB : 0 ≤ B) (hε : 0 < ε) :
    ∀ᶠ z : ℝ in atTop, ∀ M : ℕ, 0 < M → Even M → (M : ℝ) ≤ z ^ B →
      |localSieveProduct M z /
        (2 * exp (-eulerMascheroniConstant) * wuSingularSeries M / log z) - 1| ≤ ε := by
  let η := min 1 (ε / 3)
  have hη : 0 < η := lt_min (by norm_num) (by positivity)
  have hη1 : η ≤ 1 := min_le_left _ _
  have hηε : 3 * η ≤ ε := by have := min_le_right 1 (ε / 3); dsimp [η]; linarith
  have hscalar := tendsto_real_mertens_relative.eventually
    (Metric.ball_mem_nhds 1 hη)
  have htail := eventually_liuTruncated_relative_error_polynomial (2 * B) η hη
  have ht := tendsto_localClosedCutoff.eventually htail
  filter_upwards [hscalar, ht, eventually_ge_atTop 3] with z hs ht hz M hM hEven hpoly
  rw [Real.dist_eq] at hs
  have hc := localClosedCutoff_bounds z hz
  have hcy : (2 : ℝ) ≤ localClosedCutoff z := by exact_mod_cast hc.1
  have hzy : z ≤ (localClosedCutoff z : ℝ) ^ (2 : ℝ) := by
    rw [Real.rpow_two]
    nlinarith [hc.2.2]
  have hpoly' : (M : ℝ) ≤ (localClosedCutoff z : ℝ) ^ (2 * B) := by
    calc
      _ ≤ z ^ B := hpoly
      _ ≤ ((localClosedCutoff z : ℝ) ^ (2 : ℝ)) ^ B :=
        Real.rpow_le_rpow (by linarith) hzy hB
      _ = _ := (Real.rpow_mul (by positivity) 2 B).symm
  have htr := ht M hM hpoly'
  have heq :
      localSieveProduct M z /
          (2 * exp (-eulerMascheroniConstant) * wuSingularSeries M / log z) =
        (primeProduct (localClosedCutoff z) * log z / exp (-eulerMascheroniConstant)) *
          (liuSingularSeriesTruncated M (localClosedCutoff z) / wuSingularSeries M) := by
    rw [localSieveProduct_identity M z hEven hz]
    field_simp
  rw [heq]
  exact (abs_mul_sub_one_le hη.le hη1 hs.le htr).trans hηε

end Wu2008DoubleSieve
