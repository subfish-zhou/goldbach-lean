import MathlibNt.Wu2008DoubleSieve.Normalization
import MathlibNt.SieveTheory.Arithmetic.MertensTheorem
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The omitted divisor correction in Wu04 (3.10)

Wu (2004), §3, (3.1), (3.10): the integer in the local product is `d * N`,
not `N`. The frozen Mertens theorem retains a truncated singular series.
Here we bound its missing divisor factors without fixing the integer before
the cutoff. All truncations in this file are closed (`p ≤ y`).
-/

namespace Wu2008DoubleSieve

open Finset Real Filter
open MathlibNt.SieveTheory.SingularSeries
open scoped Topology

/-- The inverse correction omitted by a closed prime cutoff. -/
noncomputable def localDivisorTail (M y : ℕ) : ℝ :=
  ∏ p ∈ M.primeFactors.filter (fun p => 2 < p ∧ y < p),
    (1 - 1 / ((p : ℝ) - 1))

private theorem inverse_correction (p : ℕ) (hp : 2 < p) :
    1 - 1 / ((p : ℝ) - 1) = (liuCorrectionFactor p)⁻¹ := by
  have hp' : (2 : ℝ) < p := by exact_mod_cast hp
  unfold liuCorrectionFactor
  field_simp [show (p : ℝ) - 1 ≠ 0 by linarith,
    show (p : ℝ) - 2 ≠ 0 by linarith]
  ring

theorem localDivisorTail_eq_correction_ratio (M y : ℕ) (hM : 0 < M) :
    localDivisorTail M y = liuCorrectionTruncated M y / liuCorrection M := by
  classical
  let S := M.primeFactors.filter (fun p => 2 < p)
  have htr :
      liuCorrectionTruncated M y =
        ∏ p ∈ S.filter (fun p => p ≤ y), liuCorrectionFactor p := by
    unfold liuCorrectionTruncated
    rw [← prod_filter]
    congr 1
    ext p
    simp only [S, mem_filter, mem_range, Nat.mem_primeFactors]
    constructor
    · rintro ⟨⟨hpy, hp, hp2⟩, hpd⟩
      exact ⟨⟨⟨hp, hpd, hM.ne'⟩, hp2⟩, by omega⟩
    · rintro ⟨⟨⟨hp, hpd, _⟩, hp2⟩, hpy⟩
      exact ⟨⟨by omega, hp, hp2⟩, hpd⟩
  have htail :
      localDivisorTail M y =
        (∏ p ∈ S.filter (fun p => ¬p ≤ y), liuCorrectionFactor p)⁻¹ := by
    rw [← prod_inv_distrib]
    unfold localDivisorTail
    have hsets :
        M.primeFactors.filter (fun p => 2 < p ∧ y < p) =
          S.filter (fun p => ¬p ≤ y) := by
      ext p
      simp [S, and_assoc]
    rw [hsets]
    apply prod_congr rfl
    intro p hp
    exact inverse_correction p (mem_filter.mp (mem_filter.mp hp).1).2
  have hfactor :
      liuCorrection M =
        liuCorrectionTruncated M y *
          ∏ p ∈ S.filter (fun p => ¬p ≤ y), liuCorrectionFactor p := by
    rw [htr, prod_filter_mul_prod_filter_not]
    rfl
  rw [htail, hfactor]
  field_simp [ne_of_gt (liuCorrectionTruncated_pos M y)]

private theorem one_sub_prod_le_sum (S : Finset ℕ) (f : ℕ → ℝ)
    (hf : ∀ p ∈ S, 0 ≤ f p ∧ f p ≤ 1) :
    1 - ∏ p ∈ S, (1 - f p) ≤ ∑ p ∈ S, f p := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert p S hp ih =>
    have hp' := hf p (mem_insert_self p S)
    have hf' : ∀ q ∈ S, 0 ≤ f q ∧ f q ≤ 1 :=
      fun q hq => hf q (mem_insert_of_mem hq)
    have hprod : ∏ q ∈ S, (1 - f q) ≤ 1 :=
      prod_le_one (fun q hq => sub_nonneg.mpr (hf' q hq).2)
        (fun q hq => sub_le_self _ (hf' q hq).1)
    rw [prod_insert hp, sum_insert hp]
    have := ih hf'
    nlinarith

theorem localDivisorTail_pos (M y : ℕ) : 0 < localDivisorTail M y := by
  unfold localDivisorTail
  apply prod_pos
  intro p hp
  rw [inverse_correction p (mem_filter.mp hp).2.1]
  exact inv_pos.mpr (liuCorrectionFactor_pos (mem_filter.mp hp).2.1)

theorem localDivisorTail_le_one (M y : ℕ) : localDivisorTail M y ≤ 1 := by
  unfold localDivisorTail
  apply prod_le_one
  · intro p hp
    rw [inverse_correction p (mem_filter.mp hp).2.1]
    exact (inv_pos.mpr (liuCorrectionFactor_pos (mem_filter.mp hp).2.1)).le
  · intro p hp
    have hp' : (2 : ℝ) < p := by exact_mod_cast (mem_filter.mp hp).2.1
    exact sub_le_self _ (div_nonneg zero_le_one (by linarith))

/-- Quantitative loss from all omitted divisor corrections, not a hypothesis
of uniform normalization. No squarefreeness assumption is needed. -/
theorem one_sub_localDivisorTail_le_card (M y : ℕ) (hy : 2 ≤ y) :
    1 - localDivisorTail M y ≤ (M.primeFactors.card : ℝ) / y := by
  classical
  let S := M.primeFactors.filter (fun p => 2 < p ∧ y < p)
  have hpbound (p : ℕ) (hp : p ∈ S) :
      0 ≤ 1 / ((p : ℝ) - 1) ∧ 1 / ((p : ℝ) - 1) ≤ 1 / (y : ℝ) := by
    have hpy : y + 1 ≤ p := (mem_filter.mp hp).2.2
    have hpy' : (y : ℝ) + 1 ≤ p := by exact_mod_cast hpy
    have hy' : (0 : ℝ) < y := by exact_mod_cast (by omega : 0 < y)
    exact ⟨div_nonneg zero_le_one (by linarith),
      one_div_le_one_div_of_le hy' (by linarith)⟩
  calc
    1 - localDivisorTail M y ≤ ∑ p ∈ S, 1 / ((p : ℝ) - 1) := by
      apply one_sub_prod_le_sum
      intro p hp
      refine ⟨(hpbound p hp).1, (hpbound p hp).2.trans ?_⟩
      exact (div_le_one (by positivity : (0 : ℝ) < y)).mpr
        (by exact_mod_cast (by omega : 1 ≤ y))
    _ ≤ ∑ _p ∈ S, 1 / (y : ℝ) :=
      sum_le_sum fun p hp => (hpbound p hp).2
    _ = (S.card : ℝ) / y := by simp [div_eq_mul_inv]
    _ ≤ (M.primeFactors.card : ℝ) / y := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact_mod_cast card_le_card (filter_subset _ _)

/-- The elementary logarithmic cardinality bound is uniform in the integer. -/
theorem primeFactors_card_mul_log_two_le (M : ℕ) (hM : 0 < M) :
    (M.primeFactors.card : ℝ) * log 2 ≤ log M := by
  have hp : 2 ^ M.primeFactors.card ≤ ∏ p ∈ M.primeFactors, p := by
    calc
      _ = ∏ _p ∈ M.primeFactors, 2 := by simp
      _ ≤ _ := prod_le_prod' fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le
  have hpow : (2 : ℝ) ^ M.primeFactors.card ≤ M := by
    exact_mod_cast hp.trans (Nat.le_of_dvd hM (Nat.prod_primeFactors_dvd M))
  have hl := Real.log_le_log (by positivity : (0 : ℝ) < 2 ^ M.primeFactors.card) hpow
  simpa only [Real.log_pow, Nat.cast_commute] using hl

/-- A uniform explicit tail bound: the integer may vary arbitrarily with `y`. -/
theorem one_sub_localDivisorTail_le_log (M y : ℕ) (hM : 0 < M) (hy : 2 ≤ y) :
    1 - localDivisorTail M y ≤ log M / (log 2 * y) := by
  have hcard :
      (M.primeFactors.card : ℝ) ≤ log M / log 2 :=
    (le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr
      (primeFactors_card_mul_log_two_le M hM)
  calc
    _ ≤ (M.primeFactors.card : ℝ) / y := one_sub_localDivisorTail_le_card M y hy
    _ ≤ (log M / log 2) / y := div_le_div_of_nonneg_right hcard (by positivity)
    _ = _ := by ring

/-- The two distinct tails in the relative normalization. -/
theorem liuTruncated_div_wu_eq_tails (M y : ℕ) (hM : 0 < M) :
    liuSingularSeriesTruncated M y / wuSingularSeries M =
      localDivisorTail M y *
        (liuUniversalProductTruncated y / liuUniversalProduct) := by
  rw [wuSingularSeries_eq_liu M hM, liuSingularSeriesTruncated_factorization,
    localDivisorTail_eq_correction_ratio M y hM, liuSingularSeries]
  ring

/-- Lower comparison retaining all large prime divisors of the moving integer. -/
theorem liuTruncated_relative_lower (M y : ℕ) (hM : 0 < M) (hy : 2 ≤ y) :
    1 - log M / (log 2 * y) ≤
      liuSingularSeriesTruncated M y / wuSingularSeries M := by
  have hU : 1 ≤ liuUniversalProductTruncated y / liuUniversalProduct :=
    (one_le_div liuUniversalProduct_pos).mpr (liuUniversalProduct_le_truncated y)
  rw [liuTruncated_div_wu_eq_tails M y hM]
  have htail := one_sub_localDivisorTail_le_log M y hM hy
  have hmul := mul_le_mul_of_nonneg_left hU (localDivisorTail_pos M y).le
  nlinarith

/-- Explicit relative error, uniform in every positive integer `M`. Only the
universal Euler tail chooses the threshold; the omitted divisor correction
is paid by the displayed logarithmic term. -/
theorem eventually_liuTruncated_relative_error (η : ℝ) (hη : 0 < η) :
    ∀ᶠ y : ℕ in atTop, ∀ M : ℕ, 0 < M →
      |liuSingularSeriesTruncated M y / wuSingularSeries M - 1| ≤
        η + log M / (log 2 * y) := by
  filter_upwards [eventually_liuSingularSeriesTruncated_le η hη,
    eventually_ge_atTop 2] with y hu hy M hM
  have hpos := wuSingularSeries_pos M hM
  have hlo := liuTruncated_relative_lower M y hM hy
  have hhi :
      liuSingularSeriesTruncated M y / wuSingularSeries M ≤ 1 + η := by
    apply (div_le_iff₀ hpos).mpr
    simpa only [wuSingularSeries_eq_liu M hM] using hu M hM
  have hlog : 0 ≤ log M :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ M))
  have htail : 0 ≤ log M / (log 2 * y) := by positivity
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- A genuine uniform truncation theorem on any fixed polynomial envelope.
The threshold precedes *both* the cutoff and the positive integer `M`.
The exponent `B` is fixed; no uniformity as `B → ∞` is asserted. -/
theorem eventually_liuTruncated_relative_error_polynomial
    (B ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ y : ℕ in atTop, ∀ M : ℕ, 0 < M → (M : ℝ) ≤ (y : ℝ) ^ B →
      |liuSingularSeriesTruncated M y / wuSingularSeries M - 1| ≤ ε := by
  have hlim : Tendsto (fun y : ℕ => B * log y / (log 2 * y)) atTop (𝓝 0) := by
    have h := (isLittleO_log_rpow_atTop
      (by norm_num : (0 : ℝ) < 1)).tendsto_div_nhds_zero
    have hnat := h.comp tendsto_natCast_atTop_atTop
    have hscaled := hnat.const_mul (B / log 2)
    simpa only [Real.rpow_one, mul_zero] using
      hscaled.congr (fun y => by simp only [Function.comp_apply, Real.rpow_one]; ring)
  have he := hlim.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < ε / 2))
  filter_upwards [eventually_liuTruncated_relative_error (ε / 2) (by linarith),
    he, eventually_ge_atTop 2] with y hrel hsmall hy M hM hpoly
  have hlog : log M ≤ B * log y := by
    have h := Real.log_le_log (by exact_mod_cast hM) hpoly
    rwa [Real.log_rpow (by positivity : (0 : ℝ) < y)] at h
  have hden : 0 ≤ log 2 * (y : ℝ) := by positivity
  have htail := div_le_div_of_nonneg_right hlog hden
  exact (hrel M hM).trans (by linarith)

end Wu2008DoubleSieve
