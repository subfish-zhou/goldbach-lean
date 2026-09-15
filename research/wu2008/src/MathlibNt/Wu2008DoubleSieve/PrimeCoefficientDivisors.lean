import MathlibNt.Wu2008DoubleSieve.PrimeCoefficientContinuous
import MathlibNt.Wu2008DoubleSieve.ReboxingPrimeTransport

/-!
# Removing the prime divisors of N from the PNT sum

This is distinct from the repeated-prime lane `p | d` of reboxing.
The actual all-prime carrier is `primeWindow 1`; the deleted terms are
exactly its prime divisors of `N`, with a uniform polynomial-cutoff payment.
-/

namespace Wu2008DoubleSieve

open Finset Set Filter Real
open scoped Classical Topology

theorem primeWindow_all_sub_coprime (N : ℕ) (z w : ℝ) (g : ℕ → ℝ) :
    (∑ p ∈ primeWindow 1 z w, g p) - (∑ p ∈ primeWindow N z w, g p) =
      ∑ p ∈ (primeWindow 1 z w).filter (fun p => p ∣ N), g p := by
  simpa only [Nat.mul_one] using primeWindow_modulus_sum_difference 1 N z w g

/-- An absolute term-sum bound for the actual deleted divisors of `N`.
The coefficient may be signed and need not be continuous or monotone. -/
theorem primeCoefficient_N_divisors_abs_sum_le
    {N : ℕ} {q η B z w : ℝ} {g : ℕ → ℝ}
    (hN : 1 < N) (hη : 0 < η) (hB : 0 ≤ B)
    (hlarge : 4 ≤ (N : ℝ) ^ η) (hq : 1 < q)
    (hz : (N : ℝ) ^ η ≤ z) (hw : w ≤ q ^ (1 / 2 : ℝ))
    (hg : ∀ p ∈ primeWindow 1 z w, |g p| ≤ B) :
    (∑ p ∈ (primeWindow 1 z w).filter (fun p => p ∣ N),
      |g p / (((p : ℝ) - 2) * (1 - log p / log q))|) ≤
        4 * B / (η * (N : ℝ) ^ η) := by
  let P := (primeWindow 1 z w).filter (fun p => p ∣ N)
  have hN0 : 0 < N := by omega
  have hpow : 0 < (N : ℝ) ^ η := rpow_pos_of_pos (by exact_mod_cast hN0) _
  have hsub : P ⊆ largePrimeDivisors N ((N : ℝ) ^ η) := by
    intro p hp
    obtain ⟨hp, hpd⟩ := mem_filter.mp hp
    obtain ⟨hpp, _, hpz, _⟩ := mem_primeWindow.mp hp
    exact mem_largePrimeDivisors.mpr ⟨hpp, hpd, hN0.ne', hz.trans hpz⟩
  have hcardP : (P.card : ℝ) ≤ (largePrimeDivisors N ((N : ℝ) ^ η)).card := by
    exact_mod_cast Finset.card_le_card hsub
  have hcard : (P.card : ℝ) ≤ 1 / η :=
    hcardP.trans (largePrimeDivisors_card_le_inv hN hN0 le_rfl hη)
  calc
    _ ≤ ∑ _p ∈ P, 4 * B / (N : ℝ) ^ η := by
      apply sum_le_sum
      intro p hp
      have hp' := mem_primeWindow.mp (mem_filter.mp hp).1
      have hp4 := hlarge.trans (hz.trans hp'.2.2.1)
      have hpq := hp'.2.2.2.le.trans hw
      have hker := reboxing_prime_weight_le_four_div hq hp4 hpq
      have hinv : 0 ≤ (((p : ℝ) - 2) * (1 - log p / log q))⁻¹ := by
        simpa only [one_div] using hker.1
      rw [div_eq_mul_inv, abs_mul, abs_of_nonneg hinv]
      calc
        _ ≤ B * (1 / (((p : ℝ) - 2) * (1 - log p / log q))) := by
          simpa only [one_div] using
            mul_le_mul_of_nonneg_right (hg p (mem_filter.mp hp).1) hker.1
        _ ≤ B * (4 / (p : ℝ)) := mul_le_mul_of_nonneg_left hker.2 hB
        _ ≤ B * (4 / (N : ℝ) ^ η) := by
          exact mul_le_mul_of_nonneg_left
            (div_le_div_of_nonneg_left (by norm_num) hpow (hz.trans hp'.2.2.1)) hB
        _ = _ := by ring
    _ = (P.card : ℝ) * (4 * B / (N : ℝ) ^ η) := by simp
    _ ≤ (1 / η) * (4 * B / (N : ℝ) ^ η) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by ring

theorem primeCoefficient_all_to_coprime_abs_le
    {N : ℕ} {q η B z w : ℝ} {g : ℕ → ℝ}
    (hN : 1 < N) (hη : 0 < η) (hB : 0 ≤ B)
    (hlarge : 4 ≤ (N : ℝ) ^ η) (hq : 1 < q)
    (hz : (N : ℝ) ^ η ≤ z) (hw : w ≤ q ^ (1 / 2 : ℝ))
    (hg : ∀ p ∈ primeWindow 1 z w, |g p| ≤ B) :
    |(∑ p ∈ primeWindow 1 z w,
        g p / (((p : ℝ) - 2) * (1 - log p / log q))) -
      (∑ p ∈ primeWindow N z w,
        g p / (((p : ℝ) - 2) * (1 - log p / log q)))| ≤
      4 * B / (η * (N : ℝ) ^ η) := by
  rw [primeWindow_all_sub_coprime]
  exact (abs_sum_le_sum_abs _ _).trans
    (primeCoefficient_N_divisors_abs_sum_le hN hη hB hlarge hq hz hw hg)

/-- One threshold precedes the entire class of bounded coefficients,
the scale q, and both real endpoints. This is deletion of p dividing N,
not deletion of p dividing the selected divisor d. -/
theorem primeCoefficient_all_to_coprime_uniform {η B ε : ℝ}
    (hη : 0 < η) (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ T : ℕ, ∀ N : ℕ, T ≤ N → ∀ q z w : ℝ, ∀ g : ℕ → ℝ,
      1 < q → (N : ℝ) ^ η ≤ z → w ≤ q ^ (1 / 2 : ℝ) →
      (∀ p ∈ primeWindow 1 z w, |g p| ≤ B) →
      |(∑ p ∈ primeWindow 1 z w,
          g p / (((p : ℝ) - 2) * (1 - log p / log q))) -
        (∑ p ∈ primeWindow N z w,
          g p / (((p : ℝ) - 2) * (1 - log p / log q)))| ≤ ε := by
  have hgrow : Tendsto (fun N : ℕ => (N : ℝ) ^ η) atTop atTop :=
    (tendsto_rpow_atTop hη).comp tendsto_natCast_atTop_atTop
  have hevent : ∀ᶠ N : ℕ in atTop,
      2 ≤ N ∧ 4 ≤ (N : ℝ) ^ η ∧ 4 * B / (η * ε) ≤ (N : ℝ) ^ η := by
    filter_upwards [eventually_ge_atTop (2 : ℕ),
      hgrow.eventually (eventually_ge_atTop (4 : ℝ)),
      hgrow.eventually (eventually_ge_atTop (4 * B / (η * ε)))] with N hN h4 hεN
    exact ⟨hN, h4, hεN⟩
  obtain ⟨T, hT⟩ := eventually_atTop.mp hevent
  refine ⟨T, ?_⟩
  intro N hN q z w g hq hz hw hg
  obtain ⟨hN2, h4, hεN⟩ := hT N hN
  apply (primeCoefficient_all_to_coprime_abs_le (by omega) hη hB h4 hq hz hw hg).trans
  have hp : 0 < (N : ℝ) ^ η := rpow_pos_of_pos (by exact_mod_cast (show 0 < N by omega)) _
  apply (div_le_iff₀ (mul_pos hη hp)).2
  have := (div_le_iff₀ (mul_pos hη hε)).1 hεN
  nlinarith

/-- The divisor deletion on every actual source fibre, for the actual
depth-k+1 effective coefficient. Its threshold precedes N0, N, the box,
the selected divisor, and both outer parameters. -/
theorem wuEffectiveCoefficient_source_N_divisor_deletion (upper : Bool)
    (k : ℕ) {δ ε : ℝ} (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hε : 0 < ε) :
    ∃ T : ℕ, ∀ N0 : ℕ, T ≤ N0 → ∀ N : ℕ, N0 ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ),
        wuSourceBox k δ N i Δ V → ∀ s t : ℝ, 2 ≤ s → s ≤ t → t ≤ 10 →
      ∀ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
      |(∑ p ∈ primeWindow 1 (wuLocalCutoff N δ d t) (wuLocalCutoff N δ d s),
          wuPrimeCoefficientWeight (wuEffectiveCoefficient upper (k + 1) δ N0)
            ((N : ℝ) ^ (1 / 2 - δ) / d) p) -
        (∑ p ∈ primeWindow N (wuLocalCutoff N δ d t) (wuLocalCutoff N δ d s),
          wuPrimeCoefficientWeight (wuEffectiveCoefficient upper (k + 1) δ N0)
            ((N : ℝ) ^ (1 / 2 - δ) / d) p)| ≤ ε := by
  let η := wuLocalExponent k δ / 10
  have hη : 0 < η := div_pos (wuLocalExponent_pos k hδ hδhi) (by norm_num)
  obtain ⟨T1, hT1⟩ := primeCoefficient_all_to_coprime_uniform hη
    (show (0 : ℝ) ≤ 11 by norm_num) hε
  obtain ⟨T2, hT2⟩ := eventually_atTop.mp
    (wuEffectiveCoefficient_uniform_abs_le_eleven upper (k + 1) (by omega) hδ hδhi)
  refine ⟨max 4 (max T1 T2), ?_⟩
  intro N0 hN0 N hN i Δ V hb s t hs hst ht d hd
  have hN4 : 4 ≤ N := (le_max_left _ _).trans (hN0.trans hN)
  have hT1N : T1 ≤ N :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (hN0.trans hN))
  have hT2N0 : T2 ≤ N0 :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hN0)
  have hgeom := wu_buchstab_prime_window_bounds (show 2 ≤ N by omega)
    hδ hδhi hb hs hst ht hd
  apply hT1 N hT1N _ _ _
    (fun p => wuEffectiveCoefficient upper (k + 1) δ N0
      (log ((N : ℝ) ^ (1 / 2 - δ) / d) / log p - 1))
    hgeom.2.2.1 hgeom.2.2.2.1 hgeom.2.2.2.2
  intro p hp
  obtain ⟨hpp, _, hlow, hhigh⟩ := mem_primeWindow.mp hp
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hpp.one_lt
  have hshift := buchstab_shifted_parameter hgeom.2.2.1 hp1
    (show 0 < s by linarith) (show 0 < t by linarith) hlow hhigh
  have heq :
      log (((N : ℝ) ^ (1 / 2 - δ) / d) / p) / log p =
        log ((N : ℝ) ^ (1 / 2 - δ) / d) / log p - 1 := by
    rw [log_div (by linarith [hgeom.2.2.1]) (by linarith : (p : ℝ) ≠ 0)]
    rw [sub_div, div_self (log_pos hp1).ne']
  rw [heq] at hshift
  exact hT2 N0 hT2N0 _ ⟨by linarith [hshift.1], by linarith [hshift.2]⟩

end Wu2008DoubleSieve
