import MathlibNt.Wu2008DoubleSieve.TruncatedSixthLowerCoefficients
import MathlibNt.Wu2008DoubleSieve.PrimeOrderedQuadratureWeighted
import MathlibNt.Wu2008DoubleSieve.PrimeCoefficientDivisors

/-!
# Reciprocal mass of the actual coprime prime windows

The fixed lower exponent is arbitrary and positive. The Mertens
discrepancy, the two endpoint atoms, and the prime divisors of N are
paid uniformly before both exponent endpoints.
-/

namespace Wu2008DoubleSieve

open Finset Set Real Filter MeasureTheory LiLiuPrereqBuchstab
open scoped Classical Topology

noncomputable def truncatedSixthMassPrimeSum (N : ℕ) (a b : ℝ) : ℝ :=
  ∑ p ∈ primeWindow N ((N : ℝ) ^ a) ((N : ℝ) ^ b), 1 / (p : ℝ)

theorem truncatedSixthMass_divisor_deletion {N : ℕ} {κ z w M : ℝ}
    (hN : 1 < N) (hκ : 0 < κ) (hM : 0 ≤ M)
    (hz : (N : ℝ) ^ κ ≤ z) (g : ℕ → ℝ)
    (hg : ∀ p ∈ primeWindow 1 z w, |g p| ≤ M / p) :
    |(∑ p ∈ primeWindow 1 z w, g p) - ∑ p ∈ primeWindow N z w, g p| ≤
      M / (κ * (N : ℝ) ^ κ) := by
  rw [primeWindow_all_sub_coprime]
  let P := (primeWindow 1 z w).filter (fun p => p ∣ N)
  have hpow : 0 < (N : ℝ) ^ κ :=
    rpow_pos_of_pos (by exact_mod_cast (show 0 < N by omega)) _
  have hsub : P ⊆ largePrimeDivisors N ((N : ℝ) ^ κ) := by
    intro p hp
    obtain ⟨hp, hd⟩ := mem_filter.mp hp
    obtain ⟨hp, _, hpz, _⟩ := mem_primeWindow.mp hp
    exact mem_largePrimeDivisors.mpr ⟨hp, hd, by omega, hz.trans hpz⟩
  have hcard : (P.card : ℝ) ≤ 1 / κ :=
    (show (P.card : ℝ) ≤ (largePrimeDivisors N ((N : ℝ) ^ κ)).card by
      exact_mod_cast Finset.card_le_card hsub).trans
        (largePrimeDivisors_card_le_inv hN (by omega) le_rfl hκ)
  calc
    _ ≤ ∑ p ∈ P, |g p| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _p ∈ P, M / (N : ℝ) ^ κ := by
      apply sum_le_sum
      intro p hp
      have hp' := (mem_filter.mp hp).1
      exact (hg p hp').trans (div_le_div_of_nonneg_left hM hpow
        (hz.trans (mem_primeWindow.mp hp').2.2.1))
    _ = (P.card : ℝ) * (M / (N : ℝ) ^ κ) := by simp
    _ ≤ (1 / κ) * (M / (N : ℝ) ^ κ) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by ring

theorem truncatedSixthMass_closed_endpoint {z w M : ℝ}
    (hz : 0 < z) (hzw : z ≤ w) (hM : 0 ≤ M) (g : ℕ → ℝ)
    (hg : ∀ p ∈ primesIcc z w, |g p| ≤ M / p) :
    |(∑ p ∈ primesIcc z w, g p) - ∑ p ∈ primeWindow 1 z w, g p| ≤ M / z := by
  have hsub : primeWindow 1 z w ⊆ primesIcc z w := by
    intro p hp
    obtain ⟨hp, _, hlo, hhi⟩ := mem_primeWindow.mp hp
    exact (mem_primesIcc (hz.le.trans hzw)).mpr ⟨hp, hlo, hhi.le⟩
  let E := primesIcc z w \ primeWindow 1 z w
  have hsingle : E ⊆ {⌊w⌋₊} := by
    intro p hp
    obtain ⟨hp, hn⟩ := mem_sdiff.mp hp
    obtain ⟨hpp, hlo, hhi⟩ := (mem_primesIcc (hz.le.trans hzw)).mp hp
    have he : (p : ℝ) = w := by
      by_contra hne
      exact hn (mem_primeWindow.mpr ⟨hpp, Nat.coprime_one_right p, hlo, hhi.lt_of_ne hne⟩)
    simp only [Finset.mem_singleton]
    rw [← he, Nat.floor_natCast]
  have hcard : E.card ≤ 1 := by
    simpa using Finset.card_le_card hsingle
  rw [← sum_sdiff hsub, add_sub_cancel_right]
  calc
    _ ≤ ∑ p ∈ E, |g p| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _p ∈ E, M / z := by
      apply sum_le_sum
      intro p hp
      have hp' := (mem_sdiff.mp hp).1
      exact (hg p hp').trans (div_le_div_of_nonneg_left hM hz
        ((mem_primesIcc (hz.le.trans hzw)).mp hp').2.1)
    _ = (E.card : ℝ) * (M / z) := by simp
    _ ≤ 1 * (M / z) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
    _ = _ := one_mul _

noncomputable def truncatedSixthMassPrimeError (N : ℕ) (κ : ℝ) : ℝ :=
  (2 * primeOrderedMertensConstant / κ) / log N +
    (2 + 1 / κ) / (N : ℝ) ^ κ

theorem truncatedSixthMass_prime_error_tendsto {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (fun N => truncatedSixthMassPrimeError N κ) atTop (𝓝 0) := by
  have hl := tendsto_const_nhds.div_atTop
    (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
    (a := 2 * primeOrderedMertensConstant / κ)
  have hp := tendsto_const_nhds.div_atTop
    ((tendsto_rpow_atTop hκ).comp tendsto_natCast_atTop_atTop)
    (a := 2 + 1 / κ)
  simpa [truncatedSixthMassPrimeError] using hl.add hp

theorem truncatedSixthMass_prime_discrepancy {N : ℕ} {κ a b : ℝ}
    (hN : 1 < N) (hκ : 0 < κ)
    (hstart : primeOrderedMertensStart ≤ (N : ℝ) ^ κ)
    (ha : κ ≤ a) (hab : a ≤ b) :
    |truncatedSixthMassPrimeSum N a b - log (b / a)| ≤
      truncatedSixthMassPrimeError N κ := by
  have hNR : (1 : ℝ) < N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hlog := log_pos hNR
  have ha0 := hκ.trans_le ha
  have hb0 := ha0.trans_le hab
  have hz := rpow_pos_of_pos hN0 a
  have hlow := rpow_le_rpow_of_exponent_le hNR.le ha
  have hpow := rpow_pos_of_pos hN0 κ
  have hzw := rpow_le_rpow_of_exponent_le hNR.le hab
  have hioc := primeOrdered_reciprocal_discrepancy (hstart.trans hlow) hzw
  rw [primeOrdered_exponent_density_integral hNR ha0 hab,
    integral_one_div_of_pos ha0 hb0] at hioc
  have hioc' : |(∑ p ∈ primesIoc ((N : ℝ) ^ a) ((N : ℝ) ^ b), 1 / (p : ℝ)) -
      log (b / a)| ≤ (2 * primeOrderedMertensConstant / κ) / log N := by
    apply hioc.trans
    rw [log_rpow hN0]
    calc
      _ ≤ 2 * primeOrderedMertensConstant / (κ * log N) :=
        div_le_div_of_nonneg_left (by positivity [primeOrderedMertensConstant_pos])
          (mul_pos hκ hlog) (mul_le_mul_of_nonneg_right ha hlog.le)
      _ = _ := by ring
  have hiocc : |(∑ p ∈ primesIcc ((N : ℝ) ^ a) ((N : ℝ) ^ b), 1 / (p : ℝ)) -
      (∑ p ∈ primesIoc ((N : ℝ) ^ a) ((N : ℝ) ^ b), 1 / (p : ℝ))| ≤
      1 / (N : ℝ) ^ κ := by
    rw [sum_primesIcc_eq_sum_primesIoc_add (hz.le.trans hzw) (fun x : ℝ => 1 / x)]
    simp only [add_sub_cancel_left]
    split_ifs
    · rw [abs_of_pos (one_div_pos.mpr hz)]
      exact one_div_le_one_div_of_le hpow hlow
    · simpa using (one_div_pos.mpr hpow).le
  have hend := truncatedSixthMass_closed_endpoint hz hzw (by norm_num : (0 : ℝ) ≤ 1)
    (fun p => 1 / (p : ℝ)) (fun p _ => by simp)
  have hdel := truncatedSixthMass_divisor_deletion (w := (N : ℝ) ^ b)
    hN hκ (by norm_num : (0 : ℝ) ≤ 1)
    hlow (fun p => 1 / (p : ℝ))
    (fun p _ => by simp)
  have hend' := hend.trans (one_div_le_one_div_of_le hpow hlow)
  have htri := abs_sub_le
    (∑ p ∈ primeWindow N ((N : ℝ) ^ a) ((N : ℝ) ^ b), 1 / (p : ℝ))
    (∑ p ∈ primeWindow 1 ((N : ℝ) ^ a) ((N : ℝ) ^ b), 1 / (p : ℝ))
    (log (b / a))
  have htri2 := abs_sub_le
    (∑ p ∈ primeWindow 1 ((N : ℝ) ^ a) ((N : ℝ) ^ b), 1 / (p : ℝ))
    (∑ p ∈ primesIcc ((N : ℝ) ^ a) ((N : ℝ) ^ b), 1 / (p : ℝ))
    (log (b / a))
  have htri3 := abs_sub_le
    (∑ p ∈ primesIcc ((N : ℝ) ^ a) ((N : ℝ) ^ b), 1 / (p : ℝ))
    (∑ p ∈ primesIoc ((N : ℝ) ^ a) ((N : ℝ) ^ b), 1 / (p : ℝ))
    (log (b / a))
  rw [abs_sub_comm] at hdel hend'
  unfold truncatedSixthMassPrimeSum truncatedSixthMassPrimeError
  have he : 1 / (κ * (N : ℝ) ^ κ) + 1 / (N : ℝ) ^ κ + 1 / (N : ℝ) ^ κ =
      (2 + 1 / κ) / (N : ℝ) ^ κ := by ring
  linarith

theorem truncatedSixthMass_prime_uniform {κ ε : ℝ} (hκ : 0 < κ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ a b : ℝ, κ ≤ a → a ≤ b →
      |truncatedSixthMassPrimeSum N a b - log (b / a)| < ε := by
  have hs := ((tendsto_rpow_atTop hκ).comp tendsto_natCast_atTop_atTop).eventually
    (eventually_ge_atTop primeOrderedMertensStart)
  have he := (truncatedSixthMass_prime_error_tendsto hκ).eventually (gt_mem_nhds hε)
  filter_upwards [hs, he, eventually_ge_atTop (2 : ℕ)] with N hs he hN a b ha hab
  exact (truncatedSixthMass_prime_discrepancy (by omega) hκ hs ha hab).trans_lt he

theorem truncatedSixthMass_prime_tendsto {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    Tendsto (fun N => truncatedSixthMassPrimeSum N a b) atTop (𝓝 (log (b / a))) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨T, hT⟩ := eventually_atTop.mp (truncatedSixthMass_prime_uniform ha hε)
  exact ⟨T, fun N hN => by simpa [Real.dist_eq] using hT N hN a b le_rfl hab⟩

theorem truncatedSixthMass_rectangle_tendsto {a b c d : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hc : 0 < c) (hcd : c ≤ d) :
    Tendsto (fun N : ℕ =>
      ∑ t ∈ primeWindow N ((N : ℝ) ^ a) ((N : ℝ) ^ b) ×ˢ
        primeWindow N ((N : ℝ) ^ c) ((N : ℝ) ^ d),
          1 / ((t.1 : ℝ) * t.2)) atTop (𝓝 (log (b / a) * log (d / c))) := by
  have he (N : ℕ) : (∑ t ∈ primeWindow N ((N : ℝ) ^ a) ((N : ℝ) ^ b) ×ˢ
      primeWindow N ((N : ℝ) ^ c) ((N : ℝ) ^ d), 1 / ((t.1 : ℝ) * t.2)) =
      truncatedSixthMassPrimeSum N a b * truncatedSixthMassPrimeSum N c d := by
    simp only [truncatedSixthMassPrimeSum, sum_product, sum_mul, mul_sum, one_div_mul_one_div]
    exact sum_comm
  simp_rw [he]
  exact (truncatedSixthMass_prime_tendsto ha hab).mul (truncatedSixthMass_prime_tendsto hc hcd)

end Wu2008DoubleSieve
