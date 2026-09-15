import MathlibNt.Wu2008DoubleSieve.S3CarrierMajorant
import MathlibNt.Wu2008DoubleSieve.Omega3XIntegralDomain

/-!
# Fourth-row Gamma16: three distinct actual carriers

The raw source modulus is d*N. The prefix modulus exempts the two
selected primes below the strict third-prime cutoff. Only directed
comparisons identify their roles; the raw carrier is not redefined.
-/

namespace Wu2008DoubleSieve

open Finset
open scoped Classical

noncomputable def gamma16Alpha : ℝ := 100 / 291
noncomputable def gamma16Beta : ℝ := 2 / 5

abbrev Gamma16Tuple := Fin 4 → ℕ

def gamma16Product (p : Gamma16Tuple) : ℕ := p 0 * p 1 * p 2 * p 3

noncomputable def gamma16Tuples (N : ℕ) (δ : ℝ) (d : ℕ) : Finset Gamma16Tuple :=
  (Fintype.piFinset (fun _ : Fin 4 =>
    primeWindow N (wuLocalCutoff N δ d (291 / 100)) (wuLocalCutoff N δ d (5 / 2)))).filter
      (fun p => p 0 < p 1 ∧ p 1 < p 2 ∧ p 2 < p 3 ∧ ∀ j, p j ≤ N)

theorem mem_gamma16Tuples {N d : ℕ} {δ : ℝ} {p : Gamma16Tuple} :
    p ∈ gamma16Tuples N δ d ↔
      (∀ j, (p j).Prime ∧ (p j).Coprime N ∧
        wuLocalCutoff N δ d (291 / 100) ≤ (p j : ℝ) ∧
        (p j : ℝ) < wuLocalCutoff N δ d (5 / 2)) ∧
      p 0 < p 1 ∧ p 1 < p 2 ∧ p 2 < p 3 ∧ ∀ j, p j ≤ N := by
  simp only [gamma16Tuples, mem_filter, Fintype.mem_piFinset, mem_primeWindow]

noncomputable def gamma16RawCarrier (N d : ℕ) (p : Gamma16Tuple) : Finset ℕ :=
  sourceSieveCarrier N (d * gamma16Product p) (d * N) (p 2)

noncomputable def gamma16QuotientCarrier (N d : ℕ) (p : Gamma16Tuple) : Finset ℕ :=
  sieveCarrier N (d * gamma16Product p) (d * N) (p 2)

noncomputable def gamma16PrefixCarrier (N d : ℕ) (p : Gamma16Tuple) : Finset ℕ :=
  sourceSieveCarrier N (d * gamma16Product p) (d * p 0 * p 1 * N) (p 2)

theorem gamma16_prefix_carrier_eq {N d : ℕ} {p : Gamma16Tuple}
    (h2 : (p 2).Prime) (h3 : (p 3).Prime) (h23 : p 2 ≤ p 3) :
    gamma16PrefixCarrier N d p =
      sieveCarrier N (d * gamma16Product p) (d * p 0 * p 1 * N) (p 2) := by
  simpa only [gamma16PrefixCarrier, gamma16Product, mul_assoc, mul_left_comm, mul_comm]
    using source_strict_triple_carrier (N := N) (a := d * p 0 * p 1) h2 h3 h23

theorem gamma16_raw_subset_quotient (N d : ℕ) (p : Gamma16Tuple) :
    gamma16RawCarrier N d p ⊆ gamma16QuotientCarrier N d p := by
  unfold gamma16RawCarrier gamma16QuotientCarrier
  rw [sourceSieveCarrier_eq_ite]
  split_ifs
  · exact Subset.rfl
  · exact empty_subset _

theorem gamma16_quotient_subset_prefix {N d : ℕ} {p : Gamma16Tuple}
    (h2 : (p 2).Prime) (h3 : (p 3).Prime) (h23 : p 2 ≤ p 3) :
    gamma16QuotientCarrier N d p ⊆ gamma16PrefixCarrier N d p := by
  rw [gamma16_prefix_carrier_eq h2 h3 h23]
  simpa only [gamma16QuotientCarrier, mul_assoc, mul_left_comm, mul_comm] using
    sieveCarrier_subset_mul_modulus N (d * gamma16Product p) (d * N) (p 0 * p 1) (p 2)

theorem gamma16_forced_small_primes {N d : ℕ} {δ : ℝ} {p : Gamma16Tuple}
    (hp : p ∈ gamma16Tuples N δ d) :
    Sifted (d * N) (d * gamma16Product p) (p 2) ↔ p 0 ∣ d ∧ p 1 ∣ d := by
  obtain ⟨h, h01, h12, h23, _⟩ := mem_gamma16Tuples.mp hp
  constructor
  · intro hs
    have forced (j : Fin 4) (hj : p j < p 2) (hdiv : p j ∣ d * gamma16Product p) :
        p j ∣ d := by
      by_contra hn
      exact hs (p j) (h j).1
        (((h j).1.coprime_iff_not_dvd.mpr hn).mul_right (h j).2.1)
        (by exact_mod_cast hj) hdiv
    exact ⟨forced 0 (h01.trans h12) ⟨p 1 * p 2 * p 3 * d, by
      simp only [gamma16Product]; ring⟩,
      forced 1 h12 ⟨p 0 * p 2 * p 3 * d, by
        simp only [gamma16Product]; ring⟩⟩
  · rintro ⟨h0, h1⟩
    have hd : Sifted (d * N) d (p 2) := fun q hq hc hz =>
      siftedLE_of_dvd_modulus (dvd_mul_right d N) _ q hq hc hz.le
    have hs (j : Fin 4) (hj : p j ∣ d) : Sifted (d * N) (p j) (p 2) :=
      fun q hq hc hz => siftedLE_of_dvd_modulus
        (hj.trans (dvd_mul_right d N)) _ q hq hc hz.le
    simp only [gamma16Product, sifted_mul_iff]
    exact ⟨hd, ⟨⟨hs 0 h0, hs 1 h1⟩, sifted_prime_of_le (h 2).1 le_rfl⟩,
      sifted_prime_of_le (h 3).1 (by exact_mod_cast h23.le)⟩

theorem gamma16_raw_carrier_ite {N d : ℕ} {δ : ℝ} {p : Gamma16Tuple}
    (hp : p ∈ gamma16Tuples N δ d) :
    gamma16RawCarrier N d p =
      if p 0 ∣ d ∧ p 1 ∣ d then gamma16QuotientCarrier N d p else ∅ := by
  rw [gamma16RawCarrier, sourceSieveCarrier_eq_ite, gamma16_forced_small_primes hp]
  by_cases h : p 0 ∣ d ∧ p 1 ∣ d <;> simp [h, gamma16QuotientCarrier]

noncomputable def gamma16RawSum {i : ℕ} (N : ℕ) (δ : ℝ)
    (W : Fin i → Finset ℕ) : ℝ :=
  ∑ d ∈ boxConvolutionSupport W, (convolutionCoeff W d : ℝ) *
    ∑ p ∈ gamma16Tuples N δ d,
      (sourceSieveCount N (d * gamma16Product p) (d * N) (p 2) : ℝ)

noncomputable def gamma16QuotientSum {i : ℕ} (N : ℕ) (δ : ℝ)
    (W : Fin i → Finset ℕ) : ℝ :=
  ∑ d ∈ boxConvolutionSupport W, (convolutionCoeff W d : ℝ) *
    ∑ p ∈ gamma16Tuples N δ d,
      (sieveCount N (d * gamma16Product p) (d * N) (p 2) : ℝ)

noncomputable def gamma16PrefixSum {i : ℕ} (N : ℕ) (δ : ℝ)
    (W : Fin i → Finset ℕ) : ℝ :=
  ∑ d ∈ boxConvolutionSupport W, (convolutionCoeff W d : ℝ) *
    ∑ p ∈ gamma16Tuples N δ d,
      (sourceSieveCount N (d * gamma16Product p) (d * p 0 * p 1 * N) (p 2) : ℝ)

theorem gamma16_directed_sums {i : ℕ} (N : ℕ) (δ : ℝ) (W : Fin i → Finset ℕ) :
    gamma16RawSum N δ W ≤ gamma16QuotientSum N δ W ∧
      gamma16QuotientSum N δ W ≤ gamma16PrefixSum N δ W := by
  constructor
  · apply sum_le_sum
    intro d _
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    apply sum_le_sum
    intro p _
    have hc := card_le_card (gamma16_raw_subset_quotient N d p)
    simpa only [sourceSieveCount, sieveCount, gamma16RawCarrier, gamma16QuotientCarrier,
      Int.cast_natCast, Nat.cast_le] using (Nat.cast_le.mpr hc : (↑_ : ℝ) ≤ ↑_)
  · apply sum_le_sum
    intro d _
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    apply sum_le_sum
    intro p hp
    obtain ⟨h, _, _, h23, _⟩ := mem_gamma16Tuples.mp hp
    have hc := card_le_card (gamma16_quotient_subset_prefix (N := N) (d := d)
      (h 2).1 (h 3).1 h23.le)
    simpa only [sourceSieveCount, sieveCount, gamma16PrefixCarrier, gamma16QuotientCarrier,
      Int.cast_natCast, Nat.cast_le] using (Nat.cast_le.mpr hc : (↑_ : ℝ) ≤ ↑_)

noncomputable def gamma16RawLabels {i : ℕ} (N : ℕ) (δ : ℝ)
    (W : Fin i → Finset ℕ) :
    Finset (Σ _ : Fin i → ℕ, Σ _ : Gamma16Tuple, ℕ) :=
  (Fintype.piFinset W).sigma fun t =>
    (gamma16Tuples N δ (∏ j, t j)).sigma (gamma16RawCarrier N (∏ j, t j))

theorem gamma16_raw_natural_card {i : ℕ} (N : ℕ) (δ : ℝ) (W : Fin i → Finset ℕ) :
    (Nat.card {a // a ∈ gamma16RawLabels N δ W} : ℝ) = gamma16RawSum N δ W := by
  rw [Nat.card_eq_fintype_card, Fintype.card_coe]
  simp only [gamma16RawLabels, card_sigma, Nat.cast_sum, gamma16RawSum,
    boxConvolution_sum_fibres, sourceSieveCount, gamma16RawCarrier, Int.cast_natCast]

end Wu2008DoubleSieve
