import MathlibNt.Wu2008DoubleSieve.TruncatedSixthLowerGeometry

/-!
# Arbitrary-product bounded lower sieve on the actual pair carriers

The local product is normalized at N because both selected primes
are at or above the fixed strict cutoff. No square-prefix condition
is imposed on this classical producer.
-/

namespace Wu2008DoubleSieve

open Finset Real
open scoped Classical
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne

theorem truncatedSixthLower_sifted_selected {N p q n : ℕ} {z : ℝ}
    (hp : p.Prime) (hq : q.Prime) (hzp : z ≤ (p : ℝ)) (hzq : z ≤ (q : ℝ)) :
    Sifted ((p * q) * N) n z ↔ Sifted N n z := by
  rw [show (p * q) * N = N * p * q by ring,
    sifted_mul_modulus_of_le hq hzq, sifted_mul_modulus_of_le hp hzp]

theorem truncatedSixthLower_carrier_bridge {N p q : ℕ} {z : ℝ}
    (hp : p.Prime) (hq : q.Prime) (hzp : z ≤ (p : ℝ)) (hzq : z ≤ (q : ℝ)) :
    sourceSieveCarrier N (p * q) ((p * q) * N) z = sieveCarrier N (p * q) N z ∧
      sourceSieveCarrier N (p * q) N z = sieveCarrier N (p * q) N z := by
  constructor
  · rw [sourceSieveCarrier_of_dvd_modulus N (dvd_mul_right (p * q) N)]
    ext r
    simp only [sieveCarrier, mem_filter,
      truncatedSixthLower_sifted_selected hp hq hzp hzq]
  · rw [sourceSieveCarrier_eq_ite, if_pos]
    exact (sifted_mul_iff _ _ _ _).mpr
      ⟨sifted_prime_of_le hp hzp, sifted_prime_of_le hq hzq⟩

theorem truncatedSixthLower_local_product {N p q : ℕ} {z : ℝ}
    (hp : p.Prime) (hq : q.Prime) (hzp : z ≤ (p : ℝ)) (hzq : z ≤ (q : ℝ)) :
    localSieveProduct ((p * q) * N) z = localSieveProduct N z := by
  have he : localSievePrimes ((p * q) * N) z = localSievePrimes N z := by
    ext r
    simp only [mem_localSievePrimes, Nat.coprime_mul_iff_right]
    constructor
    · rintro ⟨hrz, hr, _, hrN⟩
      exact ⟨hrz, hr, hrN⟩
    · rintro ⟨hrz, hr, hrN⟩
      have hrp : r < p := by exact_mod_cast hrz.trans_le hzp
      have hrq : r < q := by exact_mod_cast hrz.trans_le hzq
      exact ⟨hrz, hr, ⟨(Nat.coprime_primes hr hp).mpr (ne_of_lt hrp),
        (Nat.coprime_primes hr hq).mpr (ne_of_lt hrq)⟩, hrN⟩
  simp only [localSieveProduct, he]

theorem truncatedSixthLower_bounded_signed {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ z0 : ℝ, ∀ N d : ℕ, Even N → 2 ≤ N → ∀ z level s : ℝ,
      z0 ≤ z → 2 ≤ z → 0 < level →
      s = log level / log z → 2 ≤ s → s ≤ 10 →
      (logarithmicIntegral N / (Nat.totient d : ℝ)) *
        ((jr1965f s - ρ) * localSieveProduct (d * N) z) +
        ordinaryRosserRemainder false N d (⌊level⌋₊ + 1) z ≤
          (sourceSieveCount N d (d * N) z : ℝ) := by
  obtain ⟨z0, hdensity⟩ := ordinaryRosser_lower_density_canonical_bounded_local hρ
  refine ⟨z0, ?_⟩
  intro N d he hN z level s hz0 hz hlevel hs hs2 hs10
  have hlogz : 0 < log z := log_pos (by linarith)
  have hzlevel : z ≤ level := by
    apply (log_le_log_iff (by linarith : 0 < z) hlevel).mp
    have hratio : 1 ≤ log level / log z := by rw [← hs]; linarith
    simpa only [one_mul] using (le_div_iff₀ hlogz).mp hratio
  have hlevelD : level < (⌊level⌋₊ + 1 : ℕ) := by exact_mod_cast Nat.lt_floor_add_one level
  have hfinite := ordinaryRosser_lower_finite (N := N) (d := d)
    (hzlevel.trans hlevelD.le)
  have hden := hdensity N d he z level s hz0 hz hlevel hs hs2 hs10
  have hX : 0 ≤ logarithmicIntegral N / (Nat.totient d : ℝ) :=
    div_nonneg (MathlibNt.SieveTheory.LiuWeight.liuLogarithmicIntegral_nonneg 0
      (by norm_num) (by exact_mod_cast hN)) (Nat.cast_nonneg _)
  have hmain := mul_le_mul_of_nonneg_left hden hX
  linarith

theorem truncatedSixthLower_pair_signed {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ z0 : ℝ, ∀ N p q : ℕ, Even N → 2 ≤ N →
      p.Prime → q.Prime → ∀ z level s : ℝ,
      z ≤ (p : ℝ) → z ≤ (q : ℝ) → z0 ≤ z → 2 ≤ z → 0 < level →
      s = log level / log z → 2 ≤ s → s ≤ 10 →
      (logarithmicIntegral N / (Nat.totient (p * q) : ℝ)) *
        ((jr1965f s - ρ) * localSieveProduct N z) +
        ordinaryRosserRemainder false N (p * q) (⌊level⌋₊ + 1) z ≤
          (sieveCount N (p * q) N z : ℝ) := by
  obtain ⟨z0, h⟩ := truncatedSixthLower_bounded_signed hρ
  refine ⟨z0, ?_⟩
  intro N p q he hN hp hq z level s hzp hzq hz0 hz hlevel hs hs2 hs10
  have hb := h N (p * q) he hN z level s hz0 hz hlevel hs hs2 hs10
  rw [truncatedSixthLower_local_product hp hq hzp hzq] at hb
  simpa only [sourceSieveCount, sieveCount,
    (truncatedSixthLower_carrier_bridge hp hq hzp hzq).1] using hb

end Wu2008DoubleSieve
