import MathlibNt.Wu2008DoubleSieve.RosserSieveConsumer
import MathlibNt.Wu2008DoubleSieve.LocalProductReal
import MathlibNt.SieveTheory.Arithmetic.MertensTheorem
import MathlibNt.SieveTheory.LinearSieve.JurkatRichert.JurkatRichert1965Section13HatSource
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiUpperRosserDensityEndpointDirect

/-!
# Uniform upper Rosser density for the actual Goldbach local factors

The frozen dimension-one producer is instantiated, rather than assumed.
Its threshold precedes every even `N`, selected divisor `d`, real cutoff
and real level. The exact main sum is the one in the finite sieve consumer.
The full uniform producer applies for `3/2 <= s <= 4`; its base branch is
also stated with the canonical constructed `jr1965F` on `3/2 <= s <= 3`.
-/

namespace Wu2008DoubleSieve

open Finset
open scoped Classical
open AnalyticNumberTheory.Sieve
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418
open MathlibNt.SieveTheory
open MathlibNt.SieveTheory.LinearSieve
open MathlibNt.SieveTheory.SwitchingPrinciple
open MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne

theorem ordinarySievePrimeProduct_primeFactors (M : ℕ) (z : ℝ) :
    (ordinarySievePrimeProduct M z).primeFactors = primeWindow M 0 z :=
  Nat.primeFactors_prod (fun _p hp => (mem_primeWindow.mp hp).1)

theorem ordinarySievePrimeProduct_prime_gt_two {M p : ℕ} (he : Even M)
    (z : ℝ) (hp : p.Prime) (hd : p ∣ ordinarySievePrimeProduct M z) : 2 < p := by
  have hc := (ordinarySievePrimeProduct_coprime M z).of_dvd_left hd
  have hn : ¬p ∣ M := hp.coprime_iff_not_dvd.mp hc
  have hne : p ≠ 2 := by
    intro h
    subst p
    exact hn (even_iff_two_dvd.mp he)
  have := hp.two_le
  omega

private theorem even_selected_modulus (N d : ℕ) (he : Even N) : Even (d * N) := by
  obtain ⟨k, hk⟩ := he
  exact ⟨d * k, by rw [hk, mul_add]⟩

/-- An actual finite Goldbach sieve, not a density hypothesis record.
The complement map is injective on the prime-index carrier. -/
noncomputable def ordinaryGoldbachBoundingSieve (N d : ℕ) (he : Even N)
    (z : ℝ) : BoundingSieve where
  support := (goldbachDivisible N d).image (fun p => N - p)
  prodPrimes := ordinarySievePrimeProduct (d * N) z
  prodPrimes_squarefree := ordinarySievePrimeProduct_squarefree _ _
  weights := fun _ => 1
  weights_nonneg := fun _ => zero_le_one
  totalMass := AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418.logarithmicIntegral N /
    (Nat.totient d : ℝ)
  nu := goldbachNu
  nu_mult := goldbachNu_isMultiplicative
  nu_pos_of_prime := fun _ hp _ => goldbachNu_pos_of_prime hp
  nu_lt_one_of_prime := fun _ hp hd => goldbachNu_lt_one_of_prime hp
    (ordinarySievePrimeProduct_prime_gt_two (even_selected_modulus N d he) z hp hd)

theorem ordinaryGoldbach_mainSum_eq (N d D : ℕ) (he : Even N) (z : ℝ) :
    (ordinaryGoldbachBoundingSieve N d he z).mainSum
      (upperRosserWeight (ordinaryGoldbachBoundingSieve N d he z).prodPrimes D) =
        ordinaryRosserMainSum true N d D z := by
  unfold BoundingSieve.mainSum ordinaryRosserMainSum
  change (∑ q ∈ (ordinarySievePrimeProduct (d * N) z).divisors,
      upperRosserWeight _ D q * goldbachNu q) = _
  apply sum_congr rfl
  intro q hq
  rw [goldbachNu_squarefree_eq_inv_totient
    ((ordinarySievePrimeProduct_squarefree _ _).squarefree_of_dvd
      (Nat.mem_divisors.mp hq).1)]
  simp only [ordinaryRosserWeight, if_true, div_eq_mul_inv, one_mul]
  rfl

theorem ordinaryGoldbach_sieveProduct_eq (N d : ℕ) (he : Even N) (z : ℝ) :
    sieveProductPrimeFactors (ordinaryGoldbachBoundingSieve N d he z) =
      ∏ p ∈ primeWindow (d * N) 0 z, (1 - 1 / ((p : ℝ) - 1)) := by
  change (∏ p ∈ (ordinarySievePrimeProduct (d * N) z).primeFactors,
    (1 - goldbachNu p)) = _
  rw [ordinarySievePrimeProduct_primeFactors]
  apply prod_congr rfl
  intro p hp
  rw [goldbachNu_apply_prime (mem_primeWindow.mp hp).1]

theorem localSievePrimes_eq_primeWindow (M : ℕ) (z : ℝ) :
    localSievePrimes M z = primeWindow M 0 z := by
  ext p
  rw [mem_localSievePrimes, mem_primeWindow]
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  tauto

/-- The actual density record's Euler product is exactly the product in
the uniform Wu04 (3.10) producer, not merely an asymptotic proxy. -/
theorem ordinaryGoldbach_sieveProduct_eq_local (N d : ℕ) (he : Even N) (z : ℝ) :
    sieveProductPrimeFactors (ordinaryGoldbachBoundingSieve N d he z) =
      localSieveProduct (d * N) z := by
  rw [ordinaryGoldbach_sieveProduct_eq, localSieveProduct,
    localSievePrimes_eq_primeWindow]

/-- One fixed dimension constant works for every actual selected modulus. -/
theorem ordinaryGoldbach_uniform_dimension_one :
    ∃ K : ℝ, 1 < K ∧ ∀ N d : ℕ, ∀ he : Even N, ∀ z : ℝ,
      HasDimensionOneLocalProductBound (ordinaryGoldbachBoundingSieve N d he z) K := by
  obtain ⟨K, hK, hinterval⟩ := MertensTheorem.exists_goldbach_inverse_interval_bound
  refine ⟨K, hK, ?_⟩
  intro N d he z z1 z2 hz1 hz12
  let S : Finset ℕ := ((ordinarySievePrimeProduct (d * N) z).primeFactors).filter
    (fun p : ℕ => z1 ≤ (p : ℝ) ∧ (p : ℝ) < z2)
  have hprime : ∀ p ∈ S, p.Prime ∧ 2 < p := by
    intro p hp
    have hp' := (mem_filter.mp hp).1
    have hpp := Nat.prime_of_mem_primeFactors hp'
    exact ⟨hpp, ordinarySievePrimeProduct_prime_gt_two (even_selected_modulus N d he)
      z hpp (Nat.dvd_of_mem_primeFactors hp')⟩
  have hbound := hinterval S hprime z1 z2 hz1 hz12 (fun _p hp => (mem_filter.mp hp).2)
  change (∏ p ∈ S, (1 - goldbachNu p)⁻¹) ≤ _
  convert hbound using 1
  apply prod_congr rfl
  intro p hp
  rw [goldbachNu_apply_prime (hprime p hp).1]

/-- Actual uniform upper density. The relative error multiplies the actual
Euler product, not a fixed absolute constant or the wrong singular series. -/
theorem ordinaryRosser_upper_density_uniform {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ z0 : ℝ, ∀ N d : ℕ, ∀ _he : Even N, ∀ z level s : ℝ,
      z0 ≤ z → 2 ≤ z → 0 < level →
      s = Real.log level / Real.log z → 3 / 2 ≤ s → s ≤ 4 →
      ordinaryRosserMainSum true N d (⌊level⌋₊ + 1) z ≤
        (jurkatRichertUpperLinearSieveFactor s + ρ) *
          ∏ p ∈ primeWindow (d * N) 0 z, (1 - 1 / ((p : ℝ) - 1)) := by
  have hfund : DimensionOneUpperRosserDensityFundamentalLemma :=
    dimensionOneUpperRosserDensityFundamentalLemma_of_suzuki_allDepth
      jr1965Section13HatLayers jr1965Section13HatSourceContract
      (show SuzukiClaim145SourceParameters (16 : ℝ) (1 / 2 : ℝ) (7 : ℝ) by
        constructor <;> norm_num)
  obtain ⟨K, hK, hdim⟩ := ordinaryGoldbach_uniform_dimension_one
  obtain ⟨z0, hbound⟩ := hfund K ρ hK hρ
  refine ⟨z0, ?_⟩
  intro N d he z level s hz0 hz hlevel hs hslo hshi
  have hcut : ∀ p ∈ (ordinaryGoldbachBoundingSieve N d he z).prodPrimes.primeFactors,
      (p : ℝ) ≤ z := by
    change ∀ p ∈ (ordinarySievePrimeProduct (d * N) z).primeFactors, (p : ℝ) ≤ z
    rw [ordinarySievePrimeProduct_primeFactors]
    exact fun _p hp => (mem_primeWindow.mp hp).2.2.2.le
  have h := hbound (ordinaryGoldbachBoundingSieve N d he z) z level s hz0 hz hlevel
    (hdim N d he z) hcut hs hslo hshi
  rw [ordinaryGoldbach_mainSum_eq, ordinaryGoldbach_sieveProduct_eq] at h
  exact h

/-- Canonical constructed `F`, on its constant-weight base branch. No
legacy placeholder function is substituted for the delay-equation solution. -/
theorem ordinaryRosser_upper_density_canonical {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ z0 : ℝ, ∀ N d : ℕ, ∀ _he : Even N, ∀ z level s : ℝ,
      z0 ≤ z → 2 ≤ z → 0 < level →
      s = Real.log level / Real.log z → 3 / 2 ≤ s → s ≤ 3 →
      ordinaryRosserMainSum true N d (⌊level⌋₊ + 1) z ≤
        (jr1965F s + ρ) *
          ∏ p ∈ primeWindow (d * N) 0 z, (1 - 1 / ((p : ℝ) - 1)) := by
  obtain ⟨z0, hbound⟩ := ordinaryRosser_upper_density_uniform hρ
  refine ⟨z0, ?_⟩
  intro N d he z level s hz0 hz hlevel hs hslo hshi
  have h := hbound N d he z level s hz0 hz hlevel hs hslo (by linarith)
  simpa only [jr1965F_eq_of_le_three hshi, jurkatRichertUpperLinearSieveFactor,
    if_pos hshi] using h

/-- A genuine upper sieve estimate for the actual unscaled source, with
canonical `F` and the literal ordinary AP remainder. -/
theorem ordinarySieve_upper_canonical_with_AP_error {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ z0 : ℝ, ∀ N d Q : ℕ, ∀ _he : Even N, 2 ≤ N → ∀ z level s : ℝ,
      z0 ≤ z → 2 ≤ z → 0 < level →
      s = Real.log level / Real.log z → 3 / 2 ≤ s → s ≤ 3 →
      ⌊level⌋₊ + 1 ≤ Q / d + 1 →
      (sourceSieveCount N d (d * N) z : ℝ) ≤
        (AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418.logarithmicIntegral N /
          (Nat.totient d : ℝ)) *
          ((jr1965F s + ρ) *
            ∏ p ∈ primeWindow (d * N) 0 z, (1 - 1 / ((p : ℝ) - 1))) +
          ∑ q ∈ (Icc 1 (Q / d)).filter (fun q => q.Coprime (d * N)),
            |primeAPError N (d * q) N| := by
  obtain ⟨z0, hdensity⟩ := ordinaryRosser_upper_density_canonical hρ
  refine ⟨z0, ?_⟩
  intro N d Q he hN z level s hz0 hz hl hs hslo hshi hD
  have hlogz : 0 < Real.log z := Real.log_pos (by linarith)
  have hs1 : 1 ≤ Real.log level / Real.log z := by rw [← hs]; linarith
  have hloglevel : Real.log z ≤ Real.log level := by
    simpa only [one_mul] using (le_div_iff₀ hlogz).mp hs1
  have hzlevel : z ≤ level := (Real.log_le_log_iff (by linarith) hl).mp hloglevel
  have hlevelD : level < (⌊level⌋₊ + 1 : ℕ) := by
    exact_mod_cast Nat.lt_floor_add_one level
  have hzD : z ≤ (⌊level⌋₊ + 1 : ℕ) := hzlevel.trans hlevelD.le
  have hD1 : 1 < ⌊level⌋₊ + 1 := by
    have hD2 : (2 : ℝ) ≤ (⌊level⌋₊ + 1 : ℕ) := hz.trans hzD
    exact_mod_cast (show (1 : ℝ) < (⌊level⌋₊ + 1 : ℕ) by linarith)
  have hfinite := ordinaryRosser_upper_finite (N := N) (d := d) hD1 hzD
  have hden := hdensity N d he z level s hz0 hz hl hs hslo hshi
  have hX : 0 ≤
      AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418.logarithmicIntegral N /
        (Nat.totient d : ℝ) :=
    div_nonneg (LiuWeight.liuLogarithmicIntegral_nonneg 0 (by norm_num)
      (by exact_mod_cast hN)) (Nat.cast_nonneg _)
  have hmain := mul_le_mul_of_nonneg_left hden hX
  have herr := ordinaryRosserRemainder_le_AP (upper := true) (N := N) (d := d)
    (Q := Q) z hD
  have habs := le_abs_self (ordinaryRosserRemainder true N d (⌊level⌋₊ + 1) z)
  linarith

end Wu2008DoubleSieve
