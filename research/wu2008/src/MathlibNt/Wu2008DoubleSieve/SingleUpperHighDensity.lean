import MathlibNt.Wu2008DoubleSieve.SingleUpperCounts

namespace Wu2008DoubleSieve.SingleUpperCounts
open Finset Real Filter
open scoped Classical Topology
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne

/-- Removing a prime at or above the strict cutoff does not alter the Euler product. -/
theorem primeWindow_selected_modulus {N p : ℕ} {z : ℝ}
    (hp : p.Prime) (hz : z ≤ (p : ℝ)) :
    primeWindow (p * N) 0 z = primeWindow N 0 z := by
  ext q
  simp only [mem_primeWindow]
  constructor
  · rintro ⟨hq, hc, hq0, hqz⟩
    exact ⟨hq, (Nat.coprime_mul_iff_right.mp hc).2, hq0, hqz⟩
  · rintro ⟨hq, hc, hq0, hqz⟩
    refine ⟨hq, Nat.coprime_mul_iff_right.mpr ⟨?_, hc⟩, hq0, hqz⟩
    exact (Nat.coprime_primes hq hp).mpr (by
      intro he
      subst q
      exact (not_lt_of_ge hz) hqz)

theorem localProduct_selected_modulus {N p : ℕ} {z : ℝ}
    (hp : p.Prime) (hz : z ≤ (p : ℝ)) :
    localSieveProduct (p*N) z = localSieveProduct N z := by
  simp only [localSieveProduct, localSievePrimes_eq_primeWindow,
    primeWindow_selected_modulus hp hz]

/-- The level ratio is the original moving s, not a constant initial-branch proxy. -/
theorem prime_s_exact {N p : ℕ} {δ : ℝ} (hN : 2 ≤ N) (hp : 0 < p) :
    log ((N : ℝ)^(1/2-δ)/(p : ℝ)) /
        log ((N : ℝ)^truncatedSixthLowerAlpha) =
      ((1/2-δ)-log (p : ℝ)/log (N : ℝ))/truncatedSixthLowerAlpha := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hlog : log (N : ℝ) ≠ 0 := (log_pos (by exact_mod_cast hN)).ne'
  have ha : truncatedSixthLowerAlpha ≠ 0 := by norm_num [truncatedSixthLowerAlpha]
  rw [log_div (rpow_pos_of_pos hN0 _).ne' hp0.ne', log_rpow hN0, log_rpow hN0]
  field_simp

/-- The high-prime segment fits the actually proved canonical density range.
No density extension is inferred merely from a delay-factor identity. -/
theorem high_prime_s_bounds {N p : ℕ} {δ r : ℝ}
    (hN : 2 ≤ N) (hδ : 0 ≤ δ) (hδhi : δ ≤ 1/100) (hr : r ≤ 1/3)
    (hp : p ∈ primeWindow N ((N : ℝ)^truncatedSixthLowerAlpha) ((N : ℝ)^r))
    (hhigh : (N : ℝ)^((1/2-δ)/2) ≤ (p : ℝ)) :
    3/2 ≤ ((1/2-δ)-log (p : ℝ)/log (N : ℝ))/truncatedSixthLowerAlpha ∧
      ((1/2-δ)-log (p : ℝ)/log (N : ℝ))/truncatedSixthLowerAlpha ≤ 4 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (mem_primeWindow.mp hp).1.pos
  have hlog : 0 < log (N : ℝ) := log_pos (by exact_mod_cast hN)
  have ha : 0 < truncatedSixthLowerAlpha := by norm_num [truncatedSixthLowerAlpha]
  have hup : log (p : ℝ)/log (N : ℝ) ≤ r := by
    apply (div_le_iff₀ hlog).mpr
    have h := log_le_log hp0 (mem_primeWindow.mp hp).2.2.2.le
    rwa [log_rpow hN0] at h
  have hlo : (1/2-δ)/2 ≤ log (p : ℝ)/log (N : ℝ) := by
    apply (le_div_iff₀ hlog).mpr
    have h := log_le_log (rpow_pos_of_pos hN0 _) hhigh
    rwa [log_rpow hN0] at h
  constructor
  · apply (le_div_iff₀ ha).mpr
    norm_num [truncatedSixthLowerAlpha] at *
    linarith
  · apply (div_le_iff₀ ha).mpr
    norm_num [truncatedSixthLowerAlpha] at *
    linarith

/-- Actual high-prime Rosser density, uniformly before N,p,r. The selected
prime is removed exactly from the local product, not asymptotically. -/
theorem high_prime_density {δ ρ : ℝ}
    (hδ : 0 ≤ δ) (hδhi : δ ≤ 1/100) (hρ : 0 < ρ) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ r : ℝ, r ≤ 1/3 →
      ∀ p ∈ primeWindow N ((N : ℝ)^truncatedSixthLowerAlpha) ((N : ℝ)^r),
        (N : ℝ)^((1/2-δ)/2) ≤ (p : ℝ) →
        ordinaryRosserMainSum true N p (wuVariableRosserLevel N δ p)
            ((N : ℝ)^truncatedSixthLowerAlpha) ≤
          (jr1965F (((1/2-δ)-log (p : ℝ)/log (N : ℝ))/truncatedSixthLowerAlpha)+ρ) *
            localSieveProduct N ((N : ℝ)^truncatedSixthLowerAlpha) := by
  obtain ⟨Z, hZ⟩ := ordinaryRosser_upper_density_canonical_extended_local hρ
  have ha : 0 < truncatedSixthLowerAlpha := by norm_num [truncatedSixthLowerAlpha]
  have ht : Tendsto (fun N : ℕ => (N : ℝ)^truncatedSixthLowerAlpha) atTop atTop :=
    (tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop
  obtain ⟨T, hT⟩ := eventually_atTop.mp (ht.eventually (eventually_ge_atTop (max Z 2)))
  refine ⟨max 4 T, le_max_left _ _, ?_⟩
  intro N hN he r hr p hp hhigh
  have hN4 : 4 ≤ N := (le_max_left _ _).trans hN
  have hz := hT N ((le_max_right _ _).trans hN)
  have hp0 := (mem_primeWindow.mp hp).1.pos
  have hs := high_prime_s_bounds (by omega) hδ hδhi hr hp hhigh
  have hlevel : 0 < (N : ℝ)^(1/2-δ)/(p : ℝ) := by positivity
  have hb := hZ N p he ((N : ℝ)^truncatedSixthLowerAlpha)
    ((N : ℝ)^(1/2-δ)/(p : ℝ))
    (((1/2-δ)-log (p : ℝ)/log (N : ℝ))/truncatedSixthLowerAlpha)
    ((le_max_left _ _).trans hz) ((le_max_right _ _).trans hz)
    hlevel (prime_s_exact (by omega) hp0).symm hs.1 hs.2
  rw [localProduct_selected_modulus (mem_primeWindow.mp hp).1 (mem_primeWindow.mp hp).2.2.1] at hb
  exact hb

end Wu2008DoubleSieve.SingleUpperCounts
