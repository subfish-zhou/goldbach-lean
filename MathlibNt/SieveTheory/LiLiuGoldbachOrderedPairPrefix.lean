import MathlibNt.SieveTheory.LiLiuGoldbachS3Carrier

open scoped BigOperators
open Finset

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

open BombieriVinogradov

/-- A prime at or above the sieve threshold cannot divide a small sieve divisor. -/
theorem goldbachOrderedPair_prime_not_dvd_small
    {N p d : ℕ} {z : ℝ} (hp : p.Prime) (hzp : z ≤ (p : ℝ))
    (hd : d ∣ goldbachS1ProdPrimes N z) : ¬ p ∣ d := by
  intro hpd
  have hpz := ((prime_dvd_goldbachS1ProdPrimes_iff hp).mp (hpd.trans hd)).1
  exact (not_lt_of_ge hzp) hpz

/-- Ordered pairs of primes above the sieve threshold, together with a small
sieve divisor, are uniquely determined by their product. Repeated primes are allowed. -/
theorem goldbachOrderedPair_mul_injective
    {N r s r' s' d e : ℕ} {z : ℝ}
    (hr : r.Prime) (hs : s.Prime) (hrs : r ≤ s) (hzr : z ≤ (r : ℝ))
    (hr' : r'.Prime) (hs' : s'.Prime) (hrs' : r' ≤ s') (hzr' : z ≤ (r' : ℝ))
    (hd : d ∣ goldbachS1ProdPrimes N z)
    (he : e ∣ goldbachS1ProdPrimes N z)
    (heq : r * s * d = r' * s' * e) : r = r' ∧ s = s' ∧ d = e := by
  have hre : ¬ r ∣ e := goldbachOrderedPair_prime_not_dvd_small hr hzr he
  have hr'd : ¬ r' ∣ d := goldbachOrderedPair_prime_not_dvd_small hr' hzr' hd
  have hrrs : r ∣ r' * s' := by
    apply (hr.dvd_mul.mp (show r ∣ r' * s' * e from
      heq ▸ (dvd_mul_right r s).trans (dvd_mul_right (r * s) d))).resolve_right hre
  have hr'rs : r' ∣ r * s := by
    apply (hr'.dvd_mul.mp (show r' ∣ r * s * d from
      heq.symm ▸ (dvd_mul_right r' s').trans (dvd_mul_right (r' * s') e))).resolve_right hr'd
  have hle : r' ≤ r := by
    rcases hr.dvd_mul.mp hrrs with h | h
    · exact le_of_eq (((Nat.dvd_prime hr').mp h).resolve_left hr.ne_one).symm
    · have hh : r = s' := ((Nat.dvd_prime hs').mp h).resolve_left hr.ne_one
      exact hh.symm ▸ hrs'
  have hle' : r ≤ r' := by
    rcases hr'.dvd_mul.mp hr'rs with h | h
    · exact le_of_eq (((Nat.dvd_prime hr).mp h).resolve_left hr'.ne_one).symm
    · have hh : r' = s := ((Nat.dvd_prime hs).mp h).resolve_left hr'.ne_one
      exact hh.symm ▸ hrs
  have hrr' : r = r' := le_antisymm hle' hle
  subst r'
  have hsd : s * d = s' * e := Nat.eq_of_mul_eq_mul_left hr.pos (by
    simpa only [mul_assoc] using heq)
  have hse : ¬ s ∣ e := goldbachOrderedPair_prime_not_dvd_small hs
    (hzr.trans (by exact_mod_cast hrs)) he
  have hss' : s = s' := ((Nat.dvd_prime hs').mp
    ((hs.dvd_mul.mp (show s ∣ s' * e from hsd ▸ dvd_mul_right s d)).resolve_right hse)).resolve_left hs.ne_one
  subst s'
  exact ⟨rfl, rfl, Nat.eq_of_mul_eq_mul_left hs.pos hsd⟩

/-- The whole ordered-pair prefix error sum injects once into the ordinary full
modulus prefix sum. There is no multiplicity factor, coprimality condition on
`N`, strict-pair condition, or additional upper cutoff. -/
theorem goldbachOrderedPair_prefix_doubleSum_le
    (N Q : ℕ) (z : ℝ) (T : Finset (ℕ × ℕ))
    (hT : ∀ a ∈ T, a.1.Prime ∧ a.2.Prime ∧ a.1 ≤ a.2 ∧ z ≤ (a.1 : ℝ)) :
    (∑ a ∈ T,
      ∑ d ∈ (goldbachS1ProdPrimes N z).divisors.filter
        (fun d => d < Q / (a.1 * a.2) + 1),
        standardPrimeAPPrefixMaxError N (a.1 * a.2 * d)) ≤
      ∑ k ∈ Icc 1 Q, standardPrimeAPPrefixMaxError N k := by
  classical
  let ds := fun a : ℕ × ℕ => (goldbachS1ProdPrimes N z).divisors.filter
    (fun d => d < Q / (a.1 * a.2) + 1)
  let S := T.sigma ds
  let f := fun a : (a : ℕ × ℕ) × ℕ => a.1.1 * a.1.2 * a.2
  have hinj : Set.InjOn f S := by
    rintro ⟨⟨r, s⟩, d⟩ hrd ⟨⟨r', s'⟩, e⟩ hre heq
    rcases Finset.mem_sigma.mp hrd with ⟨ha, hd⟩
    rcases Finset.mem_sigma.mp hre with ⟨hb, he⟩
    rcases hT _ ha with ⟨hr, hs, hrs, hzr⟩
    rcases hT _ hb with ⟨hr', hs', hrs', hzr'⟩
    have hdvd := (Nat.mem_divisors.mp (Finset.mem_filter.mp hd).1).1
    have hevd := (Nat.mem_divisors.mp (Finset.mem_filter.mp he).1).1
    obtain ⟨rfl, rfl, rfl⟩ := goldbachOrderedPair_mul_injective
      hr hs hrs hzr hr' hs' hrs' hzr' hdvd hevd heq
    rfl
  have hsub : S.image f ⊆ Icc 1 Q := by
    intro k hk
    rcases Finset.mem_image.mp hk with ⟨⟨⟨r, s⟩, d⟩, had, rfl⟩
    rcases Finset.mem_sigma.mp had with ⟨ha, hd⟩
    rcases Finset.mem_filter.mp hd with ⟨hdv, hdl⟩
    change d < Q / (r * s) + 1 at hdl
    rcases hT _ ha with ⟨hr, hs, _, _⟩
    have hrs0 : 0 < r * s := Nat.mul_pos hr.pos hs.pos
    have hd0 := Nat.pos_of_mem_divisors hdv
    have hdle : d ≤ Q / (r * s) := by omega
    have hmul : r * s * d ≤ Q := by
      simpa [mul_comm] using (Nat.le_div_iff_mul_le hrs0).mp hdle
    exact Finset.mem_Icc.mpr ⟨Nat.succ_le_of_lt (Nat.mul_pos hrs0 hd0), hmul⟩
  calc
    (∑ a ∈ T, ∑ d ∈ ds a, standardPrimeAPPrefixMaxError N (a.1 * a.2 * d)) =
        ∑ k ∈ S.image f, standardPrimeAPPrefixMaxError N k := by
      rw [Finset.sum_sigma', Finset.sum_image hinj]
    _ ≤ ∑ k ∈ Icc 1 Q, standardPrimeAPPrefixMaxError N k :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun k _ _ => standardPrimeAPPrefixMaxError_nonneg N k)

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
