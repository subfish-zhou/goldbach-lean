import MathlibNt.SieveTheory.LiLiuGoldbachClosedLowerBound

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
noncomputable local instance instDecidableGoldbachBadBound (P : Prop) : Decidable P :=
  Classical.propDecidable P

/-- An actual noncoprime difference N-p comes from a prime divisor of N.
No coprimality or parity exception is removed from the original carrier. -/
theorem goldbachBadCount_le_primeFactors (N : ℕ) (ε : ℝ) (hN : N ≠ 0) :
    goldbachBadCount (goldbachDifferenceCarrier N ε) N ≤ (N.primeFactors.card : ℤ) := by
  have hsub : ((goldbachDifferenceCarrier N ε).filter fun n => ¬Nat.Coprime n N) ⊆
      N.primeFactors.image (fun p => N - p) := by
    intro n hn
    obtain ⟨hnA,hnBad⟩ := Finset.mem_filter.mp hn
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hnA
    obtain ⟨hpRange,hpPrime,hpcut⟩ := Finset.mem_filter.mp hp
    have hpN : p ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp hpRange)
    have hnot : ¬Nat.Coprime p N := fun h => hnBad ((Nat.coprime_self_sub_left hpN).mpr h)
    have hdiv : p ∣ N := by
      by_contra h
      exact hnot (hpPrime.coprime_iff_not_dvd.mpr h)
    exact Finset.mem_image.mpr ⟨p,Nat.mem_primeFactors.mpr ⟨hpPrime,hdiv,hN⟩,rfl⟩
  have hc := (Finset.card_le_card hsub).trans (Finset.card_image_le)
  unfold goldbachBadCount
  exact_mod_cast hc

/-- At most one distinct prime divisor lies above the integer square root. -/
theorem goldbach_primeFactors_card_le_sqrt_add_one (N : ℕ) (hN : N ≠ 0) :
    N.primeFactors.card ≤ N.sqrt + 1 := by
  let S := N.primeFactors.filter (fun p => p ≤ N.sqrt)
  let L := N.primeFactors.filter (fun p => ¬p ≤ N.sqrt)
  have hS : S.card ≤ N.sqrt := by
    have hsub : S ⊆ Finset.Icc 1 N.sqrt := by
      intro p hp
      obtain ⟨hpf,hps⟩ := Finset.mem_filter.mp hp
      have hpPrime := (Nat.mem_primeFactors.mp hpf).1
      exact Finset.mem_Icc.mpr ⟨hpPrime.one_lt.le,hps⟩
    simpa using Finset.card_le_card hsub
  have hL : L.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro p hp q hq
    obtain ⟨hpf,hps⟩ := Finset.mem_filter.mp hp
    obtain ⟨hqf,hqs⟩ := Finset.mem_filter.mp hq
    obtain ⟨hpPrime,hpd,_⟩ := Nat.mem_primeFactors.mp hpf
    obtain ⟨hqPrime,hqd,_⟩ := Nat.mem_primeFactors.mp hqf
    by_contra hne
    have hcop : Nat.Coprime p q := (Nat.coprime_primes hpPrime hqPrime).mpr hne
    have hpq : p*q ≤ N := Nat.le_of_dvd (Nat.pos_of_ne_zero hN)
      (hcop.mul_dvd_of_dvd_of_dvd hpd hqd)
    have hsq : N < (N.sqrt+1)*(N.sqrt+1) := Nat.sqrt_lt.mp (Nat.lt_succ_self _)
    have hmul : (N.sqrt+1)*(N.sqrt+1) ≤ p*q :=
      Nat.mul_le_mul (by omega) (by omega)
    omega
  have hsum : S.card + L.card = N.primeFactors.card := by
    simpa only [Finset.sum_const, smul_eq_mul, mul_one] using
      (Finset.sum_filter_add_sum_filter_not N.primeFactors (fun p => p ≤ N.sqrt)
        (fun _ => (1 : ℕ)))
  omega

/-- The exact bad-set contribution is paid uniformly whenever z²≤N.
This finite estimate requires no analytic distribution theorem. -/
theorem goldbachBadCount_twice_le_four_div (N : ℕ) (ε z : ℝ)
    (hN : 1 ≤ N) (hz : 0 < z) (hzN : z^2 ≤ (N : ℝ)) :
    ((2 * goldbachBadCount (goldbachDifferenceCarrier N ε) N : ℤ) : ℝ) ≤
      4 * (N : ℝ) / z := by
  have hN0 : N ≠ 0 := by omega
  have hX : goldbachBadCount (goldbachDifferenceCarrier N ε) N ≤
      ((N.sqrt + 1 : ℕ) : ℤ) :=
    (goldbachBadCount_le_primeFactors N ε hN0).trans
      (by exact_mod_cast goldbach_primeFactors_card_le_sqrt_add_one N hN0)
  have hXR : (goldbachBadCount (goldbachDifferenceCarrier N ε) N : ℝ) ≤
      (N.sqrt : ℝ)+1 := by exact_mod_cast hX
  have hs1 : 1 ≤ N.sqrt := by
    rw [Nat.le_sqrt]
    omega
  have hs1R : (1 : ℝ) ≤ N.sqrt := by exact_mod_cast hs1
  have hs2 : (N.sqrt : ℝ)^2 ≤ N := by exact_mod_cast Nat.sqrt_le' N
  have hsz : (N.sqrt : ℝ)*z ≤ N := by nlinarith [sq_nonneg ((N.sqrt : ℝ)-z)]
  have hmul := mul_le_mul_of_nonneg_right hXR hz.le
  apply (le_div_iff₀ hz).mpr
  push_cast
  nlinarith

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig