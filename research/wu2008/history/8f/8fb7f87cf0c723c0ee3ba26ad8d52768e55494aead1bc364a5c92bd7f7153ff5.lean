import MathlibNt.Wu2008DoubleSieve.VariableS3

/-!
# Prime cofactors at the actual ninth-term moving cutoff

Wu (2008), section 5, sends the ninth term to a prime-cofactor switching
count. This is a direct arithmetic interface for the existing quotient
carrier, not an identification with a differently truncated source count.
The prime-index-dividing-N and repeated-first-prime exceptions are explicit.
-/

namespace Wu2008DoubleSieve
open Finset

 theorem ninth_cofactor_one_or_prime {N a b r : ℕ}
    (hN : 4 ≤ N) (he : Even N) (ha : a.Prime) (hb : b.Prime)
    (hr : r ∈ sieveCarrier N (a * b) (N * a)
      (Real.sqrt ((N : ℝ) / ((a : ℝ) * b))))
    (hrN : ¬ r ∣ N) (ha2 : ¬ a ^ 2 ∣ N - r) :
    (N - r) / (a * b) = 1 ∨ ((N - r) / (a * b)).Prime := by
  classical
  obtain ⟨hrange, hrp, hd, hs⟩ := mem_filter.mp hr
  have hrle : r ≤ N := by have := mem_range.mp hrange; omega
  have hn : 0 < N - r := complement_pos_of_even hN he hrle hrp
  have hab : 0 < a * b := Nat.mul_pos ha.pos hb.pos
  have hm : 0 < (N - r) / (a * b) := Nat.div_pos (Nat.le_of_dvd hn hd) hab
  by_cases hm1 : (N - r) / (a * b) = 1
  · exact Or.inl hm1
  right
  by_contra hnp
  let q := ((N - r) / (a * b)).minFac
  have hqp : q.Prime := Nat.minFac_prime hm1
  have hqd : q ∣ (N - r) / (a * b) := Nat.minFac_dvd _
  have hqn : q ∣ N - r := by
    rw [← Nat.mul_div_cancel' hd]
    exact hqd.trans (dvd_mul_left _ _)
  have hqN : ¬ q ∣ N := by
    intro h
    have hqr : q ∣ r := by
      have hsub := Nat.dvd_sub h hqn
      simpa only [Nat.sub_sub_self hrle] using hsub
    rcases (Nat.dvd_prime hrp).mp hqr with h1 | heq
    · exact hqp.ne_one h1
    · exact hrN (heq ▸ h)
  have hqa : q ≠ a := by
    intro h
    have had : a ∣ (N - r) / (a * b) := h ▸ hqd
    obtain ⟨k, hk⟩ := had
    apply ha2
    refine ⟨b * k, ?_⟩
    rw [← Nat.mul_div_cancel' hd, hk]
    ring
  have hcop : q.Coprime (N * a) := Nat.coprime_mul_iff_right.mpr
    ⟨(hqp.coprime_iff_not_dvd).mpr hqN, (Nat.coprime_primes hqp ha).mpr hqa⟩
  have hq2 : (q : ℝ) ^ 2 ≤ ((N - r) / (a * b) : ℕ) := by
    exact_mod_cast Nat.minFac_sq_le_self hm hnp
  have habR : 0 < (a : ℝ) * b := by exact_mod_cast hab
  have hmul : ((a : ℝ) * b) * ((N - r) / (a * b) : ℕ) = (N - r : ℕ) := by
    exact_mod_cast Nat.mul_div_cancel' hd
  have hnlt : ((N - r : ℕ) : ℝ) < N := by
    exact_mod_cast Nat.sub_lt (by omega : 0 < N) hrp.pos
  have hmY : (((N - r) / (a * b) : ℕ) : ℝ) < (N : ℝ) / ((a : ℝ) * b) := by
    apply (lt_div_iff₀ habR).mpr
    nlinarith
  have hqY : (q : ℝ) < Real.sqrt ((N : ℝ) / ((a : ℝ) * b)) := by
    have hy := Real.sq_sqrt (div_nonneg (Nat.cast_nonneg N) habR.le)
    have hy0 := Real.sqrt_nonneg ((N : ℝ) / ((a : ℝ) * b))
    by_contra h
    have hle := le_of_not_gt h
    nlinarith [(Nat.cast_nonneg q : (0 : ℝ) ≤ q)]
  exact hs q hqp hcop hqY hqd

/-- On the actual final parameter range, a cofactor below the switching
cutoff forces the whole complement into a power-saving initial interval.
This also pays the unit cofactor without identifying two sieve counts. -/
theorem ninth_small_cofactor_complement_le {N a b c : ℕ} {κ : ℝ}
    (hN : 1 < N) (hκ : 1 / 14 ≤ κ)
    (hpair : a * b ^ 2 < N)
    (ha : (a : ℝ) < (N : ℝ) ^ (1 / 2 - 3 * κ))
    (hc : (c : ℝ) < (N : ℝ) ^ (1 / 2 - 3 * κ)) :
    (a : ℝ) * b * c ≤ (N : ℝ) ^ (1 - κ) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hu : 0 ≤ (N : ℝ) ^ (1 / 2 - 3 * κ) := Real.rpow_nonneg hN0.le _
  have hc2 : (c : ℝ) ^ 2 ≤ ((N : ℝ) ^ (1 / 2 - 3 * κ)) ^ 2 :=
    (sq_le_sq₀ (Nat.cast_nonneg c) hu).mpr hc.le
  have hac : (a : ℝ) * c ^ 2 ≤ ((N : ℝ) ^ (1 / 2 - 3 * κ)) ^ 3 := by
    calc
      (a : ℝ) * c ^ 2 ≤ (N : ℝ) ^ (1 / 2 - 3 * κ) *
          ((N : ℝ) ^ (1 / 2 - 3 * κ)) ^ 2 :=
        mul_le_mul ha.le hc2 (sq_nonneg _) hu
      _ = _ := by ring
  have hp : (a : ℝ) * b ^ 2 ≤ N := by exact_mod_cast hpair.le
  have hprod : ((a : ℝ) * b * c) ^ 2 ≤
      (N : ℝ) * ((N : ℝ) ^ (1 / 2 - 3 * κ)) ^ 3 := by
    calc
      ((a : ℝ) * b * c) ^ 2 = ((a : ℝ) * c ^ 2) * ((a : ℝ) * b ^ 2) := by ring
      _ ≤ ((N : ℝ) ^ (1 / 2 - 3 * κ)) ^ 3 * N :=
        mul_le_mul hac hp (by positivity) (by positivity)
      _ = _ := by ring
  have hpow : (N : ℝ) * ((N : ℝ) ^ (1 / 2 - 3 * κ)) ^ 3 ≤
      ((N : ℝ) ^ (1 - κ)) ^ 2 := by
    calc
      (N : ℝ) * ((N : ℝ) ^ (1 / 2 - 3 * κ)) ^ 3 =
          (N : ℝ) ^ (1 + (1 / 2 - 3 * κ) * 3) := by
        rw [Real.rpow_add hN0, Real.rpow_one, Real.rpow_mul hN0.le]
        norm_num
      _ ≤ (N : ℝ) ^ ((1 - κ) * 2) :=
        Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
      _ = ((N : ℝ) ^ (1 - κ)) ^ 2 := by
        rw [Real.rpow_mul hN0.le]
        norm_num
  exact (sq_le_sq₀ (by positivity) (Real.rpow_nonneg hN0.le _)).mp
    (hprod.trans hpow)

end Wu2008DoubleSieve
