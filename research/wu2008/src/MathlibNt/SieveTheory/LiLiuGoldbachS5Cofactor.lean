import MathlibNt.SieveTheory.LiLiuGoldbachS4SwitchedCarrier

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- A cofactor in the large-second-prime S5 region is prime, unless the
exempted first prime occurs a second time. The square exception is retained. -/
theorem goldbachS5_cofactor_prime_or_square
    {N n r s : ℕ} (hr : r.Prime) (_hs : s.Prime)
    (hcop : Nat.Coprime n N) (hn : n < N) (hlarge : r * s < n)
    (hsecond : N ≤ s ^ 3)
    (hpoint : literalHPoint (N * r) (r * s) (s : ℝ) n) :
    (n / (r * s)).Prime ∨ r ^ 2 ∣ n := by
  let q := n / (r * s)
  have hf : n = r * s * q := (Nat.mul_div_cancel' hpoint.1).symm
  have hq2 : 2 ≤ q := by
    by_contra h
    have hq1 : q ≤ 1 := by omega
    have hm := Nat.mul_le_mul_left (r * s) hq1
    rw [Nat.mul_one] at hm
    omega
  by_cases hd : r ∣ q
  · right
    obtain ⟨k, hk⟩ := hd
    refine ⟨s * k, ?_⟩
    rw [hf, hk]
    ring
  · left
    change q.Prime
    by_contra hp
    have hl : q.minFac.Prime := Nat.minFac_prime (by omega)
    have hld : q.minFac ∣ q := Nat.minFac_dvd q
    have hln : q.minFac ∣ n := by
      rw [hf]
      exact dvd_mul_of_dvd_right hld _
    have hnotN : ¬q.minFac ∣ N := prime_not_dvd_of_coprime hcop hl hln
    have hne : q.minFac ≠ r := fun he => hd (he ▸ hld)
    have hnotr : ¬q.minFac ∣ r :=
      fun h => hne ((Nat.prime_dvd_prime_iff_eq hl hr).mp h)
    have hnot : ¬q.minFac ∣ N * r :=
      fun h => (hl.dvd_mul.mp h).elim hnotN hnotr
    have hsl : s ≤ q.minFac := by exact_mod_cast hpoint.2 q.minFac hl hln hnot
    have hsq : q.minFac ^ 2 ≤ q := Nat.minFac_sq_le_self (by omega) hp
    have hq : s ^ 2 ≤ q := (Nat.pow_le_pow_left hsl 2).trans hsq
    have hNn : N ≤ n := by
      calc
        N ≤ r * N := Nat.le_mul_of_pos_left N hr.pos
        _ ≤ r * s ^ 3 := Nat.mul_le_mul_left r hsecond
        _ = (r * s) * s ^ 2 := by ring
        _ ≤ (r * s) * q := Nat.mul_le_mul_left _ hq
        _ = n := hf.symm
    omega

/-- Specialization to the literal closed S5 pair filter and original difference carrier.
The cutoff inequality is a scalar threshold, not a primality premise. -/
theorem goldbachS5Closed_cofactor_prime_or_square
    {N n : ℕ} {ε : ℝ} {rs : ℕ × ℕ} (hN : 2 ≤ N) (hε : 0 < ε)
    (hcut : (N : ℝ) ^ (2 / 3 : ℝ) ≤ ε * N)
    (hrs : rs ∈ (goldbachS4Pairs N ((N : ℝ) ^ (4 / 53 : ℝ))).filter
      (fun rs => (rs.1 : ℝ) ≤ (N : ℝ) ^ (1 / 3 : ℝ) ∧
        (N : ℝ) ^ (1 / 3 : ℝ) ≤ (rs.2 : ℝ)))
    (hn : n ∈ goldbachDifferenceCarrier N ε) (hcop : Nat.Coprime n N)
    (hpoint : literalHPoint (N * rs.1) (rs.1 * rs.2) (rs.2 : ℝ) n) :
    (n / (rs.1 * rs.2)).Prime ∨ rs.1 ^ 2 ∣ n := by
  obtain ⟨hp, hwindow⟩ := Finset.mem_filter.mp hrs
  have hh := mem_goldbachS4Pairs_iff.mp hp
  have hb := goldbachG10DifferenceCarrier_bounds hε hn
  have hm := goldbachC8Prod_le_two_thirds hN hp
  have hlarge : rs.1 * rs.2 < n := by
    exact_mod_cast (hm.trans hcut).trans_lt hb.2.2
  have hpow : ((N : ℝ) ^ (1 / 3 : ℝ)) ^ 3 = N := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ N)]
    norm_num
  have hsN : N ≤ rs.2 ^ 3 := by
    have hreal : (N : ℝ) ≤ (rs.2 : ℝ)^3 := by
      calc
        (N : ℝ) = ((N : ℝ) ^ (1 / 3 : ℝ))^3 := hpow.symm
        _ ≤ (rs.2 : ℝ)^3 := by gcongr; exact hwindow.2
    exact_mod_cast hreal
  exact goldbachS5_cofactor_prime_or_square hh.1 hh.2.1 hcop hb.2.1 hlarge hsN hpoint

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig