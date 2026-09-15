import Wu18938Campaign.M1.TargetCofactorPayment

namespace Wu18938Campaign.M1

open Finset Wu2008DoubleSieve WuPaper.R2Mother
open scoped Classical ArithmeticFunction.Omega

private theorem sieve_zero_small {N p D x a : ℕ} {y : ℝ}
    (ha : a.Prime) (haN : a.Coprime N) (had : a ∣ N - p)
    (haD : a.Coprime D) (hax : a.Coprime x) (hay : (a : ℝ) < y) :
    pointSieve N p D (N * x) y = 0 := by
  apply if_neg
  intro hp
  obtain ⟨_, _, hd, hs⟩ := mem_filter.mp hp
  exact hs a ha (Nat.coprime_mul_iff_right.mpr ⟨haN, hax⟩) hay
    ((dvd_quotient_iff hd haD).mpr had)

private theorem pair_zero_two {N p a b x y : ℕ}
    (ha : a.Prime) (hb : b.Prime) (haN : a.Coprime N) (hbN : b.Coprime N)
    (had : a ∣ N - p) (hbd : b ∣ N - p) (hab : a < b)
    (hx : x.Prime) (hy : y.Prime) (hay : a < y) (hby : b < y) :
    pointSieve N p (x * y) (N * x) (y : ℝ) = 0 := by
  by_cases hax : a = x
  · have hbx : b ≠ x := by omega
    have hcopx := (Nat.coprime_primes hb hx).mpr hbx
    exact sieve_zero_small hb hbN hbd
      (Nat.coprime_mul_iff_right.mpr
        ⟨hcopx, (Nat.coprime_primes hb hy).mpr (ne_of_lt hby)⟩)
      hcopx (by exact_mod_cast hby)
  · have hcopx := (Nat.coprime_primes ha hx).mpr hax
    exact sieve_zero_small ha haN had
      (Nat.coprime_mul_iff_right.mpr
        ⟨hcopx, (Nat.coprime_primes ha hy).mpr (ne_of_lt hay)⟩)
      hcopx (by exact_mod_cast hay)

private theorem moving_zero_two {N p a b x y : ℕ}
    (ha : a.Prime) (hb : b.Prime) (haN : a.Coprime N)
    (had : a ∣ N - p) (hbd : b ∣ N - p) (hab : a < b)
    (hx : x.Prime) (hy : y.Prime) (hbx : b < x) (hxy : x < y)
    (hn : 0 < N - p) :
    pointSieve N p (x * y) (N * x) (Real.sqrt ((N : ℝ) / ((x : ℝ) * y))) = 0 := by
  apply if_neg
  intro hp
  obtain ⟨_, _, hd, hs⟩ := mem_filter.mp hp
  have hacx := (Nat.coprime_primes ha hx).mpr (ne_of_lt (hab.trans hbx))
  have hacy := (Nat.coprime_primes ha hy).mpr (ne_of_lt ((hab.trans hbx).trans hxy))
  have hbcx := (Nat.coprime_primes hb hx).mpr (ne_of_lt hbx)
  have hbcy := (Nat.coprime_primes hb hy).mpr (ne_of_lt (hbx.trans hxy))
  have haq := (dvd_quotient_iff hd (hacx.mul_right hacy)).mpr had
  have hbq := (dvd_quotient_iff hd (hbcx.mul_right hbcy)).mpr hbd
  have habq := ((Nat.coprime_primes ha hb).mpr (ne_of_lt hab)).mul_dvd_of_dvd_of_dvd haq hbq
  have hqpos := Nat.div_pos (Nat.le_of_dvd hn hd) (Nat.mul_pos hx.pos hy.pos)
  have hprod : (a : ℝ) * b ≤ ((N - p) / (x * y) : ℕ) := by
    exact_mod_cast Nat.le_of_dvd hqpos habq
  have hqbound : (((N - p) / (x * y) : ℕ) : ℝ) ≤ (N : ℝ) / ((x : ℝ) * y) := by
    apply (le_div_iff₀ (by exact_mod_cast Nat.mul_pos hx.pos hy.pos)).mpr
    have hmul : ((x : ℝ) * y) * ((N - p) / (x * y) : ℕ) = (N - p : ℕ) := by
      exact_mod_cast Nat.mul_div_cancel' hd
    rw [mul_comm, hmul]
    exact_mod_cast Nat.sub_le N p
  have ha0 : (0 : ℝ) < a := by exact_mod_cast ha.pos
  have habR : (a : ℝ) < b := by exact_mod_cast hab
  have hsq : (a : ℝ) ^ 2 < (N : ℝ) / ((x : ℝ) * y) := by
    nlinarith [hprod.trans hqbound]
  have hcut : (a : ℝ) < Real.sqrt ((N : ℝ) / ((x : ℝ) * y)) := by
    exact (Real.lt_sqrt ha0.le).mpr hsq
  exact hs a ha (haN.mul_right hacx) hcut haq

private theorem modulus_zero_squarefree {N p D x : ℕ} {y : ℝ}
    (hsf : Squarefree (N - p)) (hx : x.Prime) (hxN : x.Coprime N) (hxD : x ∣ D) :
    pointSieve N p D (N * x) y - pointSieve N p D N y = 0 := by
  by_cases hd : D ∣ N - p
  · have hcop : D.Coprime ((N - p) / D) :=
      Nat.coprime_of_squarefree_mul (by rwa [Nat.mul_div_cancel' hd])
    have hxn := hx.coprime_iff_not_dvd.mp (hcop.of_dvd_left hxD)
    have heq : Sifted (N * x) ((N - p) / D) y ↔ Sifted N ((N - p) / D) y := by
      rw [sifted_mul_modulus_iff hx hxN]
      exact ⟨fun h => ⟨h, fun _ => hxn⟩, And.left⟩
    simp only [pointSieve, sieveCarrier, mem_filter, heq, sub_self]
  · rw [pointSieve_zero_of_not_dvd _ hd, pointSieve_zero_of_not_dvd _ hd, sub_self]

theorem target_prime_cofactor_gains_zero {N p a b c d : ℕ} (hN : 4 ≤ N)
    (he : Even N) (ht : (a, b, c, d) ∈ targetExcessTuples N)
    (hp : p ∈ targetPrimeCofactorCarrier N (a * b * c * d)) :
    pointGains N p ((N : ℝ) ^ (100 / 1327 : ℝ)) ((N : ℝ) ^ (25 / 206 : ℝ))
      ((N : ℝ) ^ (1 / 2 - 3 * (100 / 1327 : ℝ))) ((N : ℝ) ^ (1 / 3 : ℝ)) = 0 := by
  let z := (N : ℝ) ^ (100 / 1327 : ℝ)
  let w := (N : ℝ) ^ (25 / 206 : ℝ)
  let u := (N : ℝ) ^ (1 / 2 - 3 * (100 / 1327 : ℝ))
  let v := (N : ℝ) ^ (1 / 3 : ℝ)
  let r := (N - p) / (a * b * c * d)
  obtain ⟨hpr, hpp, hD, hnN, hr, hvr⟩ := mem_filter.mp hp
  obtain ⟨ha, haN, hza, hb, hbN, hc, hcN, hd, hdN, hdu, hab, hbc, hcd, hcw, hwd⟩ :=
    mem_s3_second_quadruples.mp (mem_filter.mp ht).1
  change r.Prime at hr
  change v ≤ (r : ℝ) at hvr
  change z ≤ (a : ℝ) at hza
  change (d : ℝ) < u at hdu
  change (c : ℝ) < w at hcw
  change w ≤ (d : ℝ) at hwd
  have huv : u ≤ v := Real.rpow_le_rpow_of_exponent_le
    (by exact_mod_cast (show 1 ≤ N by omega)) (by norm_num)
  have hn := complement_pos_of_even hN he
    (by have := mem_range.mp hpr; omega) hpp
  have heq : N - p = a * b * c * d * r := (Nat.mul_div_cancel' hD).symm
  have hdr : d < r := by exact_mod_cast (hdu.trans_le (huv.trans hvr))
  have hprime : ∀ q : ℕ, q ∣ N - p → q.Prime →
      q = a ∨ q = b ∨ q = c ∨ q = d ∨ q = r := by
    intro q hq hqp
    rw [heq] at hq
    simpa only [hqp.dvd_mul, Nat.prime_dvd_prime_iff_eq hqp ha,
      Nat.prime_dvd_prime_iff_eq hqp hb, Nat.prime_dvd_prime_iff_eq hqp hc,
      Nat.prime_dvd_prime_iff_eq hqp hd, Nat.prime_dvd_prime_iff_eq hqp hr, or_assoc] using hq
  have hsf : Squarefree (N - p) := by
    rw [heq]
    have hco : ∀ x ∈ ({a, b, c, d, r} : Finset ℕ),
        ∀ y ∈ ({a, b, c, d, r} : Finset ℕ), x ≠ y → x.Coprime y := by
      intro x hx y hy hxy
      have hxp : x.Prime := by
        simp only [mem_insert, mem_singleton] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl <;> assumption
      have hyp : y.Prime := by
        simp only [mem_insert, mem_singleton] at hy
        rcases hy with rfl | rfl | rfl | rfl | rfl <;> assumption
      exact (Nat.coprime_primes hxp hyp).mpr hxy
    simp only [Nat.squarefree_mul_iff, Nat.coprime_mul_iff_left,
      ha.squarefree, hb.squarefree, hc.squarefree, hd.squarefree, hr.squarefree, and_true]
    repeat' constructor
    all_goals apply hco _ (by simp) _ (by simp); omega
  have had : a ∣ N - p :=
    (dvd_mul_right a b).trans ((dvd_mul_right (a * b) c).trans
      ((dvd_mul_right (a * b * c) d).trans hD))
  have hbd : b ∣ N - p :=
    (dvd_mul_left b a).trans ((dvd_mul_right (a * b) c).trans
      ((dvd_mul_right (a * b * c) d).trans hD))
  have hcdvd : c ∣ N - p := (dvd_mul_left c (a * b)).trans
    ((dvd_mul_right (a * b * c) d).trans hD)
  have hdd : d ∣ N - p := (dvd_mul_left d (a * b * c)).trans hD
  have habR : (a : ℝ) < b := by exact_mod_cast hab
  have hbcR : (b : ℝ) < c := by exact_mod_cast hbc
  have hcdR : (c : ℝ) < d := by exact_mod_cast hcd
  have haw : (a : ℝ) < w := habR.trans (hbcR.trans hcw)
  have hbw : (b : ℝ) < w := hbcR.trans hcw
  have hwu : w ≤ u := hwd.trans hdu.le
  have hwv : w ≤ v := hwu.trans huv
  have hsz : p ∈ sieveCarrier N 1 N z := by
    apply mem_sieveCarrier_one.mpr
    refine ⟨by have := mem_range.mp hpr; omega, hpp, ?_⟩
    intro q hq _ hqz hqd
    rcases hprime q hqd hq with rfl | rfl | rfl | rfl | rfl
    all_goals linarith
  have hnw : p ∉ sieveCarrier N 1 N w := by
    intro h
    exact (mem_sieveCarrier_one.mp h).2.2 a ha haN haw had
  have hF : divisorsIn (primeWindow N z v) (N - p) = {a, b, c, d} := by
    ext q
    simp only [divisorsIn, mem_filter, mem_insert, mem_singleton]
    constructor
    · rintro ⟨hq, hqd⟩
      have hqv := (mem_primeWindow.mp hq).2.2.2
      rcases hprime q hqd (mem_primeWindow.mp hq).1 with h | h | h | h | h
      · tauto
      · tauto
      · tauto
      · tauto
      · subst q; exact (not_lt_of_ge hvr hqv).elim
    · rintro (rfl | rfl | rfl | rfl)
      all_goals refine ⟨mem_primeWindow.mpr ⟨by assumption, by assumption, ?_, ?_⟩, by assumption⟩
      all_goals linarith
  have hcard : ({a, b, c, d} : Finset ℕ).card = 4 := by
    simp [ne_of_lt hab, ne_of_lt hbc, ne_of_lt hcd, ne_of_lt (hab.trans hbc),
      ne_of_lt (hbc.trans hcd), ne_of_lt ((hab.trans hbc).trans hcd)]
  have hOrd : pointOrdinary N p = 0 := by
    have hsub : divisorsIn (primeWindow N z v) (N - p) ⊆ (N - p).primeFactors := by
      intro q hq
      exact Nat.mem_primeFactors.mpr
        ⟨(mem_primeWindow.mp (mem_filter.mp hq).1).1, (mem_filter.mp hq).2, hn.ne'⟩
    have hfour := card_le_card hsub
    rw [hF, hcard, primeFactors_card_eq_omega_of_squarefree hsf] at hfour
    apply if_neg
    intro hp
    have htwo := (MathlibNt.Wu2008DoubleSieve.mem_wuPrimeComplements.mp hp).2.2.2
    omega
  have hpair : ∀ x y : ℕ, ∀ l t : ℝ, (x, y) ∈ lowerPairs N N l t → w ≤ t →
      pointSieve N p (x * y) (N * x) (y : ℝ) = 0 := by
    intro x y l t hxy hwt
    obtain ⟨hx, hy, _, _, hty, _, _⟩ := mem_lowerPairs_source.mp hxy
    apply pair_zero_two ha hb haN hbN had hbd hab hx hy
    · exact_mod_cast haw.trans_le (hwt.trans hty)
    · exact_mod_cast hbw.trans_le (hwt.trans hty)
  have hlow : pointLower N p z v = 0 := by
    have hpen : lowerPairPenalty N N (N - p) z v = 0 := by
      apply sum_eq_zero
      rintro ⟨x, y⟩ hxy
      have hz := hpair x y z v hxy hwv
      unfold pointSieve at hz
      have hnot : ¬lowerPairSurvives N (N - p) (x, y) := by
        intro hs
        have hm : p ∈ sieveCarrier N (x * y) (N * x) (y : ℝ) :=
          mem_filter.mpr ⟨hpr, hpp, hs⟩
        rw [if_pos hm] at hz
        omega
      simp only [if_neg hnot]
    unfold pointLower
    rw [if_pos hsz]
    unfold lowerWeight
    rw [hpen, two_sub_card_add_triples, hF, hcard]
    norm_num
  have hhigh : pointLower N p w u = 0 := if_neg hnw
  have hS4 : pointS4 N p w u = 0 := by
    apply sum_eq_zero
    rintro ⟨x, y, s⟩ ht
    apply if_neg
    intro hp
    have hc := tripleCarrier_eq N 1 N ht
    simp only [one_mul] at hc
    rw [← hc] at hp
    exact hnw (mem_filter.mp hp).1
  have htriple : ∀ x y s : ℕ, x.Prime → y.Prime → s.Prime →
      w ≤ (x : ℝ) → x < y → y < s → ∀ T : ℝ, (a : ℝ) < T →
      pointSieve N p (x * y * s) (N * x) T = 0 := by
    intro x y s hx hy hs hwx hxy hys T haT
    have hax : a < x := by exact_mod_cast haw.trans_le hwx
    have hcopx := (Nat.coprime_primes ha hx).mpr (ne_of_lt hax)
    have hcopy := (Nat.coprime_primes ha hy).mpr (ne_of_lt (hax.trans hxy))
    have hcops := (Nat.coprime_primes ha hs).mpr (ne_of_lt ((hax.trans hxy).trans hys))
    exact sieve_zero_small ha haN had ((hcopx.mul_right hcopy).mul_right hcops) hcopx haT
  have hVar : pointVariableSlack N p w u = 0 := by
    have hmain : ∀ t ∈ lowerPairs N N w u,
        pointSieve N p (t.1 * t.2) (N * t.1)
          (Real.sqrt ((N : ℝ) / ((t.1 : ℝ) * t.2))) = 0 := by
      rintro ⟨x, y⟩ hxy
      obtain ⟨hx, hy, _, hwx, _, hxy, _⟩ := mem_lowerPairs_source.mp hxy
      exact moving_zero_two ha hb haN had hbd hab hx hy
        (by exact_mod_cast hbw.trans_le hwx) hxy hn
    have htrip : ∀ t ∈ lowerPairs N N w u, ∀ s ∈
        (primeWindow N (t.2 : ℝ) (Real.sqrt ((N : ℝ) / ((t.1 : ℝ) * t.2)))).filter
          (fun s => t.2 < s),
        pointSieve N p (t.1 * t.2 * s) (N * t.1) (s : ℝ) = 0 := by
      rintro ⟨x, y⟩ hxy s hs
      obtain ⟨hx, hy, _, hwx, _, hxy, _⟩ := mem_lowerPairs_source.mp hxy
      have hys := (mem_filter.mp hs).2
      apply htriple x y s hx hy (mem_primeWindow.mp (mem_filter.mp hs).1).1 hwx hxy hys
      exact (haw.trans_le hwx).trans (by exact_mod_cast hxy.trans hys)
    have hbudget : pointPairBudget N p w u = 0 := by
      apply sum_eq_zero
      rintro ⟨x, y⟩ ht
      apply if_neg
      intro hp
      have hzero := hpair x y w u ht hwu
      have hmem := (mem_filter.mp hp).1
      unfold pointSieve at hzero
      rw [if_pos hmem] at hzero
      omega
    unfold pointVariableSlack
    rw [hbudget]
    have hm := sum_eq_zero (fun t (ht : t ∈ (lowerPairs N N w u).filter (fun t => (t.1 : ℝ) < u)) =>
      hmain t (mem_filter.mp ht).1)
    have ht := sum_eq_zero (fun t (ht : t ∈ (lowerPairs N N w u).filter (fun t => (t.1 : ℝ) < u)) =>
      sum_eq_zero (fun s hs => htrip t (mem_filter.mp ht).1 s hs))
    have hp := sum_eq_zero (fun t (ht : t ∈ (lowerPairs N N w u).filter (fun t => (t.1 : ℝ) < u)) =>
      hpair t.1 t.2 w u (mem_filter.mp ht).1 hwu)
    rw [hm, ht, hp]
    omega
  have hRet : pointRetained N p z w u v = 0 := by
    have hleft : (∑ t ∈ orderedTriples (primeWindow N z v) \
        (orderedTriples (primeWindow N z w) ∪ s3SecondRange N z w u ∪ s3ThirdRange N w u),
        pointSieve N p (t.1 * t.2.1 * t.2.2) (N * t.1) (t.2.1 : ℝ)) = 0 := by
      apply sum_eq_zero
      rintro ⟨x, y, s⟩ ht
      obtain ⟨hordered, hout⟩ := mem_sdiff.mp ht
      apply if_neg
      intro hp
      have hc := tripleCarrier_eq N 1 N hordered
      simp only [one_mul] at hc
      rw [← hc] at hp
      have hs := (mem_filter.mp hp).2
      simp only [Nat.div_one] at hs
      have hsurv : (x, y, s) ∈ firstTwoTriples (divisorsIn (primeWindow N z v) (N - p)) := by
        rw [firstTwoTriples_divisorsIn]
        exact mem_filter.mpr ⟨hordered, hs⟩
      rw [hF] at hsurv
      have hcan : (a, b, c) ∈ firstTwoTriples ({a, b, c, d} : Finset ℕ) := by
        rw [mem_firstTwoTriples]
        refine ⟨by simp, by simp, by simp, hab, hbc, ?_⟩
        intro q hq hqb
        simp only [mem_insert, mem_singleton] at hq
        omega
      obtain ⟨hxa, hyb⟩ := firstTwoTriples_first_two_unique hsurv hcan
      subst x
      subst y
      have hsm := (mem_firstTwoTriples.mp hsurv).2.2.1
      simp only [mem_insert, mem_singleton] at hsm
      obtain ⟨hx, hxN, hzx, hy, hyN, hs, hsN, _, hxy, hys⟩ :=
        mem_s3_ordered_triples.mp hordered
      have hsu : (s : ℝ) < u := by
        rcases hsm with rfl | rfl | rfl | rfl <;> linarith
      apply hout
      apply mem_union_left
      by_cases hsw : (s : ℝ) < w
      · exact mem_union_left _ (mem_s3_ordered_triples.mpr
          ⟨hx, hxN, hzx, hy, hyN, hs, hsN, hsw, hxy, hys⟩)
      · exact mem_union_right _ (mem_filter.mpr ⟨mem_s3_ordered_triples.mpr
          ⟨hx, hxN, hzx, hy, hyN, hs, hsN, hsu, hxy, hys⟩, hbw, le_of_not_gt hsw⟩)
    have hmod : ∀ t ∈ orderedTriples (primeWindow N z v),
        pointSieve N p (t.1 * t.2.1 * t.2.2) (N * t.1) (t.2.1 : ℝ) -
        pointSieve N p (t.1 * t.2.1 * t.2.2) N (t.2.1 : ℝ) = 0 := by
      rintro ⟨x, y, s⟩ ht
      obtain ⟨hx, hxN, _⟩ := mem_s3_ordered_triples.mp ht
      exact modulus_zero_squarefree hsf hx hxN
        ((dvd_mul_right x y).trans (dvd_mul_right (x * y) s))
    have hthird : (∑ t ∈ s3ThirdRange N w u,
        (pointSieve N p (t.1 * t.2.1 * t.2.2) (N * t.1) (t.2.1 : ℝ) -
        pointSieve N p (t.1 * t.2.1 * t.2.2) (N * t.1) (t.2.2 : ℝ))) = 0 := by
      apply sum_eq_zero
      rintro ⟨x, y, s⟩ ht
      obtain ⟨hpair, _, hs, hys⟩ := mem_s3ThirdRange.mp ht
      obtain ⟨hx, hy, _, hwx, _, hxy, _⟩ := mem_lowerPairs_source.mp hpair
      have haY : (a : ℝ) < y := (haw.trans_le hwx).trans (by exact_mod_cast hxy)
      have haS : (a : ℝ) < s := haY.trans (by exact_mod_cast hys)
      rw [htriple x y s hx hy (mem_primeWindow.mp hs).1 hwx hxy hys _ haY,
        htriple x y s hx hy (mem_primeWindow.mp hs).1 hwx hxy hys _ haS, sub_self]
    unfold pointRetained
    rw [hleft, hthird]
    have h1 := sum_eq_zero (fun t (ht : t ∈ orderedTriples (primeWindow N z w)) =>
      hmod t (s3_ordered_triples_mono N z hwv ht))
    have h2 := sum_eq_zero (fun t (ht : t ∈ s3SecondRange N z w u) =>
      hmod t (s3_ordered_triples_mono N z huv (mem_filter.mp ht).1))
    rw [h1, h2]
    omega
  change pointGains N p z w u v = 0
  unfold pointGains pointOuterSlack
  rw [hRet, hS4, hVar, hOrd, hlow, hhigh]
  omega

theorem target_prime_cofactor_residual_pos {N p a b c d : ℕ} (hN : 4 ≤ N)
    (he : Even N) (ht : (a, b, c, d) ∈ targetExcessTuples N)
    (hp : p ∈ targetPrimeCofactorCarrier N (a * b * c * d)) :
    1 ≤ pointExcess N p ((N : ℝ) ^ (100 / 1327 : ℝ))
      ((N : ℝ) ^ (25 / 206 : ℝ))
      ((N : ℝ) ^ (1 / 2 - 3 * (100 / 1327 : ℝ)))
      ((N : ℝ) ^ (1 / 2 - 2 * (100 / 1327 : ℝ))) -
      pointGains N p ((N : ℝ) ^ (100 / 1327 : ℝ)) ((N : ℝ) ^ (25 / 206 : ℝ))
        ((N : ℝ) ^ (1 / 2 - 3 * (100 / 1327 : ℝ))) ((N : ℝ) ^ (1 / 3 : ℝ)) := by
  rw [target_prime_cofactor_gains_zero hN he ht hp, sub_zero]
  obtain ⟨hpr, hpp, hD, _, hr, hvr⟩ := mem_filter.mp hp
  have hcut := (target_excess_product_geometry (by omega) ht).2.1.le.trans hvr
  have hmem : p ∈ sieveCarrier N (a * b * c * d) N (b : ℝ) :=
    mem_filter.mpr ⟨hpr, hpp, hD, sifted_prime_of_le hr hcut⟩
  have hterm : pointSieve N p (a * b * c * d) N (b : ℝ) = 1 := if_pos hmem
  change 1 ≤ ∑ t ∈ targetExcessTuples N,
    pointSieve N p (t.1 * t.2.1 * t.2.2.1 * t.2.2.2) N (t.2.1 : ℝ)
  have hsum := single_le_sum (s := targetExcessTuples N)
    (f := fun t : ℕ × ℕ × ℕ × ℕ =>
      pointSieve N p (t.1 * t.2.1 * t.2.2.1 * t.2.2.2) N (t.2.1 : ℝ))
    (fun t _ => pointSieve_nonneg N p _ _ _) ht
  dsimp only at hsum
  rw [hterm] at hsum
  exact hsum

end Wu18938Campaign.M1
