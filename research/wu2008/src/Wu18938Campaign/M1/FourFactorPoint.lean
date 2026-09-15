import Wu18938Campaign.M1.PointWeights

namespace Wu18938Campaign.M1

open Finset Wu2008DoubleSieve WuPaper.R2Mother
open scoped Classical ArithmeticFunction.Omega

structure FourFactorShape (N p a b c d : ℕ) (z w u v V : ℝ) : Prop where
  primeIndex : p.Prime
  indexBound : p ≤ N
  complement : N - p = a * b * c * d
  primeA : a.Prime
  primeB : b.Prime
  primeC : c.Prime
  primeD : d.Prime
  coprime : (N - p).Coprime N
  ab : a < b
  bc : b < c
  cd : c < d
  za : z ≤ (a : ℝ)
  cw : (c : ℝ) < w
  wd : w ≤ (d : ℝ)
  du : (d : ℝ) < u
  uv : u ≤ v
  crossing : V ≤ (c : ℝ) * d

namespace FourFactorShape

variable {N p a b c d : ℕ} {z w u v V : ℝ}
variable (h : FourFactorShape N p a b c d z w u v V)
include h

theorem squarefree : Squarefree (N - p) := by
  rw [h.complement]
  have hab := (Nat.coprime_primes h.primeA h.primeB).mpr (ne_of_lt h.ab)
  have hac := (Nat.coprime_primes h.primeA h.primeC).mpr (ne_of_lt (h.ab.trans h.bc))
  have had := (Nat.coprime_primes h.primeA h.primeD).mpr
    (ne_of_lt ((h.ab.trans h.bc).trans h.cd))
  have hbc := (Nat.coprime_primes h.primeB h.primeC).mpr (ne_of_lt h.bc)
  have hbd := (Nat.coprime_primes h.primeB h.primeD).mpr (ne_of_lt (h.bc.trans h.cd))
  have hcd := (Nat.coprime_primes h.primeC h.primeD).mpr (ne_of_lt h.cd)
  simp only [Nat.squarefree_mul_iff, Nat.coprime_mul_iff_left,
    h.primeA.squarefree, h.primeB.squarefree, h.primeC.squarefree, h.primeD.squarefree,
    and_self]
  exact ⟨⟨⟨had, hbd⟩, hcd⟩, ⟨⟨hac, hbc⟩, ⟨hab, trivial⟩, trivial⟩, trivial⟩

theorem prime_dvd_iff {q : ℕ} (hq : q.Prime) :
    q ∣ N - p ↔ q = a ∨ q = b ∨ q = c ∨ q = d := by
  rw [h.complement]
  simp only [hq.dvd_mul, Nat.prime_dvd_prime_iff_eq hq h.primeA,
    Nat.prime_dvd_prime_iff_eq hq h.primeB,
    Nat.prime_dvd_prime_iff_eq hq h.primeC,
    Nat.prime_dvd_prime_iff_eq hq h.primeD]
  tauto

theorem factors :
    (N - p).primeFactors = {a, b, c, d} := by
  ext q
  simp only [Nat.mem_primeFactors, mem_insert, mem_singleton]
  constructor
  · intro hq
    exact (h.prime_dvd_iff hq.1).mp hq.2.1
  · intro hq
    have hqp : q.Prime := by
      rcases hq with rfl | rfl | rfl | rfl
      · exact h.primeA
      · exact h.primeB
      · exact h.primeC
      · exact h.primeD
    exact ⟨hqp, (h.prime_dvd_iff hqp).mpr hq, h.squarefree.ne_zero⟩

theorem prime_dvd_lt_u {q : ℕ} (hq : q.Prime) (hqd : q ∣ N - p) :
    (q : ℝ) < u := by
  have hq := (h.prime_dvd_iff hq).mp hqd
  have hab : (a : ℝ) < b := by exact_mod_cast h.ab
  have hbc : (b : ℝ) < c := by exact_mod_cast h.bc
  have hcd : (c : ℝ) < d := by exact_mod_cast h.cd
  rcases hq with rfl | rfl | rfl | rfl <;> linarith [h.du]

theorem sifted_z : p ∈ sieveCarrier N 1 N z := by
  apply mem_sieveCarrier_one.mpr
  refine ⟨h.indexBound, h.primeIndex, ?_⟩
  intro q hq _ hqz hqd
  have he := (h.prime_dvd_iff hq).mp hqd
  have hab : (a : ℝ) < b := by exact_mod_cast h.ab
  have hbc : (b : ℝ) < c := by exact_mod_cast h.bc
  have hcd : (c : ℝ) < d := by exact_mod_cast h.cd
  rcases he with rfl | rfl | rfl | rfl <;> linarith [h.za]

theorem not_sifted_w : p ∉ sieveCarrier N 1 N w := by
  intro hp
  have ha : a ∣ N - p := (h.prime_dvd_iff h.primeA).mpr (Or.inl rfl)
  have hab : (a : ℝ) < b := by exact_mod_cast h.ab
  have hbc : (b : ℝ) < c := by exact_mod_cast h.bc
  exact (mem_sieveCarrier_one.mp hp).2.2 a h.primeA
    (h.coprime.of_dvd_left ha) (by linarith [h.cw]) ha

theorem not_ordinary : pointOrdinary N p = 0 := by
  have hf : (N - p).primeFactors.card = 4 := by
    rw [h.factors]
    simp [ne_of_lt h.ab, ne_of_lt h.bc, ne_of_lt h.cd,
      ne_of_lt (h.ab.trans h.bc), ne_of_lt (h.bc.trans h.cd),
      ne_of_lt ((h.ab.trans h.bc).trans h.cd)]
  unfold pointOrdinary
  apply if_neg
  intro hp
  have hΩ := (MathlibNt.Wu2008DoubleSieve.mem_wuPrimeComplements.mp hp).2.2.2
  rw [← primeFactors_card_eq_omega_of_squarefree h.squarefree, hf] at hΩ
  omega

theorem full_divisors :
    divisorsIn (primeWindow N z v) (N - p) = {a, b, c, d} := by
  rw [← h.factors]
  ext q
  constructor
  · intro hq
    obtain ⟨hq, hqd⟩ := mem_filter.mp hq
    exact Nat.mem_primeFactors.mpr
      ⟨(mem_primeWindow.mp hq).1, hqd, h.squarefree.ne_zero⟩
  · intro hq
    obtain ⟨hqp, hqd, _⟩ := Nat.mem_primeFactors.mp hq
    apply mem_filter.mpr
    refine ⟨mem_primeWindow.mpr
      ⟨hqp, h.coprime.of_dvd_left hqd, ?_, (h.prime_dvd_lt_u hqp hqd).trans_le h.uv⟩, hqd⟩
    exact primeFactor_ge_cutoff h.coprime
      (mem_sieveCarrier_one.mp h.sifted_z).2.2 (Nat.mem_primeFactors.mpr
        ⟨hqp, hqd, h.squarefree.ne_zero⟩)

theorem no_pair_divisor {x y : ℕ} {l t : ℝ}
    (ht : (x, y) ∈ lowerPairs N N l t) (hut : u ≤ t) :
    ¬x * y ∣ N - p := by
  intro hd
  obtain ⟨_, hy, _, _, hty, _, _⟩ := mem_lowerPairs_source.mp ht
  have hyu := h.prime_dvd_lt_u hy ((dvd_mul_left y x).trans hd)
  linarith

theorem full_lower_zero : pointLower N p z v = 0 := by
  have hpen : lowerPairPenalty N N (N - p) z v = 0 := by
    apply sum_eq_zero
    intro t ht
    have hd := h.no_pair_divisor ht h.uv
    simp only [lowerPairSurvives, hd, false_and, if_false]
  unfold pointLower
  rw [if_pos h.sifted_z]
  unfold lowerWeight
  rw [hpen, h.full_divisors, two_sub_card_add_triples]
  have hf : ({a, b, c, d} : Finset ℕ).card = 4 := by
    simp [ne_of_lt h.ab, ne_of_lt h.bc, ne_of_lt h.cd,
      ne_of_lt (h.ab.trans h.bc), ne_of_lt (h.bc.trans h.cd),
      ne_of_lt ((h.ab.trans h.bc).trans h.cd)]
  rw [hf]
  norm_num

theorem first_lower_zero : pointLower N p w u = 0 := by
  exact if_neg h.not_sifted_w

theorem outer_slacks_zero :
    pointOuterSlack N p w u = 0 ∧ pointOuterSlack N p z v = 0 := by
  simp only [pointOuterSlack, h.not_ordinary, h.first_lower_zero, h.full_lower_zero,
    mul_zero, sub_zero, and_self]

theorem high_s4_zero : pointS4 N p w u = 0 := by
  apply sum_eq_zero
  rintro ⟨x, y, r⟩ ht
  unfold pointSieve
  apply if_neg
  intro hp
  have hc := tripleCarrier_eq N 1 N ht
  simp only [one_mul] at hc
  rw [← hc] at hp
  exact h.not_sifted_w (mem_filter.mp hp).1

theorem variable_slack_zero : pointVariableSlack N p w u = 0 := by
  have hpair : ∀ t ∈ lowerPairs N N w u, ¬t.1 * t.2 ∣ N - p :=
    fun _ ht => h.no_pair_divisor ht le_rfl
  have hQ : ∀ t ∈ lowerPairs N N w u, ∀ M y,
      pointSieve N p (t.1 * t.2) M y = 0 :=
    fun t ht _ y => pointSieve_zero_of_not_dvd y (hpair t ht)
  have hQ3 : ∀ t ∈ lowerPairs N N w u, ∀ r M y,
      pointSieve N p (t.1 * t.2 * r) M y = 0 := by
    intro t ht r M y
    apply pointSieve_zero_of_not_dvd
    intro hd
    exact hpair t ht ((dvd_mul_right (t.1 * t.2) r).trans hd)
  have hB : pointPairBudget N p w u = 0 := by
    apply sum_eq_zero
    intro t ht
    apply if_neg
    intro hp
    exact hpair t ht (mem_sieveEndpointLoss.mp hp).2.2.1
  unfold pointVariableSlack
  rw [hB]
  have h1 : (∑ t ∈ (lowerPairs N N w u).filter (fun t => (t.1 : ℝ) < u),
      pointSieve N p (t.1 * t.2) (N * t.1)
        (Real.sqrt ((N : ℝ) / ((t.1 : ℝ) * t.2)))) = 0 :=
    sum_eq_zero (fun t ht => hQ t (mem_filter.mp ht).1 _ _)
  have h2 : (∑ t ∈ (lowerPairs N N w u).filter (fun t => (t.1 : ℝ) < u),
      ∑ r ∈ (primeWindow N (t.2 : ℝ)
        (Real.sqrt ((N : ℝ) / ((t.1 : ℝ) * t.2)))).filter (fun r => t.2 < r),
        pointSieve N p (t.1 * t.2 * r) (N * t.1) (r : ℝ)) = 0 :=
    sum_eq_zero (fun t ht => sum_eq_zero
      (fun r _ => hQ3 t (mem_filter.mp ht).1 r _ _))
  have h3 : (∑ t ∈ (lowerPairs N N w u).filter (fun t => (t.1 : ℝ) < u),
      pointSieve N p (t.1 * t.2) (N * t.1) (t.2 : ℝ)) = 0 :=
    sum_eq_zero (fun t ht => hQ t (mem_filter.mp ht).1 _ _)
  rw [h1, h2, h3]
  omega

theorem modulus_gain_zero {x y r : ℕ} {l t : ℝ}
    (ht : (x, y, r) ∈ orderedTriples (primeWindow N l t)) :
    pointSieve N p (x * y * r) (N * x) (y : ℝ) -
      pointSieve N p (x * y * r) N (y : ℝ) = 0 := by
  have hx := (mem_s3_ordered_triples.mp ht).1
  have he : p ∈ sieveCarrier N (x * y * r) (N * x) (y : ℝ) ↔
      p ∈ sieveCarrier N (x * y * r) N (y : ℝ) := by
    constructor
    · intro hp
      obtain ⟨hpR, hpp, hd, hs⟩ := mem_filter.mp hp
      refine mem_filter.mpr ⟨hpR, hpp, hd, ?_⟩
      have hxn : ¬x ∣ (N - p) / (x * y * r) := by
        intro hxd
        have hxx := Nat.mul_dvd_mul
          ((dvd_mul_right x y).trans (dvd_mul_right (x * y) r)) hxd
        rw [Nat.mul_div_cancel' hd] at hxx
        exact (Nat.squarefree_iff_prime_squarefree.mp h.squarefree) x hx hxx
      intro q hq hqN hqy hqd
      by_cases hqx : q = x
      · exact hxn (hqx ▸ hqd)
      · exact hs q hq
          (Nat.coprime_mul_iff_right.mpr
            ⟨hqN, (Nat.coprime_primes hq hx).mpr hqx⟩) hqy hqd
    · intro hp
      obtain ⟨hpR, hpp, hd, hs⟩ := mem_filter.mp hp
      exact mem_filter.mpr ⟨hpR, hpp, hd, fun q hq hqN hqy =>
        hs q hq (Nat.coprime_mul_iff_right.mp hqN).1 hqy⟩
  simp only [pointSieve, he, sub_self]

theorem retained_zero : pointRetained N p z w u v = 0 := by
  have hleft :
      (∑ t ∈ orderedTriples (primeWindow N z v) \
        (orderedTriples (primeWindow N z w) ∪ s3SecondRange N z w u ∪
          s3ThirdRange N w u),
        pointSieve N p (t.1 * t.2.1 * t.2.2) (N * t.1) (t.2.1 : ℝ)) = 0 := by
    apply sum_eq_zero
    rintro ⟨x, y, r⟩ ht
    obtain ⟨ht, hout⟩ := mem_sdiff.mp ht
    unfold pointSieve
    apply if_neg
    intro hp
    have hc := tripleCarrier_eq N 1 N ht
    simp only [one_mul] at hc
    rw [← hc] at hp
    have hs := (mem_filter.mp hp).2
    simp only [Nat.div_one] at hs
    obtain ⟨hx, hxN, hzx, hy, hyN, hr, hrN, _, hxy, hyr⟩ :=
      mem_s3_ordered_triples.mp ht
    have hru : (r : ℝ) < u := h.prime_dvd_lt_u hr hs.2.2.1
    have hmin : ∀ q ∈ divisorsIn (primeWindow N z v) (N - p),
        q < y → q = x := by
      intro q hq hqy
      by_contra hqx
      exact hs.2.2.2 q (mem_filter.mp hq).1 hqy hqx (mem_filter.mp hq).2
    have hyw : (y : ℝ) < w := by
      by_contra hyw
      have ham : a ∈ divisorsIn (primeWindow N z v) (N - p) := by
        rw [h.full_divisors]; simp
      have hbm : b ∈ divisorsIn (primeWindow N z v) (N - p) := by
        rw [h.full_divisors]; simp
      have hab : (a : ℝ) < b := by exact_mod_cast h.ab
      have hbc : (b : ℝ) < c := by exact_mod_cast h.bc
      have hay : a < y := by exact_mod_cast (show (a : ℝ) < y by linarith [h.cw])
      have hby : b < y := by exact_mod_cast (show (b : ℝ) < y by linarith [h.cw])
      have := hmin a ham hay
      have := hmin b hbm hby
      have := h.ab
      omega
    apply hout
    apply mem_union.mpr
    left
    apply mem_union.mpr
    by_cases hrw : (r : ℝ) < w
    · exact Or.inl (mem_s3_ordered_triples.mpr
        ⟨hx, hxN, hzx, hy, hyN, hr, hrN, hrw, hxy, hyr⟩)
    · exact Or.inr (mem_filter.mpr ⟨mem_s3_ordered_triples.mpr
        ⟨hx, hxN, hzx, hy, hyN, hr, hrN, hru, hxy, hyr⟩,
          hyw, le_of_not_gt hrw⟩)
  have hthird : (∑ t ∈ s3ThirdRange N w u,
      (pointSieve N p (t.1 * t.2.1 * t.2.2) (N * t.1) (t.2.1 : ℝ) -
        pointSieve N p (t.1 * t.2.1 * t.2.2) (N * t.1) (t.2.2 : ℝ))) = 0 := by
    apply sum_eq_zero
    rintro ⟨x, y, r⟩ ht
    have hd : ¬x * y * r ∣ N - p := by
      intro hd
      exact h.no_pair_divisor (mem_s3ThirdRange.mp ht).1 le_rfl
        ((dvd_mul_right (x * y) r).trans hd)
    simp only [pointSieve_zero_of_not_dvd _ hd, sub_self]
  unfold pointRetained
  rw [hleft, hthird]
  have hfirst := sum_eq_zero (fun t (ht : t ∈ orderedTriples (primeWindow N z w)) =>
    h.modulus_gain_zero ht)
  have hsecond := sum_eq_zero (fun t (ht : t ∈ s3SecondRange N z w u) =>
    h.modulus_gain_zero (mem_filter.mp ht).1)
  rw [hfirst, hsecond]
  omega

theorem gains_zero : pointGains N p z w u v = 0 := by
  unfold pointGains
  rw [h.retained_zero, h.high_s4_zero, h.variable_slack_zero,
    h.outer_slacks_zero.1, h.outer_slacks_zero.2]
  omega

theorem low_s4_two : pointS4 N p z v = 2 := by
  rw [pointS4_eq_firstTwo h.sifted_z, h.full_divisors, firstTwoTriples_card]
  have hf : ({a, b, c, d} : Finset ℕ).card = 4 := by
    simp [ne_of_lt h.ab, ne_of_lt h.bc, ne_of_lt h.cd,
      ne_of_lt (h.ab.trans h.bc), ne_of_lt (h.bc.trans h.cd),
      ne_of_lt ((h.ab.trans h.bc).trans h.cd)]
  rw [hf]
  norm_num

theorem quadruple_unique {x y r s : ℕ}
    (hx : x.Prime) (hy : y.Prime) (hr : r.Prime) (hs : s.Prime)
    (hxy : x < y) (hyr : y < r) (hrs : r < s)
    (hd : x * y * r * s ∣ N - p) :
    (x, y, r, s) = (a, b, c, d) := by
  have hxd := (h.prime_dvd_iff hx).mp
    (((dvd_mul_right x y).trans (dvd_mul_right (x * y) r)).trans
      ((dvd_mul_right (x * y * r) s).trans hd))
  have hyd := (h.prime_dvd_iff hy).mp
    (((dvd_mul_left y x).trans (dvd_mul_right (x * y) r)).trans
      ((dvd_mul_right (x * y * r) s).trans hd))
  have hrd := (h.prime_dvd_iff hr).mp
    ((dvd_mul_left r (x * y)).trans ((dvd_mul_right (x * y * r) s).trans hd))
  have hsd := (h.prime_dvd_iff hs).mp ((dvd_mul_left s (x * y * r)).trans hd)
  have hab := h.ab
  have hbc := h.bc
  have hcd := h.cd
  have : x = a ∧ y = b ∧ r = c ∧ s = d := by omega
  rcases this with ⟨rfl, rfl, rfl, rfl⟩
  rfl

theorem excess_one : pointExcess N p z w u V = 1 := by
  have hcop : ∀ q, q.Prime → q = a ∨ q = b ∨ q = c ∨ q = d →
      q.Coprime N :=
    fun q hq he => h.coprime.of_dvd_left ((h.prime_dvd_iff hq).mpr he)
  have hmem : (a, b, c, d) ∈ s3Upsilon11Excess N z w u V :=
    mem_filter.mpr ⟨mem_s3_second_quadruples.mpr
      ⟨h.primeA, hcop a h.primeA (by tauto), h.za,
        h.primeB, hcop b h.primeB (by tauto),
        h.primeC, hcop c h.primeC (by tauto),
        h.primeD, hcop d h.primeD (by tauto),
        h.du, h.ab, h.bc, h.cd, h.cw, h.wd⟩, h.crossing⟩
  have hone : pointSieve N p (a * b * c * d) N (b : ℝ) = 1 := by
    apply if_pos
    apply mem_filter.mpr
    refine ⟨mem_range.mpr (Nat.lt_succ_of_le h.indexBound),
      h.primeIndex, h.complement ▸ dvd_refl _, ?_⟩
    rw [h.complement, Nat.div_self
      (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos h.primeA.pos h.primeB.pos)
        h.primeC.pos) h.primeD.pos)]
    intro q hq _ _
    exact hq.not_dvd_one
  unfold pointExcess
  rw [sum_eq_single (a, b, c, d)]
  · exact hone
  · rintro ⟨x, y, r, s⟩ ht hne
    apply pointSieve_zero_of_not_dvd
    intro hd
    obtain ⟨hx, _, _, hy, _, hr, _, hs, _, _, hxy, hyr, hrs, _, _⟩ :=
      mem_s3_second_quadruples.mp (mem_filter.mp ht).1
    exact hne (h.quadruple_unique hx hy hr hs hxy hyr hrs hd)
  · exact fun hnot => (hnot hmem).elim

theorem full_signed_residual_one :
    pointExcess N p z w u V - pointGains N p z w u v = 1 := by
  rw [h.excess_one, h.gains_zero, sub_zero]

theorem moving_positive_tail_pos :
    1 ≤ ∑ y ∈ primeWindow N w u, ∑ x ∈ primeWindow N z w,
      if V ≤ (x : ℝ) * y then pointSieve N p (x * y) N z else 0 := by
  have hcd : c * d ∣ N - p := by
    rw [h.complement, mul_assoc]
    exact dvd_mul_left _ _
  have hc : c ∣ N - p := (h.prime_dvd_iff h.primeC).mpr (by tauto)
  have hd : d ∣ N - p := (h.prime_dvd_iff h.primeD).mpr (by tauto)
  have hac : (a : ℝ) < c := by exact_mod_cast h.ab.trans h.bc
  have hcm : c ∈ primeWindow N z w := mem_primeWindow.mpr
    ⟨h.primeC, h.coprime.of_dvd_left hc, h.za.trans hac.le, h.cw⟩
  have hdm : d ∈ primeWindow N w u := mem_primeWindow.mpr
    ⟨h.primeD, h.coprime.of_dvd_left hd, h.wd, h.du⟩
  have hQ : pointSieve N p (c * d) N z = 1 := by
    apply if_pos
    apply mem_filter.mpr
    refine ⟨mem_range.mpr (Nat.lt_succ_of_le h.indexBound), h.primeIndex, hcd, ?_⟩
    intro q hq hqN hqz hqd
    exact (mem_sieveCarrier_one.mp h.sifted_z).2.2 q hq hqN hqz
      (hqd.trans (Nat.div_dvd_of_dvd hcd))
  have hnonneg : ∀ x y : ℕ,
      0 ≤ (if V ≤ (x : ℝ) * y then pointSieve N p (x * y) N z else 0) := by
    intro x y
    split_ifs
    · exact pointSieve_nonneg _ _ _ _ _
    · exact le_rfl
  calc
    1 = if V ≤ (c : ℝ) * d then pointSieve N p (c * d) N z else 0 := by
      rw [if_pos h.crossing, hQ]
    _ ≤ ∑ x ∈ primeWindow N z w,
        if V ≤ (x : ℝ) * d then pointSieve N p (x * d) N z else 0 :=
      single_le_sum (fun x _ => hnonneg x d) hcm
    _ ≤ _ := single_le_sum (fun y _ => sum_nonneg (fun x _ => hnonneg x y)) hdm

end FourFactorShape

end Wu18938Campaign.M1
