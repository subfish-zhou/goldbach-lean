import MathlibNt.Wu2008DoubleSieve.LowerWeights

/-!
# Wu's lower weight on actual Goldbach indices

The squarefree pointwise inequality is summed without changing the prime
index carrier. Common-factor and zero exceptions are explicit, as is the
uniform prime-square budget. Source: Wu (2004), proof of Lemma 9.1;
Wu (2008), Lemma 2.1.
-/

namespace Wu2008DoubleSieve

open Finset
open scoped Classical ArithmeticFunction.Omega

theorem mem_sieveCarrier_one {N p : ℕ} {z : ℝ} :
    p ∈ sieveCarrier N 1 N z ↔ p ≤ N ∧ p.Prime ∧ Sifted N (N - p) z := by
  simp only [sieveCarrier, mem_filter, mem_range, Nat.lt_succ_iff,
    one_dvd, Nat.div_one, true_and]

theorem lower_pair_carrier (N : ℕ) {a b : ℕ} {z : ℝ}
    (ha : a.Prime) (hb : b.Prime) (hza : z ≤ (a : ℝ)) (hab : a < b) :
    (sieveCarrier N 1 N z).filter (fun p => lowerPairSurvives N (N - p) (a, b)) =
      sieveCarrier N (a * b) (N * a) (b : ℝ) := by
  ext p
  simp only [sieveCarrier, mem_filter, mem_range, Nat.lt_succ_iff,
    one_dvd, Nat.div_one, true_and, lowerPairSurvives]
  constructor
  · rintro ⟨⟨hpN, hp, _⟩, hd, hs⟩
    exact ⟨hpN, hp, hd, hs⟩
  · rintro ⟨hpN, hp, hd, hs⟩
    refine ⟨⟨hpN, hp, ?_⟩, hd, hs⟩
    intro q hq hqN hqz hqn
    have hqa : q ≠ a := by
      intro he
      subst q
      exact (not_lt_of_ge hza) hqz
    have hqab := hqz.trans_le hza
    have hqb : (q : ℝ) < b := hqab.trans (by exact_mod_cast hab)
    have hqac := (Nat.coprime_primes hq ha).mpr hqa
    have hqbc := (Nat.coprime_primes hq hb).mpr (by
      have : q < b := by exact_mod_cast hqb
      omega)
    exact hs q hq (Nat.coprime_mul_iff_right.mpr ⟨hqN, hqac⟩) hqb
      ((dvd_quotient_iff hd (Nat.coprime_mul_iff_right.mpr ⟨hqac, hqbc⟩)).mpr hqn)

theorem lowerPairPenalty_sum (N : ℕ) (z w : ℝ) :
    (∑ p ∈ sieveCarrier N 1 N z, lowerPairPenalty N N (N - p) z w) =
      ∑ t ∈ lowerPairs N N z w,
        (if w ≤ (t.1 : ℝ) then 2 else 1) *
          sieveCount N (t.1 * t.2) (N * t.1) (t.2 : ℝ) := by
  unfold lowerPairPenalty
  rw [sum_comm]
  apply sum_congr rfl
  rintro ⟨a, b⟩ ht
  obtain ⟨hwin, hab, _⟩ := mem_filter.mp ht
  obtain ⟨hwa, hwb⟩ := mem_product.mp hwin
  obtain ⟨ha, _, hza, _⟩ := mem_primeWindow.mp hwa
  obtain ⟨hb, _, _, _⟩ := mem_primeWindow.mp hwb
  rw [sieveCount, ← lower_pair_carrier N ha hb hza hab, ← sum_boole, mul_sum]
  apply sum_congr rfl
  intro p _
  split_ifs <;> simp

theorem lowerWeight_sum_eq (N : ℕ) (z w : ℝ) :
    (∑ p ∈ sieveCarrier N 1 N z, lowerWeight N N (N - p) z w) =
      2 * sieveCount N 1 N z -
        (∑ q ∈ primeWindow N z w, sieveCount N q N z) -
        (∑ t ∈ lowerPairs N N z w,
          (if w ≤ (t.1 : ℝ) then 2 else 1) *
            sieveCount N (t.1 * t.2) (N * t.1) (t.2 : ℝ)) +
        ∑ t ∈ orderedTriples (primeWindow N z w),
          sieveCount N (t.1 * t.2.1 * t.2.2) (N * t.1) (t.2.1 : ℝ) := by
  simp only [lowerWeight, sum_sub_distrib, sum_add_distrib]
  have hs := singleMass_sieveCarrier N 1 N z w
  have ht := tripleMass_sieveCarrier N 1 N z w
  rw [singleMass_eq_sum] at hs
  rw [tripleMass_eq_sum] at ht
  simp only [Nat.div_one, one_mul] at hs ht
  rw [hs, ht, lowerPairPenalty_sum]
  simp only [sum_const, nsmul_eq_mul, sieveCount]
  ring

/-- All noncoprime prime indices lie among the prime divisors of `N`. -/
theorem prime_dvd_of_complement_not_coprime {N p : ℕ}
    (hpN : p ≤ N) (hp : p.Prime) (hc : ¬(N - p).Coprime N) :
    p ∣ N := by
  by_contra hd
  have hcop := (hp.coprime_iff_not_dvd).mpr hd
  apply hc
  have h := hcop.symm
  rw [← Nat.coprime_sub_self_right (Nat.sub_le N p), Nat.sub_sub_self hpN,
    Nat.coprime_sub_self_left hpN]
  exact h

/-- The prime divisor count has an elementary square-root bound. -/
theorem primeFactors_card_le_sqrt_add_one (N : ℕ) :
    (N.primeFactors.card : ℝ) ≤ Real.sqrt N + 1 := by
  let small := N.primeFactors.filter (fun p : ℕ => (p : ℝ) ≤ Real.sqrt N)
  let large := N.primeFactors.filter (fun p : ℕ => ¬(p : ℝ) ≤ Real.sqrt N)
  have hs : small.card ≤ ⌊Real.sqrt N⌋₊ := by
    calc
      small.card ≤ (Ioc 0 ⌊Real.sqrt N⌋₊).card := by
        apply card_le_card
        intro p hp
        obtain ⟨hp, hps⟩ := mem_filter.mp hp
        exact mem_Ioc.mpr ⟨(Nat.mem_primeFactors.mp hp).1.pos, Nat.le_floor hps⟩
      _ = ⌊Real.sqrt N⌋₊ := by simp
  have hl : large.card ≤ 1 := by
    apply card_le_one.mpr
    intro p hp q hq
    obtain ⟨hp, hps⟩ := mem_filter.mp hp
    obtain ⟨hq, hqs⟩ := mem_filter.mp hq
    obtain ⟨hpp, hpd, hN⟩ := Nat.mem_primeFactors.mp hp
    obtain ⟨hqp, hqd, _⟩ := Nat.mem_primeFactors.mp hq
    by_contra hpq
    have hd := ((Nat.coprime_primes hpp hqp).mpr hpq).mul_dvd_of_dvd_of_dvd hpd hqd
    have hle : (p : ℝ) * q ≤ N := by
      exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hN) hd
    have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ N by positivity)
    have hpos := Real.sqrt_nonneg (N : ℝ)
    have hpS : Real.sqrt N < (p : ℝ) := lt_of_not_ge hps
    have hqS : Real.sqrt N < (q : ℝ) := lt_of_not_ge hqs
    have hprod : Real.sqrt N * Real.sqrt N < (p : ℝ) * q := by
      nlinarith [mul_pos (sub_pos.mpr hpS) (sub_pos.mpr hqS),
        mul_nonneg hpos (sub_nonneg.mpr hpS.le),
        mul_nonneg hpos (sub_nonneg.mpr hqS.le)]
    nlinarith
  have he := card_filter_add_card_filter_not (s := N.primeFactors)
    (fun p => (p : ℝ) ≤ Real.sqrt N)
  have hf := Nat.floor_le (Real.sqrt_nonneg (N : ℝ))
  have hsc : (small.card : ℝ) ≤ Real.sqrt N :=
    (by exact_mod_cast hs : (small.card : ℝ) ≤ ⌊Real.sqrt N⌋₊).trans hf
  have hlc : (large.card : ℝ) ≤ 1 := by exact_mod_cast hl
  have hec : (small.card : ℝ) + large.card = N.primeFactors.card := by
    exact_mod_cast he
  linarith

noncomputable def exceptionalGoldbach (N : ℕ) (z : ℝ) : Finset ℕ :=
  (sieveCarrier N 1 N z).filter
    (fun p => ¬(0 < N - p ∧ (N - p).Coprime N))

theorem exceptionalGoldbach_card_le {N : ℕ} (hN : 0 < N) (z : ℝ) :
    ((exceptionalGoldbach N z).card : ℝ) ≤ Real.sqrt N + 1 := by
  have hsub : exceptionalGoldbach N z ⊆ N.primeFactors := by
    intro p hp
    obtain ⟨hp, he⟩ := mem_filter.mp hp
    obtain ⟨hpN, hpp, _⟩ := mem_sieveCarrier_one.mp hp
    apply Nat.mem_primeFactors.mpr
    refine ⟨hpp, ?_, Nat.ne_of_gt hN⟩
    by_cases hn : 0 < N - p
    · exact prime_dvd_of_complement_not_coprime hpN hpp (by tauto)
    · have : p = N := by omega
      subst p
      exact dvd_rfl
  exact (by exact_mod_cast card_le_card hsub :
    ((exceptionalGoldbach N z).card : ℝ) ≤ N.primeFactors.card).trans
      (primeFactors_card_le_sqrt_add_one N)

/-- The actual lower weight with every exceptional prime index paid explicitly.
No parity, distribution, or numerical sieve estimate is a premise. -/
theorem lowerWeight_goldbach_sum_le {N : ℕ} (hN : 0 < N) {z : ℝ}
    (hz : 2 ≤ z) (w : ℝ) :
    (∑ p ∈ sieveCarrier N 1 N z, (lowerWeight N N (N - p) z w : ℝ)) ≤
      2 * ((MathlibNt.Wu2008DoubleSieve.wuPrimeComplements N).card : ℝ) +
        4 * (N : ℝ) / z + 2 * (Real.sqrt N + 1) := by
  let A := sieveCarrier N 1 N z
  let G := A.filter (fun p => 0 < N - p ∧ (N - p).Coprime N)
  let F := A.filter (fun p =>
    0 < N - p ∧ (N - p).Coprime N ∧ Squarefree (N - p))
  let W := fun p => (lowerWeight N N (N - p) z w : ℝ)
  have hex : ∑ p ∈ exceptionalGoldbach N z, W p ≤ 2 * (Real.sqrt N + 1) := by
    calc
      ∑ p ∈ exceptionalGoldbach N z, W p ≤
          ∑ _p ∈ exceptionalGoldbach N z, (2 : ℝ) := by
        apply sum_le_sum
        intro p _
        dsimp [W]
        exact_mod_cast lowerWeight_le_two N N (N - p) z w
      _ = 2 * ((exceptionalGoldbach N z).card : ℝ) := by simp [mul_comm]
      _ ≤ 2 * (Real.sqrt N + 1) :=
        mul_le_mul_of_nonneg_left (exceptionalGoldbach_card_le hN z) (by norm_num)
  have hsq : (∑ p ∈ G, W p) ≤ (∑ p ∈ F, W p) + 4 * (N : ℝ) / z := by
    exact sifted_goldbach_sum_le_squarefree_sum_add N hz W (fun p _ => by
      dsimp [W]
      exact_mod_cast lowerWeight_le_two N N (N - p) z w)
  have hgood : (∑ p ∈ F, W p) ≤
      2 * ((MathlibNt.Wu2008DoubleSieve.wuPrimeComplements N).card : ℝ) := by
    have hpw : ∀ p ∈ F, W p ≤ if Ω (N - p) ≤ 2 then (2 : ℝ) else 0 := by
      intro p hp
      obtain ⟨hp, _, hc, hs⟩ := mem_filter.mp hp
      have hsp := (mem_sieveCarrier_one.mp hp).2.2
      have h := lowerWeight_le_omega_indicator (N := N) (z := z) (w := w)
        (Nat.sub_le N p) hc hsp hs
      dsimp [W]
      split_ifs at h ⊢ <;> exact_mod_cast h
    have hsub : F.filter (fun p => Ω (N - p) ≤ 2) ⊆
        MathlibNt.Wu2008DoubleSieve.wuPrimeComplements N := by
      intro p hp
      obtain ⟨hp, hΩ⟩ := mem_filter.mp hp
      obtain ⟨hp, hpos, _, _⟩ := mem_filter.mp hp
      obtain ⟨hpN, hpp, _⟩ := mem_sieveCarrier_one.mp hp
      exact MathlibNt.Wu2008DoubleSieve.mem_wuPrimeComplements.mpr
        ⟨hpN, hpp, hpos, hΩ⟩
    calc
      (∑ p ∈ F, W p) ≤ ∑ p ∈ F, if Ω (N - p) ≤ 2 then (2 : ℝ) else 0 :=
        sum_le_sum hpw
      _ = 2 * ((F.filter (fun p => Ω (N - p) ≤ 2)).card : ℝ) := by
        rw [← sum_boole, mul_sum]
        apply sum_congr rfl
        intro p _
        split_ifs <;> norm_num
      _ ≤ 2 * ((MathlibNt.Wu2008DoubleSieve.wuPrimeComplements N).card : ℝ) := by
        exact_mod_cast Nat.mul_le_mul_left 2 (card_le_card hsub)
  have he := sum_filter_add_sum_filter_not A
    (fun p => 0 < N - p ∧ (N - p).Coprime N) W
  change (∑ p ∈ G, W p) + (∑ p ∈ exceptionalGoldbach N z, W p) =
    ∑ p ∈ A, W p at he
  change (∑ p ∈ A, W p) ≤ _
  linarith

/-- The source square-root endpoint is retained exactly, not rounded. -/
theorem lower_pair_size_iff {N a b : ℕ} (ha : 0 < a) :
    a * b ^ 2 < N ↔ (b : ℝ) < Real.sqrt ((N : ℝ) / a) := by
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  rw [Real.lt_sqrt (by positivity), lt_div_iff₀ ha']
  exact_mod_cast (show a * b ^ 2 < N ↔ b ^ 2 * a < N by rw [mul_comm])

noncomputable def lowerS2 (N : ℕ) (z w : ℝ) : ℤ :=
  ∑ t ∈ (lowerPairs N N z w).filter (fun t => w ≤ (t.1 : ℝ)),
    sieveCount N (t.1 * t.2) (N * t.1) (t.2 : ℝ)

noncomputable def lowerS3 (N : ℕ) (z w : ℝ) : ℤ :=
  ∑ t ∈ (lowerPairs N N z w).filter (fun t => (t.1 : ℝ) < w),
    sieveCount N (t.1 * t.2) (N * t.1) (t.2 : ℝ)

noncomputable def lowerWeightRHS (N : ℕ) (z w : ℝ) : ℤ :=
  2 * sieveCount N 1 N z -
    (∑ q ∈ primeWindow N z w, sieveCount N q N z) -
    2 * lowerS2 N z w - lowerS3 N z w +
    ∑ t ∈ orderedTriples (primeWindow N z w),
      sieveCount N (t.1 * t.2.1 * t.2.2) (N * t.1) (t.2.1 : ℝ)

theorem lower_pair_sum_split (N : ℕ) (z w : ℝ) :
    (∑ t ∈ lowerPairs N N z w,
      (if w ≤ (t.1 : ℝ) then 2 else 1) *
        sieveCount N (t.1 * t.2) (N * t.1) (t.2 : ℝ)) =
      2 * lowerS2 N z w + lowerS3 N z w := by
  simp only [lowerS2, lowerS3, sum_filter, mul_sum, ← sum_add_distrib]
  apply sum_congr rfl
  intro t _
  by_cases h : w ≤ (t.1 : ℝ)
  · simp [h, not_lt_of_ge h]
  · simp [h, lt_of_not_ge h]

theorem lowerWeightRHS_eq_sum (N : ℕ) (z w : ℝ) :
    lowerWeightRHS N z w =
      ∑ p ∈ sieveCarrier N 1 N z, lowerWeight N N (N - p) z w := by
  rw [lowerWeight_sum_eq, lower_pair_sum_split]
  unfold lowerWeightRHS
  ring

theorem lowerWeightRHS_le_count_add_explicit_error {N : ℕ} (hN : 0 < N)
    {z : ℝ} (hz : 2 ≤ z) (w : ℝ) :
    (lowerWeightRHS N z w : ℝ) ≤
      2 * ((MathlibNt.Wu2008DoubleSieve.wuPrimeComplements N).card : ℝ) +
        4 * (N : ℝ) / z + 2 * (Real.sqrt N + 1) := by
  rw [lowerWeightRHS_eq_sum, Int.cast_sum]
  exact lowerWeight_goldbach_sum_le hN hz w

theorem lowerWeight_error_le_rpow {N : ℕ} (hN : 0 < N) {κ : ℝ}
    (hκ : κ ≤ 1 / 2) :
    4 * (N : ℝ) / (N : ℝ) ^ κ + 2 * (Real.sqrt N + 1) ≤
      8 * (N : ℝ) ^ (1 - κ) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hs : Real.sqrt N ≤ (N : ℝ) ^ (1 - κ) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have h1 : 1 ≤ (N : ℝ) ^ (1 - κ) := Real.one_le_rpow hN1 (by linarith)
  have he : (N : ℝ) / (N : ℝ) ^ κ = (N : ℝ) ^ (1 - κ) := by
    rw [Real.rpow_sub hN', Real.rpow_one]
  rw [mul_div_assoc, he]
  linarith

/-- Wu08 (2.1) with strict sifting and a proved, absolute error constant.
The full source range includes `sigma = 1/3`; no `3*sigma+kappa > 1`
assumption or unproved asymptotic premise is introduced. -/
theorem wu_lemma21_strict {κ σ : ℝ}
    (hκ : 0 < κ) (hκσ : κ < σ) (hσ : σ ≤ 1 / 3) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      (lowerWeightRHS N ((N : ℝ) ^ κ) ((N : ℝ) ^ σ) : ℝ) -
        8 * (N : ℝ) ^ (1 - κ) ≤
          2 * ((MathlibNt.Wu2008DoubleSieve.wuPrimeComplements N).card : ℝ) := by
  have hz : ∀ᶠ N : ℕ in Filter.atTop, 2 ≤ (N : ℝ) ^ κ :=
    ((tendsto_rpow_atTop hκ).comp tendsto_natCast_atTop_atTop).eventually
      (Filter.eventually_ge_atTop 2)
  apply Filter.eventually_atTop.mp
  filter_upwards [hz, Filter.eventually_ge_atTop (1 : ℕ)] with N hzN hN
  have hl := lowerWeightRHS_le_count_add_explicit_error (by omega : 0 < N)
    hzN ((N : ℝ) ^ σ)
  have he := lowerWeight_error_le_rpow (by omega : 0 < N)
    (by linarith : κ ≤ 1 / 2)
  linarith

end Wu2008DoubleSieve
