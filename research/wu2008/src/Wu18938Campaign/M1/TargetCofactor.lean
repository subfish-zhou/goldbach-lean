import Wu18938Campaign.M1.TargetFourFactor

namespace Wu18938Campaign.M1

open Finset Wu2008DoubleSieve WuPaper.R2Mother
open scoped Classical

noncomputable def targetExcessTuples (N : ℕ) : Finset (ℕ × ℕ × ℕ × ℕ) :=
  s3Upsilon11Excess N ((N : ℝ) ^ (100 / 1327 : ℝ))
    ((N : ℝ) ^ (25 / 206 : ℝ))
    ((N : ℝ) ^ (1 / 2 - 3 * (100 / 1327 : ℝ)))
    ((N : ℝ) ^ (1 / 2 - 2 * (100 / 1327 : ℝ)))

theorem target_excess_product_geometry {N a b c d : ℕ} (hN : 1 ≤ N)
    (ht : (a, b, c, d) ∈ targetExcessTuples N) :
    (N : ℝ) ^ (1 / 2 : ℝ) ≤ (a * b * c * d : ℕ) ∧
      (b : ℝ) < (N : ℝ) ^ (1 / 3 : ℝ) ∧
      (a * b * c * d).Coprime N := by
  obtain ⟨ht, hcd⟩ := mem_filter.mp ht
  obtain ⟨ha, haN, hza, hb, hbN, hc, hcN, hd, hdN, _, hab, hbc, _, hcw, _⟩ :=
    mem_s3_second_quadruples.mp ht
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have habR : (a : ℝ) ≤ b := by exact_mod_cast hab.le
  have hz0 : 0 ≤ (N : ℝ) ^ (100 / 1327 : ℝ) := Real.rpow_nonneg hN0.le _
  have hablo :
      ((N : ℝ) ^ (100 / 1327 : ℝ)) ^ 2 ≤ (a : ℝ) * b := by
    rw [pow_two]
    exact mul_le_mul hza (hza.trans habR) hz0 (Nat.cast_nonneg a)
  have hprod :
      ((N : ℝ) ^ (100 / 1327 : ℝ)) ^ 2 *
        (N : ℝ) ^ (1 / 2 - 2 * (100 / 1327 : ℝ)) ≤
      (a : ℝ) * b * (c * d) :=
    mul_le_mul hablo hcd (Real.rpow_nonneg hN0.le _) (by positivity)
  have he :
      ((N : ℝ) ^ (100 / 1327 : ℝ)) ^ 2 *
        (N : ℝ) ^ (1 / 2 - 2 * (100 / 1327 : ℝ)) =
        (N : ℝ) ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le, ← Real.rpow_add hN0]
    congr 1
    norm_num
  refine ⟨?_, ?_, ?_⟩
  · rw [he] at hprod
    simpa only [Nat.cast_mul, mul_assoc] using hprod
  · have hbcR : (b : ℝ) < c := by exact_mod_cast hbc
    exact (hbcR.trans hcw).trans_le
      (Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num : (25 / 206 : ℝ) ≤ 1 / 3))
  · exact ((haN.mul_left hbN).mul_left hcN).mul_left hdN

theorem target_excess_quotient_lt_sqrt {N p a b c d : ℕ} (hN : 4 ≤ N)
    (he : Even N) (ht : (a, b, c, d) ∈ targetExcessTuples N)
    (hp : p.Prime) (hpN : p ≤ N) (hd : a * b * c * d ∣ N - p) :
    0 < (N - p) / (a * b * c * d) ∧
      (((N - p) / (a * b * c * d) : ℕ) : ℝ) < (N : ℝ) ^ (1 / 2 : ℝ) := by
  have hn := complement_pos_of_even hN he hpN hp
  have hD := (target_excess_product_geometry (by omega) ht).1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hroot := Real.rpow_pos_of_pos hN0 (1 / 2 : ℝ)
  have hD0 : 0 < a * b * c * d := by exact_mod_cast hroot.trans_le hD
  have hq0 := Nat.div_pos (Nat.le_of_dvd hn hd) hD0
  have hmul : ((a * b * c * d : ℕ) : ℝ) *
      ((N - p) / (a * b * c * d) : ℕ) = (N - p : ℕ) := by
    exact_mod_cast Nat.mul_div_cancel' hd
  have hnlt : ((N - p : ℕ) : ℝ) < N := by
    exact_mod_cast Nat.sub_lt (by omega : 0 < N) hp.pos
  have hsq : ((N : ℝ) ^ (1 / 2 : ℝ)) ^ 2 = N := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
    norm_num
  refine ⟨hq0, ?_⟩
  by_contra h
  have hq := le_of_not_gt h
  have hle := mul_le_mul hD hq hroot.le (Nat.cast_nonneg _)
  rw [← pow_two, hsq, hmul] at hle
  linarith

theorem target_vrough_cofactor {N p a b c d : ℕ} (hN : 4 ≤ N)
    (he : Even N) (ht : (a, b, c, d) ∈ targetExcessTuples N)
    (hp : p ∈ sieveCarrier N (a * b * c * d) N ((N : ℝ) ^ (1 / 3 : ℝ)))
    (hcop : (N - p).Coprime N) :
    (N - p) / (a * b * c * d) = 1 ∨
      (((N - p) / (a * b * c * d)).Prime ∧
        (N : ℝ) ^ (1 / 3 : ℝ) ≤ (((N - p) / (a * b * c * d) : ℕ) : ℝ)) := by
  obtain ⟨hpr, hpp, hd, hs⟩ := mem_filter.mp hp
  have hpN : p ≤ N := by have := mem_range.mp hpr; omega
  obtain ⟨hq0, hqhi⟩ := target_excess_quotient_lt_sqrt hN he ht hpp hpN hd
  let r := (N - p) / (a * b * c * d)
  have hrough : ∀ q : ℕ, q.Prime → q ∣ r →
      (N : ℝ) ^ (1 / 3 : ℝ) ≤ (q : ℝ) := by
    intro q hq hqd
    have hqn := hqd.trans (Nat.div_dvd_of_dvd hd)
    exact le_of_not_gt (fun hlt => hs q hq (hcop.of_dvd_left hqn) hlt hqd)
  by_cases hr1 : r = 1
  · exact Or.inl hr1
  have hrp : r.Prime := by
    by_contra hnp
    have hmin := hrough r.minFac (Nat.minFac_prime hr1) (Nat.minFac_dvd r)
    have hsq : ((r.minFac : ℕ) : ℝ) ^ 2 ≤ (r : ℝ) := by
      exact_mod_cast Nat.minFac_sq_le_self hq0 hnp
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hroot :
        (N : ℝ) ^ (1 / 2 : ℝ) ≤ ((N : ℝ) ^ (1 / 3 : ℝ)) ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
      apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ N by omega))
      norm_num
    have hminsq := (sq_le_sq₀ (Real.rpow_nonneg hN0.le _) (Nat.cast_nonneg r.minFac)).mpr hmin
    exact (not_lt_of_ge ((hroot.trans hminsq).trans hsq)) hqhi
  exact Or.inr ⟨hrp, hrough r hrp (dvd_refl r)⟩

noncomputable def targetUnitCarrier (N D : ℕ) : Finset ℕ :=
  (range (N + 1)).filter (fun p => p.Prime ∧ N - p = D)

noncomputable def targetPrimeCofactorCarrier (N D : ℕ) : Finset ℕ :=
  (range (N + 1)).filter (fun p =>
    p.Prime ∧ D ∣ N - p ∧ (N - p).Coprime N ∧
      ((N - p) / D).Prime ∧ (N : ℝ) ^ (1 / 3 : ℝ) ≤ (((N - p) / D : ℕ) : ℝ))

theorem target_rough_carrier_partition {N a b c d : ℕ} (hN : 4 ≤ N)
    (he : Even N) (ht : (a, b, c, d) ∈ targetExcessTuples N) :
    sieveCarrier N (a * b * c * d) N ((N : ℝ) ^ (1 / 3 : ℝ)) =
      (targetUnitCarrier N (a * b * c * d) ∪
        targetPrimeCofactorCarrier N (a * b * c * d)) ∪
      (sieveCarrier N (a * b * c * d) N ((N : ℝ) ^ (1 / 3 : ℝ))).filter
        (fun p => ¬(N - p).Coprime N) := by
  have hgeom := target_excess_product_geometry (by omega) ht
  have hD0 : 0 < a * b * c * d := by
    have hpow := Real.rpow_pos_of_pos
      (by exact_mod_cast (show 0 < N by omega) : (0 : ℝ) < N) (1 / 2 : ℝ)
    exact_mod_cast hpow.trans_le hgeom.1
  ext p
  constructor
  · intro hp
    by_cases hcop : (N - p).Coprime N
    · obtain hunit | hprime := target_vrough_cofactor hN he ht hp hcop
      · apply mem_union_left
        apply mem_union_left
        obtain ⟨hpr, hpp, hd, _⟩ := mem_filter.mp hp
        have hmul := Nat.mul_div_cancel' hd
        rw [hunit, mul_one] at hmul
        exact mem_filter.mpr ⟨hpr, hpp, hmul.symm⟩
      · apply mem_union_left
        apply mem_union_right
        obtain ⟨hpr, hpp, hd, _⟩ := mem_filter.mp hp
        exact mem_filter.mpr ⟨hpr, hpp, hd, hcop, hprime⟩
    · exact mem_union_right _ (mem_filter.mpr ⟨hp, hcop⟩)
  · intro hp
    rcases mem_union.mp hp with hp | hp
    · rcases mem_union.mp hp with hp | hp
      · obtain ⟨hpr, hpp, hunit⟩ := mem_filter.mp hp
        refine mem_filter.mpr ⟨hpr, hpp, hunit ▸ dvd_refl _, ?_⟩
        rw [hunit, Nat.div_self hD0]
        exact fun q hq _ _ => hq.not_dvd_one
      · obtain ⟨hpr, hpp, hd, _, hq, hcut⟩ := mem_filter.mp hp
        exact mem_filter.mpr ⟨hpr, hpp, hd, sifted_prime_of_le hq hcut⟩
    · exact (mem_filter.mp hp).1

theorem target_rough_count_partition {N a b c d : ℕ} (hN : 4 ≤ N)
    (he : Even N) (ht : (a, b, c, d) ∈ targetExcessTuples N) :
    sieveCount N (a * b * c * d) N ((N : ℝ) ^ (1 / 3 : ℝ)) =
      ((targetUnitCarrier N (a * b * c * d)).card : ℤ) +
      ((targetPrimeCofactorCarrier N (a * b * c * d)).card : ℤ) +
      (((sieveCarrier N (a * b * c * d) N ((N : ℝ) ^ (1 / 3 : ℝ))).filter
        (fun p => ¬(N - p).Coprime N)).card : ℤ) := by
  have hD := (target_excess_product_geometry (by omega) ht).2.2
  have hdis : Disjoint (targetUnitCarrier N (a * b * c * d))
      (targetPrimeCofactorCarrier N (a * b * c * d)) := by
    apply disjoint_left.mpr
    intro p hu hp
    have heq := (mem_filter.mp hu).2.2
    have hprime := (mem_filter.mp hp).2.2.2.2.1
    have hpos := complement_pos_of_even hN he
      (by have := mem_range.mp (mem_filter.mp hu).1; omega) (mem_filter.mp hu).2.1
    rw [heq, Nat.div_self (heq ▸ hpos)] at hprime
    exact Nat.not_prime_one hprime
  have hbad : Disjoint
      (targetUnitCarrier N (a * b * c * d) ∪ targetPrimeCofactorCarrier N (a * b * c * d))
      ((sieveCarrier N (a * b * c * d) N ((N : ℝ) ^ (1 / 3 : ℝ))).filter
        (fun p => ¬(N - p).Coprime N)) := by
    apply disjoint_left.mpr
    intro p hp hb
    have hn := (mem_filter.mp hb).2
    rcases mem_union.mp hp with hu | hp
    · exact hn ((mem_filter.mp hu).2.2.symm ▸ hD)
    · exact hn (mem_filter.mp hp).2.2.2.1
  unfold sieveCount
  nth_rw 1 [target_rough_carrier_partition hN he ht]
  rw [card_union_of_disjoint hbad,
    card_union_of_disjoint hdis, Nat.cast_add, Nat.cast_add]

theorem target_excess_buchstab_prime_remainder {N : ℕ} (hN : 4 ≤ N) (he : Even N) :
    quotientExcess N ((N : ℝ) ^ (100 / 1327 : ℝ))
        ((N : ℝ) ^ (25 / 206 : ℝ))
        ((N : ℝ) ^ (1 / 2 - 3 * (100 / 1327 : ℝ)))
        ((N : ℝ) ^ (1 / 2 - 2 * (100 / 1327 : ℝ))) =
      ∑ t ∈ targetExcessTuples N,
        (((targetUnitCarrier N (t.1 * t.2.1 * t.2.2.1 * t.2.2.2)).card : ℤ) +
        ((targetPrimeCofactorCarrier N (t.1 * t.2.1 * t.2.2.1 * t.2.2.2)).card : ℤ) +
        (((sieveCarrier N (t.1 * t.2.1 * t.2.2.1 * t.2.2.2) N
          ((N : ℝ) ^ (1 / 3 : ℝ))).filter (fun p => ¬(N - p).Coprime N)).card : ℤ) +
        ∑ q ∈ primeWindow N (t.2.1 : ℝ) ((N : ℝ) ^ (1 / 3 : ℝ)),
          sieveCount N (t.1 * t.2.1 * t.2.2.1 * t.2.2.2 * q) N (q : ℝ)) := by
  apply sum_congr rfl
  rintro ⟨a, b, c, d⟩ ht
  have hcut := (target_excess_product_geometry (by omega) ht).2.1.le
  have h := goldbach_buchstab N (a * b * c * d) N hcut
  rw [target_rough_count_partition hN he ht] at h
  change sieveCount N (a * b * c * d) N (b : ℝ) = _
  dsimp only
  omega

end Wu18938Campaign.M1
