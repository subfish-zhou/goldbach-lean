import Wu18938Campaign.M1.TargetCofactor
import MathlibNt.Wu2008DoubleSieve.Omega3Multiplicity

namespace Wu18938Campaign.M1

open Finset Wu2008DoubleSieve WuPaper.R2Mother
open scoped Classical

theorem target_unit_shape {N p a b c d : ℕ} (hN : 1 ≤ N)
    (ht : (a, b, c, d) ∈ targetExcessTuples N)
    (hp : p ∈ targetUnitCarrier N (a * b * c * d)) :
    FourFactorShape N p a b c d
      ((N : ℝ) ^ (100 / 1327 : ℝ)) ((N : ℝ) ^ (25 / 206 : ℝ))
      ((N : ℝ) ^ (1 / 2 - 3 * (100 / 1327 : ℝ))) ((N : ℝ) ^ (1 / 3 : ℝ))
      ((N : ℝ) ^ (1 / 2 - 2 * (100 / 1327 : ℝ))) := by
  obtain ⟨htr, hcross⟩ := mem_filter.mp ht
  obtain ⟨ha, haN, hza, hb, hbN, hc, hcN, hd, hdN, hdu, hab, hbc, hcd, hcw, hwd⟩ :=
    mem_s3_second_quadruples.mp htr
  obtain ⟨hpr, hpp, hprod⟩ := mem_filter.mp hp
  exact {
    primeIndex := hpp
    indexBound := by have := mem_range.mp hpr; omega
    complement := hprod
    primeA := ha
    primeB := hb
    primeC := hc
    primeD := hd
    coprime := hprod.symm ▸ ((haN.mul_left hbN).mul_left hcN).mul_left hdN
    ab := hab
    bc := hbc
    cd := hcd
    za := hza
    cw := hcw
    wd := hwd
    du := hdu
    uv := Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) (by norm_num)
    crossing := hcross
  }

theorem target_unit_mass_le_fourFactor_card {N : ℕ} (hN : 1 ≤ N) :
    (∑ t ∈ targetExcessTuples N,
      ((targetUnitCarrier N (t.1 * t.2.1 * t.2.2.1 * t.2.2.2)).card : ℝ)) ≤
    ((fourFactorIndices N ((N : ℝ) ^ (100 / 1327 : ℝ))
      ((N : ℝ) ^ (25 / 206 : ℝ)) ((N : ℝ) ^ (1 / 2 - 3 * (100 / 1327 : ℝ)))
      ((N : ℝ) ^ (1 / 3 : ℝ)) ((N : ℝ) ^ (1 / 2 - 2 * (100 / 1327 : ℝ)))).card : ℝ) := by
  let F := fourFactorIndices N ((N : ℝ) ^ (100 / 1327 : ℝ))
    ((N : ℝ) ^ (25 / 206 : ℝ)) ((N : ℝ) ^ (1 / 2 - 3 * (100 / 1327 : ℝ)))
    ((N : ℝ) ^ (1 / 3 : ℝ)) ((N : ℝ) ^ (1 / 2 - 2 * (100 / 1327 : ℝ)))
  have hsub : ∀ t ∈ targetExcessTuples N,
      targetUnitCarrier N (t.1 * t.2.1 * t.2.2.1 * t.2.2.2) ⊆ F := by
    rintro ⟨a, b, c, d⟩ ht p hp
    exact mem_filter.mpr ⟨(mem_filter.mp hp).1, a, b, c, d, target_unit_shape hN ht hp⟩
  rw [endpoint_sum_cards_eq (targetExcessTuples N) F _ hsub]
  calc
    _ ≤ ∑ _p ∈ F, (1 : ℝ) := by
      apply sum_le_sum
      intro p _
      apply Nat.cast_le_one.mpr
      apply card_le_one.mpr
      rintro ⟨a, b, c, d⟩ ht ⟨x, y, r, s⟩ hu
      obtain ⟨ht, hp⟩ := mem_filter.mp ht
      obtain ⟨hu, hpu⟩ := mem_filter.mp hu
      have hshape := target_unit_shape hN ht hp
      obtain ⟨hx, _, _, hy, _, hr, _, hs, _, _, hxy, hyr, hrs, _, _⟩ :=
        mem_s3_second_quadruples.mp (mem_filter.mp hu).1
      exact (hshape.quadruple_unique hx hy hr hs hxy hyr hrs
        ((mem_filter.mp hpu).2.2 ▸ dvd_refl _)).symm
    _ = _ := by simp [F]

theorem target_unit_mass_paid {N : ℕ} (hN : 1 ≤ N) :
    (∑ t ∈ targetExcessTuples N,
      ((targetUnitCarrier N (t.1 * t.2.1 * t.2.2.1 * t.2.2.2)).card : ℝ)) ≤
      2 * (N : ℝ) ^ (1 - (100 / 1327 : ℝ)) := by
  have h := source_fourFactor_residual_paid hN
    target_fourFactor_geometry.2.2.2.2.1 target_fourFactor_geometry.2.2.2.2.2
  dsimp only at h
  rw [fourFactor_residual_sum, Int.cast_natCast] at h
  exact (target_unit_mass_le_fourFactor_card hN).trans h

private def slots (t : ℕ × ℕ × ℕ × ℕ) : Fin 4 → ℕ :=
  ![t.1, t.2.1, t.2.2.1, t.2.2.2]

private theorem slots_injective : Function.Injective slots := by
  rintro ⟨a, b, c, d⟩ ⟨x, y, r, s⟩ h
  have ha := congrFun h 0
  have hb := congrFun h 1
  have hc := congrFun h 2
  have hd := congrFun h 3
  simp only [slots, Matrix.cons_val_zero] at ha hb hc hd
  exact Prod.ext ha (Prod.ext hb (Prod.ext hc hd))

private theorem target_slots {N a b c d p : ℕ}
    (ht : (a, b, c, d) ∈ targetExcessTuples N)
    (hD : a * b * c * d ∣ N - p) :
    ∀ j : Fin 4, (slots (a, b, c, d) j).Prime ∧
      slots (a, b, c, d) j ∣ N - p ∧
      (N : ℝ) ^ (100 / 1327 : ℝ) ≤ (slots (a, b, c, d) j : ℝ) := by
  obtain ⟨ha, _, hza, hb, _, hc, _, hd, _, _, hab, hbc, hcd, _, _⟩ :=
    mem_s3_second_quadruples.mp (mem_filter.mp ht).1
  have hzb := hza.trans (by exact_mod_cast hab.le : (a : ℝ) ≤ b)
  have hzc := hzb.trans (by exact_mod_cast hbc.le : (b : ℝ) ≤ c)
  have hzd := hzc.trans (by exact_mod_cast hcd.le : (c : ℝ) ≤ d)
  have hda : a ∣ N - p :=
    (dvd_mul_right a b).trans ((dvd_mul_right (a * b) c).trans
      ((dvd_mul_right (a * b * c) d).trans hD))
  have hdb : b ∣ N - p :=
    (dvd_mul_left b a).trans ((dvd_mul_right (a * b) c).trans
      ((dvd_mul_right (a * b * c) d).trans hD))
  have hdc : c ∣ N - p :=
    (dvd_mul_left c (a * b)).trans ((dvd_mul_right (a * b * c) d).trans hD)
  have hdd : d ∣ N - p := (dvd_mul_left d (a * b * c)).trans hD
  simp only [slots, Fin.forall_fin_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Fin.forall_fin_zero, and_true]
  exact ⟨⟨ha, hda, hza⟩, ⟨hb, hdb, hzb⟩, ⟨hc, hdc, hzc⟩, hd, hdd, hzd⟩

theorem target_bad_cofactor_mass_le {N : ℕ} (hN : 4 ≤ N) (he : Even N) :
    (∑ t ∈ targetExcessTuples N,
      (((sieveCarrier N (t.1 * t.2.1 * t.2.2.1 * t.2.2.2) N
        ((N : ℝ) ^ (1 / 3 : ℝ))).filter (fun p => ¬(N - p).Coprime N)).card : ℝ)) ≤
      (1327 / 100 : ℝ) ^ 4 * (Real.sqrt N + 1) := by
  let f := fun t : ℕ × ℕ × ℕ × ℕ =>
    (sieveCarrier N (t.1 * t.2.1 * t.2.2.1 * t.2.2.2) N
      ((N : ℝ) ^ (1 / 3 : ℝ))).filter (fun p => ¬(N - p).Coprime N)
  have hsub : ∀ t ∈ targetExcessTuples N, f t ⊆ N.primeFactors := by
    intro t _ p hp
    obtain ⟨hp, hcop⟩ := mem_filter.mp hp
    obtain ⟨hpr, hpp, _⟩ := mem_filter.mp hp
    have hpN : p ≤ N := by have := mem_range.mp hpr; omega
    exact Nat.mem_primeFactors.mpr
      ⟨hpp, prime_dvd_of_complement_not_coprime hpN hpp hcop, by omega⟩
  rw [endpoint_sum_cards_eq (targetExcessTuples N) N.primeFactors f hsub]
  calc
    _ ≤ ∑ _p ∈ N.primeFactors, (1327 / 100 : ℝ) ^ 4 := by
      apply sum_le_sum
      intro p hp
      have hpp := (Nat.mem_primeFactors.mp hp).1
      have hpN := Nat.le_of_dvd (by omega : 0 < N) (Nat.mem_primeFactors.mp hp).2.1
      have hn := complement_pos_of_even hN he hpN hpp
      have h := omega3_prime_labels_card_le
        ((targetExcessTuples N).filter (fun t => p ∈ f t)) slots
        slots_injective.injOn (by omega : 1 < N) hn (Nat.sub_le N p)
        (by norm_num : (0 : ℝ) < 100 / 1327) (by
          rintro ⟨a, b, c, d⟩ ht
          obtain ⟨ht, hp⟩ := mem_filter.mp ht
          exact target_slots ht (mem_filter.mp (mem_filter.mp hp).1).2.2.1)
      convert! h using 1
      norm_num
    _ = (1327 / 100 : ℝ) ^ 4 * N.primeFactors.card := by simp [mul_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_left (primeFactors_card_le_sqrt_add_one N) (by positivity)

theorem target_bad_cofactor_mass_paid {N : ℕ} (hN : 4 ≤ N) (he : Even N) :
    (∑ t ∈ targetExcessTuples N,
      (((sieveCarrier N (t.1 * t.2.1 * t.2.2.1 * t.2.2.2) N
        ((N : ℝ) ^ (1 / 3 : ℝ))).filter (fun p => ¬(N - p).Coprime N)).card : ℝ)) ≤
      2 * (1327 / 100 : ℝ) ^ 4 * (N : ℝ) ^ (1 - (100 / 1327 : ℝ)) := by
  have hbase : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hs : Real.sqrt N ≤ (N : ℝ) ^ (1 - (100 / 1327 : ℝ)) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hbase (by norm_num)
  have hone : 1 ≤ (N : ℝ) ^ (1 - (100 / 1327 : ℝ)) :=
    Real.one_le_rpow hbase (by norm_num)
  have h := target_bad_cofactor_mass_le hN he
  nlinarith

theorem target_excess_nonunit_paid {N : ℕ} (hN : 4 ≤ N) (he : Even N) :
    (quotientExcess N ((N : ℝ) ^ (100 / 1327 : ℝ))
        ((N : ℝ) ^ (25 / 206 : ℝ))
        ((N : ℝ) ^ (1 / 2 - 3 * (100 / 1327 : ℝ)))
        ((N : ℝ) ^ (1 / 2 - 2 * (100 / 1327 : ℝ))) : ℝ) ≤
      (∑ t ∈ targetExcessTuples N,
        ((targetPrimeCofactorCarrier N (t.1 * t.2.1 * t.2.2.1 * t.2.2.2)).card : ℝ)) +
      ((∑ t ∈ targetExcessTuples N,
        ∑ q ∈ primeWindow N (t.2.1 : ℝ) ((N : ℝ) ^ (1 / 3 : ℝ)),
          sieveCount N (t.1 * t.2.1 * t.2.2.1 * t.2.2.2 * q) N (q : ℝ) : ℤ) : ℝ) +
      (2 + 2 * (1327 / 100 : ℝ) ^ 4) * (N : ℝ) ^ (1 - (100 / 1327 : ℝ)) := by
  have hunit := target_unit_mass_paid (by omega : 1 ≤ N)
  have hbad := target_bad_cofactor_mass_paid hN he
  rw [target_excess_buchstab_prime_remainder hN he]
  push_cast
  simp only [sum_add_distrib] at *
  linarith

end Wu18938Campaign.M1
