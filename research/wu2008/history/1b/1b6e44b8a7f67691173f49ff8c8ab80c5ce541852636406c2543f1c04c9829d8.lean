import MathlibNt.Wu2008DoubleSieve.JointResidualTransport

/-!
# An obstruction to a carrierwise payment in the printed convention

We evaluate the actual eleven-term linear form at one prime index, not
on a replacement sequence. The complement `5 * 7 * 11 * 13 * 101` has
four primes below `w` and its last prime above `v`. Its coefficient is
positive although it is not a representation counted by `D_{1,2}`.
This does not refute an estimate after summing over all prime indices.
-/

namespace Wu2008DoubleSieve

open Finset
open scoped Classical ArithmeticFunction.Omega

noncomputable def jointResidualClosedAtom (N p d M : ℕ) (y : ℝ) : ℤ :=
  if p ∈ sourceSieveCarrierLE N d M y then 1 else 0

theorem jointResidualClosedAtom_sum (N d M : ℕ) (y : ℝ) :
    (∑ p ∈ range (N + 1), jointResidualClosedAtom N p d M y) =
      sourceSieveCountLE N d M y := by
  unfold jointResidualClosedAtom sourceSieveCountLE
  rw [← sum_filter]
  have he : (range (N + 1)).filter (fun p => p ∈ sourceSieveCarrierLE N d M y) =
      sourceSieveCarrierLE N d M y := by
    ext p
    simp only [mem_filter, sourceSieveCarrierLE]
    tauto
  rw [he]
  simp

theorem jointResidual_expression_sum (N : ℕ) (z w u v V : ℝ) :
    finiteElevenExpression N z w u v V (sourceSieveCountLE N)
        (fun d y => sourceSieveCountLE N d N y) =
      ∑ p ∈ range (N + 1),
        finiteElevenExpression N z w u v V (jointResidualClosedAtom N p)
          (fun d y => jointResidualClosedAtom N p d N y) := by
  simp only [finiteElevenExpression, sum_sub_distrib, sum_add_distrib, ← mul_sum]
  simp_rw [sum_comm (s := range (N + 1)), jointResidualClosedAtom_sum]

/-- Exact connection of the atom calculation to `X11 - P - J` in the
accepted consumer. The outer and repeated-prime errors remain literal.
In particular, a positive atom alone does not prove this residual positive. -/
theorem jointResidual_closed_exact (N : ℕ) (z w u v V : ℝ)
    (hzw : z ≤ w) (hwu : w ≤ u) (hwv : w ≤ v) (huv : u ≤ v)
    (hv : 0 ≤ v) (hNv : (N : ℝ) ≤ v ^ 3)
    (hthird : s3ThirdRange N w u ⊆ orderedTriples (primeWindow N z v)) :
    (s3Upsilon11ExcessMass N z w u V : ℝ) -
        finiteAssemblyGains N z w u v V -
        (finiteElevenExpression N z w u v V
          (fun d M y => sieveCount N d M y - sourceSieveCountLE N d M y)
          (fun d y => sourceSieveCount N d (d * N) y - sourceSieveCountLE N d N y) : ℝ) =
      ((∑ p ∈ range (N + 1),
        finiteElevenExpression N z w u v V (jointResidualClosedAtom N p)
          (fun d y => jointResidualClosedAtom N p d N y) : ℤ) : ℝ) -
        4 * ((MathlibNt.Wu2008DoubleSieve.wuPrimeComplements N).card : ℝ) -
        (4 * (N : ℝ) / w + 2 * (Real.sqrt N + 1)) -
        (4 * (N : ℝ) / z + 2 * (Real.sqrt N + 1)) -
        (s3RepeatedFirstPrimeMass N (orderedTriples (primeWindow N z w)) : ℝ) -
        (s3RepeatedFirstPrimeMass N (s3SecondRange N z w u) : ℝ) -
        (s3PairRepeatedBudget N w u : ℝ) := by
  have h := finiteElevenMixed_exact_aggregate N z w u v V
    hzw hwu hwv huv hv hNv hthird
  rw [finiteElevenExpression_sub, Int.cast_sub, ← jointResidual_expression_sum]
  unfold finiteElevenMixed at h
  linarith

private theorem witness_prime_dvd {q : ℕ} (hq : q.Prime) :
    q ∣ 505505 ↔ q = 5 ∨ q = 7 ∨ q = 11 ∨ q = 13 ∨ q = 101 := by
  have hn : (505505 : ℕ) = 5 * 7 * 11 * 13 * 101 := by norm_num
  rw [hn]
  simp only [hq.dvd_mul]
  have h5 : q ∣ 5 ↔ q = 5 := (Nat.dvd_prime (by norm_num : Nat.Prime 5)).trans
    (by simp [hq.ne_one])
  have h7 : q ∣ 7 ↔ q = 7 := (Nat.dvd_prime (by norm_num : Nat.Prime 7)).trans
    (by simp [hq.ne_one])
  have h11 : q ∣ 11 ↔ q = 11 := (Nat.dvd_prime (by norm_num : Nat.Prime 11)).trans
    (by simp [hq.ne_one])
  have h13 : q ∣ 13 ↔ q = 13 := (Nat.dvd_prime (by norm_num : Nat.Prime 13)).trans
    (by simp [hq.ne_one])
  have h101 : q ∣ 101 ↔ q = 101 := (Nat.dvd_prime (by norm_num : Nat.Prime 101)).trans
    (by simp [hq.ne_one])
  rw [h5, h7, h11, h13, h101]
  tauto

private theorem witness_atom (d M : ℕ) (y : ℝ) :
    jointResidualClosedAtom 505508 3 d M y =
      if d ∣ 505505 ∧ SiftedLE M 505505 y then 1 else 0 := by
  norm_num [jointResidualClosedAtom, sourceSieveCarrierLE]

private theorem witness_sifted {z : ℝ} (hz : z < 5) :
    SiftedLE 505508 505505 z := by
  intro q hq _ hqz hqd
  rcases (witness_prime_dvd hq).mp hqd with rfl | rfl | rfl | rfl | rfl <;>
    norm_num at hqz <;> linarith

private theorem witness_atom_small {z : ℝ} (hz : z < 5) (d : ℕ) :
    jointResidualClosedAtom 505508 3 d 505508 z =
      if d ∣ 505505 then 1 else 0 := by
  rw [witness_atom]
  simp only [witness_sifted hz, and_true]

private theorem witness_divisor_window {z y : ℝ}
    (hz : z < 5) (hy : 13 < y) (hy' : y ≤ 101) :
    (primeWindow 505508 z y).filter (fun q => q ∣ 505505) = {5, 7, 11, 13} := by
  ext q
  simp only [mem_filter, mem_primeWindow, mem_insert, mem_singleton]
  constructor
  · rintro ⟨⟨hq, _, _, hqy⟩, hqd⟩
    rcases (witness_prime_dvd hq).mp hqd with rfl | rfl | rfl | rfl | rfl
    · tauto
    · tauto
    · tauto
    · tauto
    · norm_num at hqy
      linarith
  · rintro (rfl | rfl | rfl | rfl) <;> norm_num <;> constructor <;> linarith

private theorem witness_single_sum {z y : ℝ}
    (hz : z < 5) (hy : 13 < y) (hy' : y ≤ 101) :
    (∑ q ∈ primeWindow 505508 z y,
      jointResidualClosedAtom 505508 3 q 505508 z) = 4 := by
  simp_rw [witness_atom_small hz]
  rw [← sum_filter]
  rw [witness_divisor_window hz hy hy']
  norm_num

private theorem witness_pair_sum {z w : ℝ}
    (hz : z < 5) (hw : 13 < w) (hw' : w ≤ 101) :
    (∑ c ∈ primeWindow 505508 z w, ∑ b ∈ primeWindow 505508 z (c : ℝ),
      jointResidualClosedAtom 505508 3 (b * c) 505508 z) = 6 := by
  have hdiv {b c : ℕ} (hb : b.Prime) (hc : c.Prime) (hbc : b < c) :
      b * c ∣ 505505 ↔ b ∣ 505505 ∧ c ∣ 505505 := by
    constructor
    · intro h
      exact ⟨(dvd_mul_right b c).trans h, (dvd_mul_left c b).trans h⟩
    · rintro ⟨hb', hc'⟩
      exact ((Nat.coprime_primes hb hc).mpr (ne_of_lt hbc)).mul_dvd_of_dvd_of_dvd hb' hc'
  have hinner (c : ℕ) (hc : c ∈ primeWindow 505508 z w) :
      (∑ b ∈ primeWindow 505508 z (c : ℝ),
        jointResidualClosedAtom 505508 3 (b * c) 505508 z) =
      if c ∣ 505505 then
        ∑ b ∈ ({5, 7, 11, 13} : Finset ℕ), if b < c then (1 : ℤ) else 0
      else 0 := by
    have hcw := (mem_primeWindow.mp hc).2.2.2
    have hfilter :
        (primeWindow 505508 z (c : ℝ)).filter (fun b => b ∣ 505505) =
          ({5, 7, 11, 13} : Finset ℕ).filter (fun b => b < c) := by
      rw [← witness_divisor_window hz hw hw']
      ext b
      simp only [mem_filter, mem_primeWindow]
      constructor
      · rintro ⟨⟨hb, hbN, hzb, hbc⟩, hbd⟩
        exact ⟨⟨⟨hb, hbN, hzb, hbc.trans hcw⟩, hbd⟩, by exact_mod_cast hbc⟩
      · rintro ⟨⟨⟨hb, hbN, hzb, _⟩, hbd⟩, hbc⟩
        exact ⟨⟨hb, hbN, hzb, by exact_mod_cast hbc⟩, hbd⟩
    simp_rw [witness_atom_small hz]
    have he :
        (∑ b ∈ primeWindow 505508 z (c : ℝ), if b * c ∣ 505505 then (1 : ℤ) else 0) =
          ∑ b ∈ primeWindow 505508 z (c : ℝ),
            if b ∣ 505505 ∧ c ∣ 505505 then (1 : ℤ) else 0 := by
      apply sum_congr rfl
      intro b hb
      simp only [hdiv (mem_primeWindow.mp hb).1 (mem_primeWindow.mp hc).1
        (by exact_mod_cast (mem_primeWindow.mp hb).2.2.2)]
    rw [he]
    by_cases hcd : c ∣ 505505
    · simp only [hcd, and_true, if_true]
      rw [← sum_filter, hfilter, sum_filter]
    · simp [hcd]
  rw [sum_congr rfl hinner, ← sum_filter, witness_divisor_window hz hw hw']
  norm_num [filter_insert, filter_singleton]

private theorem witness_gap {a : ℕ} {w v : ℝ}
    (hw : 13 < w) (hv : v ≤ 101) (ha : a.Prime)
    (haw : w ≤ (a : ℝ)) (hav : (a : ℝ) < v) :
    ¬a ∣ 505505 := by
  intro had
  rcases (witness_prime_dvd ha).mp had with rfl | rfl | rfl | rfl | rfl <;>
    norm_num at haw hav <;> linarith

theorem jointResidual_closed_atom_obstruction {z w v V : ℝ}
    (hz : z < 5) (hw : 13 < w) (hwv : w ≤ v) (hv : v ≤ 101) :
    finiteElevenExpression 505508 z w v v V (jointResidualClosedAtom 505508 3)
        (fun d y => jointResidualClosedAtom 505508 3 d 505508 y) = 1 := by
  have hbase : jointResidualClosedAtom 505508 3 1 505508 z = 1 := by
    simp [witness_atom_small hz]
  have hbasew : jointResidualClosedAtom 505508 3 1 505508 w = 0 := by
    rw [witness_atom]
    have hs : ¬SiftedLE 505508 505505 w := by
      intro h
      exact h 5 (by norm_num) (by norm_num) (by norm_num; linarith) (by norm_num)
    simp [hs]
  have h6 :
      (∑ c ∈ primeWindow 505508 w v, ∑ b ∈ primeWindow 505508 z w,
        jointResidualClosedAtom 505508 3 (b * c) 505508 z) = 0 := by
    apply sum_eq_zero
    intro c hc
    apply sum_eq_zero
    intro b _
    rw [witness_atom_small hz, if_neg]
    intro hd
    exact witness_gap hw hv (mem_primeWindow.mp hc).1
      (mem_primeWindow.mp hc).2.2.1 (mem_primeWindow.mp hc).2.2.2
      ((dvd_mul_left c b).trans hd)
  have hpairs (x y : ℝ) (f : ℕ × ℕ → Prop) [DecidablePred f] :
      (∑ t ∈ (lowerPairs 505508 505508 x y).filter f,
        jointResidualClosedAtom 505508 3 (t.1 * t.2) (505508 * t.1) (t.2 : ℝ)) = 0 := by
    apply sum_eq_zero
    rintro ⟨a, b⟩ ht
    obtain ⟨ha, hb, hcop, _, _, hab, _⟩ :=
      mem_lowerPairs_source.mp (mem_filter.mp ht).1
    have hbNa : b.Coprime (505508 * a) := Nat.coprime_mul_iff_right.mpr
      ⟨(Nat.coprime_mul_iff_left.mp hcop).2,
        (Nat.coprime_primes hb ha).mpr (ne_of_gt hab)⟩
    simp only [jointResidualClosedAtom,
      source_closed_pair_at_selected_prime 505508 a b hb hbNa, notMem_empty, if_false]
  have h9 :
      (∑ t ∈ (lowerPairs 505508 505508 w v).filter (fun t => (t.1 : ℝ) < v),
        jointResidualClosedAtom 505508 3 (t.1 * t.2) (505508 * t.1)
          (Real.sqrt ((505508 : ℝ) / ((t.1 : ℝ) * t.2)))) = 0 := by
    apply sum_eq_zero
    rintro ⟨a, b⟩ ht
    obtain ⟨ht, hav⟩ := mem_filter.mp ht
    obtain ⟨ha, _, _, haw, _, _, _⟩ := mem_lowerPairs_source.mp ht
    rw [witness_atom]
    have hd : ¬a * b ∣ 505505 := fun hd =>
      witness_gap hw hv ha haw hav ((dvd_mul_right a b).trans hd)
    simp [hd]
  have hfour {a b c d : ℕ} (ha : a.Prime) (haN : a.Coprime 505508) (hab : a < b) :
      jointResidualClosedAtom 505508 3 (a * b * c * d) 505508 (b : ℝ) = 0 := by
    have hz0 := (jointResidual_source_four_zero (c := c) (d := d) ha haN hab).2
    have he : sourceSieveCarrierLE 505508 (a * b * c * d) 505508 (b : ℝ) = ∅ := by
      apply card_eq_zero.mp
      exact Int.ofNat_eq_zero.mp hz0
    simp [jointResidualClosedAtom, he]
  have h10 :
      (∑ t ∈ s3DistinctQuadruples 505508 (orderedTriples (primeWindow 505508 z w)),
        jointResidualClosedAtom 505508 3 (t.1 * t.2.1 * t.2.2.1 * t.2.2.2)
          505508 (t.2.1 : ℝ)) = 0 := by
    apply sum_eq_zero
    rintro ⟨a, b, c, d⟩ ht
    obtain ⟨ha, haN, _, _, _, _, _, _, _, _, hab, _⟩ :=
      mem_s3_first_quadruples.mp ht
    exact hfour ha haN hab
  have h11 :
      (∑ t ∈ s3Upsilon11Range 505508 z w V,
        jointResidualClosedAtom 505508 3 (t.1 * t.2.1 * t.2.2.1 * t.2.2.2)
          505508 (t.2.1 : ℝ)) = 0 := by
    apply sum_eq_zero
    rintro ⟨a, b, c, d⟩ ht
    obtain ⟨ha, haN, _, _, _, _, _, _, _, hab, _⟩ := mem_s3Upsilon11Range.mp ht
    exact hfour ha haN hab
  unfold finiteElevenExpression
  dsimp only
  norm_num only [Nat.cast_ofNat]
  rw [hbase, hbasew, witness_single_sum hz (hw.trans_le hwv) hv,
    witness_pair_sum hz hw (hwv.trans hv), h6, hpairs, hpairs, h9, h10, h11]
  norm_num

theorem jointResidual_witness_squarefree :
    Squarefree (505508 - 3 : ℕ) := by
  rw [Nat.squarefree_iff_prime_squarefree]
  intro q hq hd
  have hqd : q ∣ 505505 := by
    exact (dvd_mul_right q q).trans hd
  rcases (witness_prime_dvd hq).mp hqd with rfl | rfl | rfl | rfl | rfl <;>
    norm_num at hd

theorem jointResidual_witness_not_representation :
    3 ∉ MathlibNt.Wu2008DoubleSieve.wuPrimeComplements 505508 := by
  have hf : Ω (505508 - 3) = 5 := by
    rw [show (505508 - 3 : ℕ) = 5 * 7 * 11 * 13 * 101 by norm_num]
    rw [ArithmeticFunction.cardFactors_mul (by norm_num) (by norm_num),
      ArithmeticFunction.cardFactors_mul (by norm_num) (by norm_num),
      ArithmeticFunction.cardFactors_mul (by norm_num) (by norm_num),
      ArithmeticFunction.cardFactors_mul (by norm_num) (by norm_num)]
    norm_num [ArithmeticFunction.cardFactors_apply_prime]
  intro hp
  have h := (MathlibNt.Wu2008DoubleSieve.mem_wuPrimeComplements.mp hp).2.2.2
  omega

/-- Every cutoff condition used for the witness follows from the literal
source parameters. No extra eventual threshold is being assumed. -/
theorem jointResidual_witness_cutoffs :
    2 ≤ (505508 : ℝ) ^ (1 / 18 : ℝ) ∧
    (505508 : ℝ) ^ (1 / 18 : ℝ) < 5 ∧
    13 < (505508 : ℝ) ^ (1 / 4 : ℝ) ∧
    (505508 : ℝ) ^ (1 / 4 : ℝ) ≤ (505508 : ℝ) ^ (1 / 3 : ℝ) ∧
    (505508 : ℝ) ^ (1 / 3 : ℝ) ≤ 101 := by
  have hp18 : ((505508 : ℝ) ^ (1 / 18 : ℝ)) ^ 18 = 505508 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 505508)]
    norm_num
  have hp4 : ((505508 : ℝ) ^ (1 / 4 : ℝ)) ^ 4 = 505508 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 505508)]
    norm_num
  have hp3 : ((505508 : ℝ) ^ (1 / 3 : ℝ)) ^ 3 = 505508 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 505508)]
    norm_num
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · by_contra h
    have hp := pow_le_pow_left₀ (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 505508) _)
      (le_of_lt (lt_of_not_ge h)) 18
    rw [hp18] at hp
    norm_num at hp
  · by_contra h
    have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 5) (le_of_not_gt h) 18
    rw [hp18] at hp
    norm_num at hp
  · by_contra h
    have hp := pow_le_pow_left₀ (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 505508) _)
      (le_of_not_gt h) 4
    rw [hp4] at hp
    norm_num at hp
  · exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  · by_contra h
    have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 101)
      (le_of_lt (lt_of_not_ge h)) 3
    rw [hp3] at hp
    norm_num at hp

theorem jointResidual_witness_domain :
    4 ≤ (505508 : ℕ) ∧ Even (505508 : ℕ) ∧
    (1 / 18 : ℝ) ≤ 1 / 18 ∧ (1 / 18 : ℝ) ≤ 1 / 4 ∧
    3 * (1 / 18 : ℝ) + 1 / 4 ≤ 1 / 2 ∧
    3 * (1 / 18 : ℝ) - 1 / 4 ≤ 1 / 6 ∧
    2 ≤ (505508 : ℝ) ^ (1 / 18 : ℝ) := by
  norm_num
  exact jointResidual_witness_cutoffs.1

/-- A positive coefficient at a squarefree, non-representation prime
index, at admissible source parameters. It obstructs a pointwise
nonpositivity proof, not a global power-saving estimate. -/
theorem jointResidual_closed_source_pointwise_failure :
    let N : ℕ := 505508
    let κ₁ : ℝ := 1 / 18
    let κ₂ : ℝ := 1 / 4
    let z := (N : ℝ) ^ κ₁
    let w := (N : ℝ) ^ κ₂
    let u := (N : ℝ) ^ (1 / 2 - 3 * κ₁)
    let v := (N : ℝ) ^ (1 / 3 : ℝ)
    let V := (N : ℝ) ^ (1 / 2 - 2 * κ₁)
    finiteElevenExpression N z w u v V (jointResidualClosedAtom N 3)
        (fun d y => jointResidualClosedAtom N 3 d N y) >
      4 * (if 3 ∈ MathlibNt.Wu2008DoubleSieve.wuPrimeComplements N then 1 else 0) := by
  dsimp only
  rw [if_neg jointResidual_witness_not_representation]
  norm_num only [show (1 / 2 - 3 * (1 / 18) : ℝ) = 1 / 3 by norm_num]
  obtain ⟨_, hz, hw, hwv, hv⟩ := jointResidual_witness_cutoffs
  rw [jointResidual_closed_atom_obstruction hz hw hwv hv]
  norm_num

end Wu2008DoubleSieve
