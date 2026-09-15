import MathlibNt.Wu2008DoubleSieve.ClassicalPairSieveCore

/-! Actual small-output labels, with the original alpha and repeated-prime
endpoint. Positive complements follow from the actual product, not parity. -/
namespace Wu2008DoubleSieve.SeventhEighth
open Finset Real
open scoped Classical

noncomputable def classicalSmallLabels (N : ℕ) (S : Finset (ℕ × ℕ)) (Z : ℝ) :
    Finset NinthLabel := (physical N S).filter (fun x => (ninthOutput N x : ℝ) < Z)
noncomputable def classicalSmallBudget (Z : ℝ) : ℝ :=
  (1 / alpha ^ 2) * (⌊max Z 0⌋₊ + 1 : ℕ)

theorem classicalPhysical_data {N : ℕ} {S : Finset (ℕ × ℕ)} {x : NinthLabel}
    (hx : x ∈ physical N S) : x.1 ∈ S ∧ x.2.Prime ∧
      x.1.2 ≤ x.2 ∧ x.1.1 * x.1.2 * x.2 < N ∧ (ninthOutput N x).Prime := by
  obtain ⟨ht, hr⟩ := mem_sigma.mp hx
  obtain ⟨_, hp, hbr, hs, hout⟩ := mem_filter.mp hr
  exact ⟨ht, hp, hbr, hs, hout⟩

theorem classicalPhysical_complement {N : ℕ} {S : Finset (ℕ × ℕ)}
    (hS : ClassicalPairGeometry N S) {x : NinthLabel} (hx : x ∈ physical N S) :
    N - ninthOutput N x = x.1.1 * x.1.2 * x.2 ∧ 0 < N - ninthOutput N x := by
  obtain ⟨ht, hr, _, hs, _⟩ := classicalPhysical_data hx
  obtain ⟨ha, hb, _⟩ := hS x.1 ht
  have heq : N - ninthOutput N x = x.1.1 * x.1.2 * x.2 := Nat.sub_sub_self hs.le
  exact ⟨heq, heq.symm ▸ Nat.mul_pos (Nat.mul_pos ha.pos hb.pos) hr.pos⟩

theorem classicalOutput_pair_injective {N : ℕ} {S : Finset (ℕ × ℕ)}
    (hS : ClassicalPairGeometry N S) :
    Set.InjOn (fun x : NinthLabel =>
      (⟨ninthOutput N x, x.1⟩ : Sigma (fun _ : ℕ => ℕ × ℕ))) (physical N S) := by
  intro x hx y hy h
  have hr := congrArg Sigma.fst h
  have ht := congrArg (fun z : Sigma (fun _ : ℕ => ℕ × ℕ) => z.2) h
  have hprod : x.1.1 * x.1.2 * x.2 = y.1.1 * y.1.2 * y.2 := by
    rw [← (classicalPhysical_complement hS hx).1, ← (classicalPhysical_complement hS hy).1]
    exact congrArg (fun r => N - r) hr
  obtain ⟨ha, hb, _⟩ := hS x.1 (classicalPhysical_data hx).1
  have hpos := Nat.mul_pos ha.pos hb.pos
  change x.1 = y.1 at ht
  rw [← ht] at hprod
  have hc : x.2 = y.2 := by nlinarith
  exact Sigma.ext ht (heq_of_eq hc)

theorem classicalOutput_pair_divisors {N : ℕ} {S : Finset (ℕ × ℕ)}
    (hS : ClassicalPairGeometry N S) {x : NinthLabel} (hx : x ∈ physical N S) :
    x.1 ∈ largePrimeDivisors (N - ninthOutput N x) ((N : ℝ) ^ alpha) ×ˢ
      largePrimeDivisors (N - ninthOutput N x) ((N : ℝ) ^ alpha) := by
  obtain ⟨ha, hb, hab, hwa, _⟩ := hS x.1 (classicalPhysical_data hx).1
  obtain ⟨heq, hn⟩ := classicalPhysical_complement hS hx
  have hd : x.1.1 * x.1.2 ∣ N - ninthOutput N x := heq.symm ▸ dvd_mul_right _ _
  exact mem_product.mpr
    ⟨mem_largePrimeDivisors.mpr
      ⟨ha, (dvd_mul_right _ _).trans hd, hn.ne', hwa⟩,
     mem_largePrimeDivisors.mpr
      ⟨hb, (dvd_mul_left _ _).trans hd, hn.ne',
        hwa.trans (by exact_mod_cast hab.le)⟩⟩

theorem classicalSmallLabels_card_le {N : ℕ} (hN : 1 < N) {S : Finset (ℕ × ℕ)}
    (hS : ClassicalPairGeometry N S) (Z : ℝ) :
    ((classicalSmallLabels N S Z).card : ℝ) ≤ classicalSmallBudget Z := by
  let I := (range (⌊max Z 0⌋₊ + 1)).filter (fun r => 0 < N - r)
  let F := fun r => largePrimeDivisors (N - r) ((N : ℝ) ^ alpha)
  have hinj : (classicalSmallLabels N S Z).card ≤ (I.sigma (fun r => F r ×ˢ F r)).card := by
    apply card_le_card_of_injOn (fun x : NinthLabel =>
      (⟨ninthOutput N x, x.1⟩ : Sigma (fun _ : ℕ => ℕ × ℕ)))
    · intro x hx
      obtain ⟨hx, hZ⟩ := mem_filter.mp hx
      have hrsmall : ninthOutput N x ≤ ⌊max Z 0⌋₊ :=
        Nat.le_floor (hZ.le.trans (le_max_left _ _))
      exact mem_sigma.mpr
        ⟨mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le hrsmall),
          (classicalPhysical_complement hS hx).2⟩, classicalOutput_pair_divisors hS hx⟩
    · exact (classicalOutput_pair_injective hS).mono (filter_subset _ _)
  calc
    _ ≤ ((I.sigma (fun r => F r ×ˢ F r)).card : ℝ) := by exact_mod_cast hinj
    _ = ∑ r ∈ I, ((F r ×ˢ F r).card : ℝ) := by rw [card_sigma, Nat.cast_sum]
    _ ≤ ∑ _r ∈ I, (1 / alpha ^ 2 : ℝ) := by
      apply sum_le_sum
      intro r hr
      exact ninth_pair_budget hN (mem_filter.mp hr).2 (Nat.sub_le N r)
        (by norm_num [alpha])
    _ = (1 / alpha ^ 2) * I.card := by simp only [sum_const, nsmul_eq_mul, mul_comm]
    _ ≤ classicalSmallBudget Z := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have hc : I.card ≤ ⌊max Z 0⌋₊ + 1 := by
        simpa only [card_range] using (card_le_card (filter_subset _ _) : I.card ≤
          (range (⌊max Z 0⌋₊ + 1)).card)
      exact_mod_cast hc

theorem classicalPhysical_large_le_sifted {N : ℕ} {S : Finset (ℕ × ℕ)}
    (hS : ClassicalPairGeometry N S) (Z : ℝ) :
    (((physical N S).filter (fun x => ¬(ninthOutput N x : ℝ) < Z)).card : ℝ) ≤
      classicalSifted N S Z := by
  let G := S.sigma (fun p => (classicalProfile N p).filter
    (fun r => Sifted N (N - ninthPairProduct p * r) Z))
  have hsub : (physical N S).filter (fun x => ¬(ninthOutput N x : ℝ) < Z) ⊆ G := by
    intro x hx
    obtain ⟨hx, hZ⟩ := mem_filter.mp hx
    have ht := (classicalPhysical_data hx).1
    have hcf := (mem_sigma.mp hx).2
    rw [classicalPair_physical_fibre hS ht] at hcf
    exact mem_sigma.mpr ⟨ht, mem_filter.mpr ⟨(mem_filter.mp hcf).1,
      ninth_prime_sifted (classicalPhysical_data hx).2.2.2.2 (le_of_not_gt hZ)⟩⟩
  have hcard : (G.card : ℝ) = classicalSifted N S Z := by
    simp only [G, card_sigma, Nat.cast_sum, classicalSifted]
  exact (by exact_mod_cast card_le_card hsub : (_ : ℝ) ≤ (G.card : ℝ)).trans_eq hcard

theorem classicalPhysical_upper_finite {N D : ℕ} (hN : 1 < N) {S : Finset (ℕ × ℕ)}
    (hS : ClassicalPairGeometry N S) (he : Even N) (Z : ℝ)
    (hD : 1 < D) (hZ : Z ≤ (D : ℝ)) :
    ((physical N S).card : ℝ) ≤
      classicalMass N S * ordinaryRosserMainSum true N 1 D Z +
        classicalPairR1 N S D Z + classicalR2 N S D Z + classicalSmallBudget Z := by
  have hsplit := card_filter_add_card_filter_not (s := physical N S)
    (fun x => (ninthOutput N x : ℝ) < Z)
  have hsplitR : ((classicalSmallLabels N S Z).card : ℝ) +
      (((physical N S).filter (fun x => ¬(ninthOutput N x : ℝ) < Z)).card : ℝ) =
      (physical N S).card := by exact_mod_cast hsplit
  have hs := classicalSmallLabels_card_le hN hS Z
  have hl := classicalPhysical_large_le_sifted hS Z
  have hu := classical_sifted_upper_finite hS he Z hD hZ
  linarith
end Wu2008DoubleSieve.SeventhEighth
