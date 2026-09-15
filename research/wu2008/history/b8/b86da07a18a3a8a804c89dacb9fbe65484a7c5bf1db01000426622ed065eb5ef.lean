import MathlibNt.Wu2008DoubleSieve.ClosedLowerWeightFactors

/-!
# Paid changes from strict to closed sifting

The endpoint losses of negative single and pair terms are counted on the
actual prime indices. A fixed prime endpoint is paid by positive multiples;
a moving pair endpoint forces a large prime-square divisor.
-/

namespace Wu2008DoubleSieve

open Finset
open scoped Classical

noncomputable def sieveCountLE (N d M : ℕ) (z : ℝ) : ℤ :=
  (sieveCarrierLE N d M z).card

noncomputable def sieveEndpointLoss (N d M : ℕ) (z : ℝ) : Finset ℕ :=
  (sieveCarrier N d M z).filter (fun p => ¬SiftedLE M ((N - p) / d) z)

theorem mem_sieveEndpointLoss {N d M p : ℕ} {z : ℝ} :
    p ∈ sieveEndpointLoss N d M z ↔
      p ≤ N ∧ p.Prime ∧ d ∣ N - p ∧ Sifted M ((N - p) / d) z ∧
        ∃ q : ℕ, q.Prime ∧ q.Coprime M ∧ (q : ℝ) = z ∧ q ∣ (N - p) / d := by
  simp only [sieveEndpointLoss, sieveCarrier, mem_filter, mem_range,
    Nat.lt_succ_iff, siftedLE_iff_strict_and_endpoint, not_and, not_forall,
    not_not, exists_prop]
  constructor
  · rintro ⟨⟨hpN, hp, hd, hs⟩, he⟩
    exact ⟨hpN, hp, hd, hs, he hs⟩
  · rintro ⟨hpN, hp, hd, hs, he⟩
    exact ⟨⟨hpN, hp, hd, hs⟩, fun _ => he⟩

theorem sieveCount_eq_closed_add_loss (N d M : ℕ) (z : ℝ) :
    sieveCount N d M z =
      sieveCountLE N d M z + ((sieveEndpointLoss N d M z).card : ℤ) := by
  have he :
      (sieveCarrier N d M z).filter (fun p => SiftedLE M ((N - p) / d) z) =
        sieveCarrierLE N d M z := by
    ext p
    simp only [sieveCarrier, sieveCarrierLE, mem_filter]
    constructor
    · rintro ⟨⟨hp, hprime, hd, _⟩, hs⟩
      exact ⟨hp, hprime, hd, hs⟩
    · rintro ⟨hp, hprime, hd, hs⟩
      exact ⟨⟨hp, hprime, hd,
        (siftedLE_iff_strict_and_endpoint M ((N - p) / d) z).mp hs |>.1⟩, hs⟩
  have h := card_filter_add_card_filter_not (s := sieveCarrier N d M z)
    (fun p => SiftedLE M ((N - p) / d) z)
  rw [he] at h
  unfold sieveCount sieveCountLE sieveEndpointLoss
  exact_mod_cast h.symm

theorem sieveCountLE_le_strict (N d M : ℕ) (z : ℝ) :
    sieveCountLE N d M z ≤ sieveCount N d M z := by
  rw [sieveCount_eq_closed_add_loss]
  exact le_add_of_nonneg_right (Int.natCast_nonneg _)

noncomputable def primeIndices (N : ℕ) : Finset ℕ :=
  (range (N + 1)).filter Nat.Prime

theorem mem_primeIndices {N p : ℕ} :
    p ∈ primeIndices N ↔ p ≤ N ∧ p.Prime := by
  simp only [primeIndices, mem_filter, mem_range, Nat.lt_succ_iff]

theorem sieveEndpointLoss_subset_primeIndices (N d M : ℕ) (z : ℝ) :
    sieveEndpointLoss N d M z ⊆ primeIndices N := by
  intro p hp
  obtain ⟨hpN, hp, _⟩ := mem_sieveEndpointLoss.mp hp
  exact mem_primeIndices.mpr ⟨hpN, hp⟩

/-- Finite double counting, with every multiplicity retained. -/
theorem endpoint_sum_cards_eq {ι : Type*} (s : Finset ι) (A : Finset ℕ)
    (f : ι → Finset ℕ) (hf : ∀ i ∈ s, f i ⊆ A) :
    (∑ i ∈ s, ((f i).card : ℝ)) =
      ∑ p ∈ A, ((s.filter (fun i => p ∈ f i)).card : ℝ) := by
  calc
    (∑ i ∈ s, ((f i).card : ℝ)) =
        ∑ i ∈ s, ∑ p ∈ A, if p ∈ f i then (1 : ℝ) else 0 := by
      apply sum_congr rfl
      intro i hi
      rw [sum_boole]
      have hset : A.filter (fun p => p ∈ f i) = f i := by
        ext p
        simp only [mem_filter]
        exact ⟨fun hp => hp.2, fun hp => ⟨hf i hi hp, hp⟩⟩
      rw [hset]
    _ = ∑ p ∈ A, ∑ i ∈ s, if p ∈ f i then (1 : ℝ) else 0 := sum_comm
    _ = _ := by simp only [sum_boole]

theorem primeComplement_filter_card_le (N : ℕ) (E : Finset ℕ) :
    ((primeIndices N).filter (fun p => N - p ∈ E)).card ≤ E.card := by
  apply card_le_card_of_injOn (fun p => N - p)
  · intro p hp
    exact (mem_filter.mp hp).2
  · intro p hp q hq he
    have hpN := (mem_primeIndices.mp (mem_filter.mp hp).1).1
    have hqN := (mem_primeIndices.mp (mem_filter.mp hq).1).1
    dsimp at he
    omega

noncomputable def fixedPrimeEndpoint (N : ℕ) (z : ℝ) : Finset ℕ :=
  (Ioc 0 N).filter (fun n => ∃ q : ℕ, q.Prime ∧ (q : ℝ) = z ∧ q ∣ n)

theorem fixedPrimeEndpoint_card_le (N : ℕ) {z : ℝ} (hz : 0 < z) :
    ((fixedPrimeEndpoint N z).card : ℝ) ≤ (N : ℝ) / z := by
  by_cases he : ∃ q : ℕ, q.Prime ∧ (q : ℝ) = z
  · obtain ⟨q, hq, hqz⟩ := he
    have hset : fixedPrimeEndpoint N z = (Ioc 0 N).filter (fun n => q ∣ n) := by
      ext n
      simp only [fixedPrimeEndpoint, mem_filter]
      constructor
      · rintro ⟨hn, r, _, hrz, hrn⟩
        have hrq : r = q := by exact_mod_cast hrz.trans hqz.symm
        exact ⟨hn, hrq ▸ hrn⟩
      · rintro ⟨hn, hqn⟩
        exact ⟨hn, q, hq, hqz, hqn⟩
    rw [hset, Nat.Ioc_filter_dvd_card_eq_div, ← hqz]
    exact Nat.cast_div_le
  · have hset : fixedPrimeEndpoint N z = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro n hn
      obtain ⟨_, q, hq, hqz, _⟩ := mem_filter.mp hn
      exact he ⟨q, hq, hqz⟩
    rw [hset, card_empty, Nat.cast_zero]
    exact div_nonneg (Nat.cast_nonneg N) hz.le

theorem single_endpoint_mem_fixed {N p q : ℕ} {z : ℝ}
    (hn : 0 < N - p) (hp : p ∈ sieveEndpointLoss N q N z) :
    N - p ∈ fixedPrimeEndpoint N z := by
  obtain ⟨_, _, hd, _, r, hr, _, hrz, hrd⟩ := mem_sieveEndpointLoss.mp hp
  have hrn : r ∣ N - p :=
    dvd_trans hrd (Nat.div_dvd_of_dvd hd)
  exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨hn, Nat.sub_le N p⟩, r, hr, hrz, hrn⟩

theorem pair_endpoint_mem_square {N p a b : ℕ} {z : ℝ}
    (hn : 0 < N - p) (hb : b.Prime) (hzb : z ≤ (b : ℝ))
    (hp : p ∈ sieveEndpointLoss N (a * b) (N * a) (b : ℝ)) :
    N - p ∈ largePrimeSquareExceptions N z := by
  obtain ⟨_, _, hd, _, r, _, _, hrb, hrd⟩ := mem_sieveEndpointLoss.mp hp
  have hr : r = b := by exact_mod_cast hrb
  subst r
  have hbnd : (a * b) * b ∣ N - p := (Nat.dvd_div_iff_mul_dvd hd).mp hrd
  have hbsq : b ^ 2 ∣ N - p := by
    apply dvd_trans _ hbnd
    have : (a * b) * b = a * b ^ 2 := by ring
    rw [this]
    exact dvd_mul_left _ _
  exact mem_largePrimeSquareExceptions.mpr
    ⟨hn, Nat.sub_le N p, b, hb, hzb, hbsq⟩

private theorem endpoint_sum_cards_le {ι : Type*} (s : Finset ι) (A : Finset ℕ)
    (f : ι → Finset ℕ) (P : ℕ → Prop) [DecidablePred P] (B : ℝ)
    (hf : ∀ i ∈ s, f i ⊆ A)
    (hb : ∀ p ∈ A, ((s.filter (fun i => p ∈ f i)).card : ℝ) ≤ B)
    (hs : ∀ p ∈ A, ¬P p → s.filter (fun i => p ∈ f i) = ∅) :
    (∑ i ∈ s, ((f i).card : ℝ)) ≤ B * ((A.filter P).card : ℝ) := by
  rw [endpoint_sum_cards_eq s A f hf]
  calc
    (∑ p ∈ A, ((s.filter (fun i => p ∈ f i)).card : ℝ)) ≤
        ∑ p ∈ A, if P p then B else 0 := by
      apply sum_le_sum
      intro p hp
      by_cases hP : P p
      · simpa only [if_pos hP] using hb p hp
      · rw [if_neg hP, hs p hp hP, card_empty, Nat.cast_zero]
    _ = B * ((A.filter P).card : ℝ) := by
      rw [← sum_filter]
      simp only [sum_const, nsmul_eq_mul, mul_comm]

theorem single_endpoint_multiplicity_le {N p : ℕ} (hN : 1 < N)
    (hn : 0 < N - p) {κ : ℝ} (hκ : 0 < κ) (w : ℝ) :
    (((primeWindow N ((N : ℝ) ^ κ) w).filter
      (fun q => p ∈ sieveEndpointLoss N q N ((N : ℝ) ^ κ))).card : ℝ) ≤ 1 / κ := by
  have hsub :
      (primeWindow N ((N : ℝ) ^ κ) w).filter
        (fun q => p ∈ sieveEndpointLoss N q N ((N : ℝ) ^ κ)) ⊆
          largePrimeDivisors (N - p) ((N : ℝ) ^ κ) := by
    intro q hq
    obtain ⟨hq, hl⟩ := mem_filter.mp hq
    obtain ⟨hqp, _, hzq, _⟩ := mem_primeWindow.mp hq
    have hd := (mem_sieveEndpointLoss.mp hl).2.2.1
    exact mem_largePrimeDivisors.mpr ⟨hqp, hd, Nat.ne_of_gt hn, hzq⟩
  calc
    _ ≤ ((largePrimeDivisors (N - p) ((N : ℝ) ^ κ)).card : ℝ) := by
      exact_mod_cast card_le_card hsub
    _ ≤ 1 / κ := largePrimeDivisors_card_le_inv hN hn (Nat.sub_le N p) hκ

theorem single_endpoint_sum_le {N : ℕ} (hN : 4 ≤ N) (he : Even N)
    {κ : ℝ} (hκ : 0 < κ) (w : ℝ) :
    (∑ q ∈ primeWindow N ((N : ℝ) ^ κ) w,
      ((sieveEndpointLoss N q N ((N : ℝ) ^ κ)).card : ℝ)) ≤
        (1 / κ) * ((N : ℝ) / (N : ℝ) ^ κ) := by
  have hsum := endpoint_sum_cards_le
    (primeWindow N ((N : ℝ) ^ κ) w) (primeIndices N)
    (fun q => sieveEndpointLoss N q N ((N : ℝ) ^ κ))
    (fun p => N - p ∈ fixedPrimeEndpoint N ((N : ℝ) ^ κ)) (1 / κ)
    (fun q _ => sieveEndpointLoss_subset_primeIndices N q N ((N : ℝ) ^ κ))
    (by
      intro p hp
      obtain ⟨hpN, hpp⟩ := mem_primeIndices.mp hp
      exact single_endpoint_multiplicity_le (by omega)
        (complement_pos_of_even hN he hpN hpp) hκ w)
    (by
      intro p hp hnot
      apply eq_empty_iff_forall_notMem.mpr
      intro q hq
      obtain ⟨hpN, hpp⟩ := mem_primeIndices.mp hp
      exact hnot (single_endpoint_mem_fixed
        (complement_pos_of_even hN he hpN hpp) (mem_filter.mp hq).2))
  have hcard :
      (((primeIndices N).filter
        (fun p => N - p ∈ fixedPrimeEndpoint N ((N : ℝ) ^ κ))).card : ℝ) ≤
          (N : ℝ) / (N : ℝ) ^ κ := by
    calc
      _ ≤ ((fixedPrimeEndpoint N ((N : ℝ) ^ κ)).card : ℝ) := by
        exact_mod_cast primeComplement_filter_card_le N
          (fixedPrimeEndpoint N ((N : ℝ) ^ κ))
      _ ≤ _ := fixedPrimeEndpoint_card_le N
        (Real.rpow_pos_of_pos (by positivity) κ)
  have hb := mul_le_mul_of_nonneg_left hcard (show (0 : ℝ) ≤ 1 / κ by positivity)
  exact hsum.trans hb

theorem pair_endpoint_multiplicity_le {N p : ℕ} (hN : 1 < N)
    (hn : 0 < N - p) {κ w : ℝ} (hκ : 0 < κ) (hzw : (N : ℝ) ^ κ ≤ w) :
    (((lowerPairs N N ((N : ℝ) ^ κ) w).filter
      (fun t => p ∈ sieveEndpointLoss N (t.1 * t.2) (N * t.1) (t.2 : ℝ))).card : ℝ)
        ≤ (1 / κ) ^ 2 := by
  let F := largePrimeDivisors (N - p) ((N : ℝ) ^ κ)
  have hsub :
      (lowerPairs N N ((N : ℝ) ^ κ) w).filter
        (fun t => p ∈ sieveEndpointLoss N (t.1 * t.2) (N * t.1) (t.2 : ℝ)) ⊆
          F ×ˢ F := by
    rintro ⟨a, b⟩ ht
    obtain ⟨ht, hl⟩ := mem_filter.mp ht
    obtain ⟨ht, _, _⟩ := mem_filter.mp ht
    obtain ⟨ha, hb⟩ := mem_product.mp ht
    obtain ⟨hap, _, hza, _⟩ := mem_primeWindow.mp ha
    obtain ⟨hbp, _, hwb, _⟩ := mem_primeWindow.mp hb
    have hd := (mem_sieveEndpointLoss.mp hl).2.2.1
    apply mem_product.mpr
    exact ⟨mem_largePrimeDivisors.mpr
      ⟨hap, dvd_trans (dvd_mul_right a b) hd, Nat.ne_of_gt hn, hza⟩,
      mem_largePrimeDivisors.mpr
      ⟨hbp, dvd_trans (dvd_mul_left b a) hd, Nat.ne_of_gt hn, hzw.trans hwb⟩⟩
  have hc : (F.card : ℝ) ≤ 1 / κ :=
    largePrimeDivisors_card_le_inv hN hn (Nat.sub_le N p) hκ
  calc
    _ ≤ ((F ×ˢ F).card : ℝ) := by exact_mod_cast card_le_card hsub
    _ = (F.card : ℝ) ^ 2 := by rw [card_product, Nat.cast_mul, pow_two]
    _ ≤ (1 / κ) ^ 2 := by
      exact pow_le_pow_left₀ (Nat.cast_nonneg _) hc 2

theorem pair_endpoint_sum_le {N : ℕ} (hN : 4 ≤ N) (he : Even N)
    {κ w : ℝ} (hκ : 0 < κ) (hz : 2 ≤ (N : ℝ) ^ κ)
    (hzw : (N : ℝ) ^ κ ≤ w) :
    (∑ t ∈ lowerPairs N N ((N : ℝ) ^ κ) w,
      ((sieveEndpointLoss N (t.1 * t.2) (N * t.1) (t.2 : ℝ)).card : ℝ)) ≤
        2 * (1 / κ) ^ 2 * ((N : ℝ) / (N : ℝ) ^ κ) := by
  have hsum := endpoint_sum_cards_le
    (lowerPairs N N ((N : ℝ) ^ κ) w) (primeIndices N)
    (fun t => sieveEndpointLoss N (t.1 * t.2) (N * t.1) (t.2 : ℝ))
    (fun p => N - p ∈ largePrimeSquareExceptions N ((N : ℝ) ^ κ)) ((1 / κ) ^ 2)
    (fun t _ => sieveEndpointLoss_subset_primeIndices N (t.1 * t.2) (N * t.1) t.2)
    (by
      intro p hp
      obtain ⟨hpN, hpp⟩ := mem_primeIndices.mp hp
      exact pair_endpoint_multiplicity_le (by omega)
        (complement_pos_of_even hN he hpN hpp) hκ hzw)
    (by
      intro p hp hnot
      apply eq_empty_iff_forall_notMem.mpr
      rintro ⟨a, b⟩ ht
      obtain ⟨ht, hl⟩ := mem_filter.mp ht
      obtain ⟨ht, _, _⟩ := mem_filter.mp ht
      have hb := (mem_product.mp ht).2
      obtain ⟨hbp, _, hwb, _⟩ := mem_primeWindow.mp hb
      obtain ⟨hpN, hpp⟩ := mem_primeIndices.mp hp
      exact hnot (pair_endpoint_mem_square (complement_pos_of_even hN he hpN hpp)
        hbp (hzw.trans hwb) hl))
  have hcard :
      (((primeIndices N).filter
        (fun p => N - p ∈ largePrimeSquareExceptions N ((N : ℝ) ^ κ))).card : ℝ) ≤
          2 * (N : ℝ) / (N : ℝ) ^ κ := by
    calc
      _ ≤ ((largePrimeSquareExceptions N ((N : ℝ) ^ κ)).card : ℝ) := by
        exact_mod_cast primeComplement_filter_card_le N
          (largePrimeSquareExceptions N ((N : ℝ) ^ κ))
      _ ≤ _ := largePrimeSquareExceptions_card_le N hz
  have hb := mul_le_mul_of_nonneg_left hcard (sq_nonneg (1 / κ))
  calc
    _ ≤ (1 / κ) ^ 2 * (2 * (N : ℝ) / (N : ℝ) ^ κ) := hsum.trans hb
    _ = _ := by ring

end Wu2008DoubleSieve
