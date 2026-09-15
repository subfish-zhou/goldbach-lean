import MathlibNt.Wu2004MeanValue.OriginalTailQuotients

/-!
# Finite switching with the actual exceptional indices

A composite sifted quotient has least prime divisor equal to the original
prime value. Its cube is at most `N`. The unit quotient and small prime values
are counted separately, without suppressing their multiplicities.
-/

namespace Wu2004MeanValue

open Classical Finset
noncomputable section

theorem originalTailQuotient_pos {N r p : ℕ} {η : ℝ}
    (hη : 0 < η) (hp : p ∈ originalTailPrimeIndices N r η) :
    0 < (N - p) / r := by
  have h := mem_originalTailPrimeIndices.mp hp
  have hN : 0 < N := h.2.1.pos.trans_le h.1
  have hpN : p < N := by
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    have : (p : ℝ) < N := by nlinarith [h.2.2.1]
    exact_mod_cast this
  have heq := Nat.mul_div_cancel' h.2.2.2.1
  have hsub := Nat.sub_pos_of_lt hpN
  nlinarith

theorem originalTailComposite_leastPrime {N r p : ℕ} {η : ℝ}
    (hη : 0 < η) (hp : p ∈ originalTailPrimeIndices N r η)
    (hr3 : N < r ^ 3) (hm1 : (N - p) / r ≠ 1)
    (hm : ¬((N - p) / r).Prime) :
    p = ((N - p) / r).minFac ∧ p < r ∧ p ^ 3 ≤ N := by
  let m := (N - p) / r
  let s := m.minFac
  have h := mem_originalTailPrimeIndices.mp hp
  have hm0 : 0 < m := originalTailQuotient_pos hη hp
  have hs : s.Prime := Nat.minFac_prime hm1
  have hsd : s ∣ m := Nat.minFac_dvd m
  have hs2 : s ^ 2 ≤ m := Nat.minFac_sq_le_self hm0 hm
  have heq : r * m = N - p := Nat.mul_div_cancel' h.2.2.2.1
  have hrm : r * m ≤ N := heq ▸ Nat.sub_le N p
  have hmr : m < r ^ 2 := by
    by_contra hn
    have hh := Nat.mul_le_mul_left r (le_of_not_gt hn)
    nlinarith
  have hsr : s < r := by nlinarith
  have hsdN : s ∣ N := by
    by_contra hn
    have hdP : s ∣ siftingProduct N r :=
      (prime_dvd_siftingProduct_iff hs).mpr ⟨by exact_mod_cast hsr, hn⟩
    exact (hs.coprime_iff_not_dvd.mp (h.2.2.2.2.coprime_dvd_left hsd)) hdP
  have hsdsub : s ∣ N - p := heq ▸ dvd_mul_of_dvd_right hsd r
  have hsdp : s ∣ p := by
    have hh := Nat.dvd_sub hsdN hsdsub
    simpa only [Nat.sub_sub_self h.1] using hh
  have hps : p = s := ((Nat.prime_dvd_prime_iff_eq hs h.2.1).mp hsdp).symm
  refine ⟨hps, hps ▸ hsr, ?_⟩
  calc
    p ^ 3 = p * p ^ 2 := by ring
    _ ≤ r * m := Nat.mul_le_mul (hps ▸ hsr.le) (hps ▸ hs2)
    _ ≤ N := hrm

def originalTailGood (N : ℕ) (c τ η z : ℝ) : Finset (Σ _ : ℕ, ℕ) :=
  (originalTailIndices N c τ η).filter
    (fun t => ((N - t.2) / t.1).Prime ∧ z ≤ (t.2 : ℝ))

def originalTailSmall (N : ℕ) (c τ η X : ℝ) : Finset (Σ _ : ℕ, ℕ) :=
  (originalTailIndices N c τ η).filter (fun t => (t.2 : ℝ) ≤ X)

def originalTailUnit (N : ℕ) (c τ η : ℝ) : Finset (Σ _ : ℕ, ℕ) :=
  (originalTailIndices N c τ η).filter (fun t => (N - t.2) / t.1 = 1)

theorem originalTailGood_card_le (N : ℕ) (c τ η z : ℝ) :
    (originalTailGood N c τ η z).card ≤ tailSiftedCount N c τ η z := by
  unfold tailSiftedCount indexedSiftedCount
  apply card_le_card_of_injOn (originalTailSwitch N)
  · intro t ht
    obtain ⟨hti, hprime, hz⟩ := mem_filter.mp ht
    obtain ⟨hr, hp⟩ := mem_originalTailIndices.mp hti
    apply mem_filter.mpr
    refine ⟨originalTailSwitch_mem_tailPairs hr hp hprime, ?_⟩
    rw [originalTailSwitch_pairValue hp]
    exact prime_coprime_siftingProduct (mem_originalTailPrimeIndices.mp hp).2.1 hz
  · exact originalTailSwitch_injective.mono (filter_subset _ _)

theorem originalTailUnit_card_le (N : ℕ) (c τ η : ℝ) :
    (originalTailUnit N c τ η).card ≤ ⌊Real.sqrt N⌋₊ + 1 := by
  apply (card_le_card_of_injOn Sigma.fst (t := range (⌊Real.sqrt N⌋₊ + 1)) ?_ ?_).trans_eq
    (card_range _)
  · intro t ht
    have h := (mem_originalTailIndices.mp (mem_filter.mp ht).1).1
    exact (mem_filter.mp h).1
  · rintro ⟨r, p⟩ hp ⟨s, q⟩ hq hrs
    change r = s at hrs
    subst s
    obtain ⟨hpI, hp1⟩ := mem_filter.mp hp
    obtain ⟨hqI, hq1⟩ := mem_filter.mp hq
    have hp' := (mem_originalTailIndices.mp hpI).2
    have hq' := (mem_originalTailIndices.mp hqI).2
    have hpq : p = q := originalTailQuotient_injective hp' hq' (hp1.trans hq1.symm)
    subst q
    rfl

theorem originalTailSmall_card_le (N : ℕ) (c τ η X : ℝ) (hX : 0 ≤ X) :
    (originalTailSmall N c τ η X).card ≤
      (⌊Real.sqrt N⌋₊ + 1) * (⌊X⌋₊ + 1) := by
  have hsub : originalTailSmall N c τ η X ⊆
      (range (⌊Real.sqrt N⌋₊ + 1)).sigma (fun _ => range (⌊X⌋₊ + 1)) := by
    intro t ht
    obtain ⟨htI, hpX⟩ := mem_filter.mp ht
    have hr := (mem_originalTailIndices.mp htI).1
    apply mem_sigma.mpr
    refine ⟨(mem_filter.mp hr).1, ?_⟩
    rw [mem_range, Nat.lt_succ_iff, Nat.le_floor_iff hX]
    exact hpX
  simpa using card_le_card hsub

theorem tailOriginalSum_le_sifted_add_rectangle {N : ℕ} {c τ η z X : ℝ}
    (hη : 0 < η) (hX : 0 ≤ X) (hNX : (N : ℝ) ≤ X ^ 3) (hz : z ≤ X)
    (hr3 : ∀ r ∈ tailSource N c τ, N < r ^ 3) :
    tailOriginalSum N c τ η ≤ tailSiftedCount N c τ η z +
      (⌊Real.sqrt N⌋₊ + 1) * (⌊X⌋₊ + 1) + (⌊Real.sqrt N⌋₊ + 1) := by
  have hcover : originalTailIndices N c τ η ⊆
      (originalTailGood N c τ η z ∪ originalTailSmall N c τ η X) ∪
        originalTailUnit N c τ η := by
    intro t ht
    obtain ⟨hr, hp⟩ := mem_originalTailIndices.mp ht
    by_cases hu : (N - t.2) / t.1 = 1
    · exact mem_union_right _ (mem_filter.mpr ⟨ht, hu⟩)
    apply mem_union_left
    by_cases hm : ((N - t.2) / t.1).Prime
    · by_cases hpz : z ≤ (t.2 : ℝ)
      · exact mem_union_left _ (mem_filter.mpr ⟨ht, hm, hpz⟩)
      · exact mem_union_right _ (mem_filter.mpr ⟨ht, (le_of_not_ge hpz).trans hz⟩)
    · have hc := (originalTailComposite_leastPrime hη hp (hr3 t.1 hr) hu hm).2.2
      have hp3 : (t.2 : ℝ) ^ 3 ≤ X ^ 3 := (by exact_mod_cast hc : (t.2 : ℝ) ^ 3 ≤ N).trans hNX
      have hpX : (t.2 : ℝ) ≤ X := le_of_pow_le_pow_left₀ (by norm_num) hX hp3
      exact mem_union_right _ (mem_filter.mpr ⟨ht, hpX⟩)
  rw [tailOriginalSum_eq_primeIndex_card]
  calc
    _ ≤ _ := card_le_card hcover
    _ ≤ ((originalTailGood N c τ η z).card + (originalTailSmall N c τ η X).card) +
        (originalTailUnit N c τ η).card :=
      (card_union_le _ _).trans (Nat.add_le_add_right (card_union_le _ _) _)
    _ ≤ _ := Nat.add_le_add
      (Nat.add_le_add (originalTailGood_card_le N c τ η z)
        (originalTailSmall_card_le N c τ η X hX))
      (originalTailUnit_card_le N c τ η)

end
end Wu2004MeanValue
