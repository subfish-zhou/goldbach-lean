import MathlibNt.Wu2004MeanValue.OriginalLargeTriples

/-!
# Finite transport of large-product triples

Coprime source primes map to the original quotient-sieve indices. If the
source prime divides `N`, it equals `p`; this exceptional branch injects into
the integers up to `sqrt N`. No coprimality of `q` with `N` is assumed.
-/

namespace Wu2004MeanValue

open Classical Finset
noncomputable section

def originalLargeTripleIndex (t : ℕ × ℕ × ℕ) : Σ _ : ℕ, ℕ :=
  ⟨t.2.1, t.1⟩

theorem originalLargeTripleIndex_injOn (N : ℕ) (a η : ℝ) :
    Set.InjOn originalLargeTripleIndex
      (originalLargeTriples N a η : Set (ℕ × ℕ × ℕ)) := by
  rintro ⟨p, r, q⟩ ht ⟨p', r', q'⟩ hu he
  have hr : r = r' := congrArg Sigma.fst he
  have hp : p = p' := congrArg (fun t : Σ _ : ℕ, ℕ => t.2) he
  subst r'
  subst p'
  have htN := (mem_originalLargeTriples.mp ht).2.2.2.1
  have huN := (mem_originalLargeTriples.mp hu).2.2.2.1
  have hr0 := (mem_originalLargeTriples.mp ht).2.1.ne_zero
  have hq : q = q' := mul_left_cancel₀ hr0 (by omega : r * q = r * q')
  subst q'
  rfl

theorem originalLargeTriple_product_lt_rpow {N : ℕ} {a η : ℝ}
    {t : ℕ × ℕ × ℕ} (ht : t ∈ originalLargeTriples N a η) (ha : 1 < a) :
    (t.2.1 : ℝ) * t.2.2 < (t.2.1 : ℝ) ^ (a / (a - 1)) := by
  have hr0 : (0 : ℝ) < t.2.1 := by
    exact_mod_cast (mem_originalLargeTriples.mp ht).2.1.pos
  have hpow := (mem_originalLargeTriples.mp ht).2.2.2.2.2.1
  have hq : (t.2.2 : ℝ) < (t.2.1 : ℝ) ^ (a - 1)⁻¹ :=
    (Real.lt_rpow_inv_iff_of_pos (Nat.cast_nonneg _) hr0.le (sub_pos.mpr ha)).mpr hpow
  have hexp : a / (a - 1) = 1 + (a - 1)⁻¹ := by
    field_simp [(sub_pos.mpr ha).ne']
    ring
  calc
    (t.2.1 : ℝ) * t.2.2 < (t.2.1 : ℝ) * (t.2.1 : ℝ) ^ (a - 1)⁻¹ :=
      mul_lt_mul_of_pos_left hq hr0
    _ = (t.2.1 : ℝ) ^ (a / (a - 1)) := by
      rw [hexp, Real.rpow_add hr0, Real.rpow_one]

theorem originalLargeTriple_source_gt_product_rpow {N : ℕ} {a η : ℝ}
    {t : ℕ × ℕ × ℕ} (ht : t ∈ originalLargeTriples N a η) (ha : 1 < a) :
    ((t.2.1 : ℝ) * t.2.2) ^ ((a - 1) / a) < t.2.1 := by
  have ha0 : 0 < a := lt_trans zero_lt_one ha
  have hexp : a / (a - 1) * ((a - 1) / a) = 1 := by
    field_simp [(sub_pos.mpr ha).ne', ha0.ne']
  have h := Real.rpow_lt_rpow (by positivity : 0 ≤ (t.2.1 : ℝ) * t.2.2)
    (originalLargeTriple_product_lt_rpow ht ha) (div_pos (sub_pos.mpr ha) ha0)
  rwa [← Real.rpow_mul (Nat.cast_nonneg _), hexp, Real.rpow_one] at h

theorem originalLargeTriple_product_rpow_gt_cutoff {N : ℕ} {a η : ℝ}
    {t : ℕ × ℕ × ℕ} (ht : t ∈ originalLargeTriples N a η)
    (ha : 1 < a) (hη : 0 ≤ η) :
    η ^ ((a - 1) / a) * (N : ℝ) ^ ((a - 1) / a) <
      ((t.2.1 : ℝ) * t.2.2) ^ ((a - 1) / a) := by
  rw [← Real.mul_rpow hη (Nat.cast_nonneg N)]
  exact Real.rpow_lt_rpow (mul_nonneg hη (Nat.cast_nonneg N))
    (mem_originalLargeTriples.mp ht).2.2.2.2.2.2
    (div_pos (sub_pos.mpr ha) (lt_trans zero_lt_one ha))

theorem originalLargeTriple_source_le_sqrt {N : ℕ} {a η : ℝ}
    {t : ℕ × ℕ × ℕ} (ht : t ∈ originalLargeTriples N a η) :
    (t.2.1 : ℝ) ≤ Real.sqrt N := by
  obtain ⟨_, _, _, hN, hrq, _, _⟩ := mem_originalLargeTriples.mp ht
  have hrq' : (t.2.1 : ℝ) ≤ t.2.2 := by exact_mod_cast hrq
  have hN' : (N : ℝ) = t.1 + (t.2.1 : ℝ) * t.2.2 := by exact_mod_cast hN
  apply (Real.le_sqrt (Nat.cast_nonneg _) (Nat.cast_nonneg N)).mpr
  nlinarith [mul_le_mul_of_nonneg_left hrq' (Nat.cast_nonneg t.2.1),
    Nat.cast_nonneg (α := ℝ) t.1]

theorem originalLargeTriple_quotient {N : ℕ} {a η : ℝ} {t : ℕ × ℕ × ℕ}
    (ht : t ∈ originalLargeTriples N a η) :
    (N - t.1) / t.2.1 = t.2.2 := by
  have hN := (mem_originalLargeTriples.mp ht).2.2.2.1
  have hr0 := (mem_originalLargeTriples.mp ht).2.1.pos
  rw [hN, Nat.add_sub_cancel_left, Nat.mul_div_cancel_left _ hr0]

theorem originalLargeTriple_quotient_sifted {N : ℕ} {a η : ℝ}
    {t : ℕ × ℕ × ℕ} (ht : t ∈ originalLargeTriples N a η) :
    ((N - t.1) / t.2.1).Coprime (siftingProduct N t.2.1) := by
  rw [originalLargeTriple_quotient ht]
  apply prime_coprime_siftingProduct (mem_originalLargeTriples.mp ht).2.2.1
  exact_mod_cast (mem_originalLargeTriples.mp ht).2.2.2.2.1

theorem originalLargeTriple_mem_originalTailIndices {N : ℕ} {a η : ℝ}
    {t : ℕ × ℕ × ℕ} (ht : t ∈ originalLargeTriples N a η)
    (ha : 1 < a) (hη : 0 ≤ η) (hc : t.2.1.Coprime N) :
    originalLargeTripleIndex t ∈
      originalTailIndices N (η ^ ((a - 1) / a)) ((a - 1) / a) η := by
  obtain ⟨hp, hr, _, hN, _, _, hlarge⟩ := mem_originalLargeTriples.mp ht
  have hN' : (N : ℝ) = t.1 + (t.2.1 : ℝ) * t.2.2 := by exact_mod_cast hN
  apply mem_originalTailIndices.mpr
  refine ⟨mem_tailSource.mpr ⟨hr, hc, ?_, originalLargeTriple_source_le_sqrt ht⟩,
    mem_originalTailPrimeIndices.mpr ⟨?_, hp, ?_, ?_,
      originalLargeTriple_quotient_sifted ht⟩⟩
  · exact (originalLargeTriple_product_rpow_gt_cutoff ht ha hη).trans
      (originalLargeTriple_source_gt_product_rpow ht ha)
  · omega
  · nlinarith
  · rw [hN, Nat.add_sub_cancel_left]
    exact dvd_mul_right _ _

def originalLargeTriplesCoprime (N : ℕ) (a η : ℝ) : Finset (ℕ × ℕ × ℕ) :=
  (originalLargeTriples N a η).filter (fun t => t.2.1.Coprime N)

def originalLargeTriplesExceptional (N : ℕ) (a η : ℝ) : Finset (ℕ × ℕ × ℕ) :=
  (originalLargeTriples N a η).filter (fun t => ¬t.2.1.Coprime N)

theorem originalLargeTriplesCoprime_card_le {N : ℕ} {a η : ℝ}
    (ha : 1 < a) (hη : 0 ≤ η) :
    (originalLargeTriplesCoprime N a η).card ≤
      tailOriginalSum N (η ^ ((a - 1) / a)) ((a - 1) / a) η := by
  rw [tailOriginalSum_eq_primeIndex_card]
  apply card_le_card_of_injOn originalLargeTripleIndex
  · intro t ht
    obtain ⟨ht, hc⟩ := mem_filter.mp ht
    exact originalLargeTriple_mem_originalTailIndices ht ha hη hc
  · intro t ht u hu he
    exact originalLargeTripleIndex_injOn N a η
      (mem_filter.mp ht).1 (mem_filter.mp hu).1 he

theorem originalLargeTriple_prime_eq_source_of_dvd {N : ℕ} {a η : ℝ}
    {t : ℕ × ℕ × ℕ} (ht : t ∈ originalLargeTriples N a η)
    (hd : t.2.1 ∣ N) : t.1 = t.2.1 := by
  obtain ⟨hp, hr, _, hN, _, _, _⟩ := mem_originalLargeTriples.mp ht
  have hdp : t.2.1 ∣ t.1 :=
    (Nat.dvd_add_iff_left (dvd_mul_right t.2.1 t.2.2)).mpr (hN ▸ hd)
  exact ((Nat.prime_dvd_prime_iff_eq hr hp).mp hdp).symm

theorem originalLargeTriple_exceptional_prime_eq_source {N : ℕ} {a η : ℝ}
    {t : ℕ × ℕ × ℕ} (ht : t ∈ originalLargeTriplesExceptional N a η) :
    t.1 = t.2.1 := by
  obtain ⟨ht, hc⟩ := mem_filter.mp ht
  apply originalLargeTriple_prime_eq_source_of_dvd ht
  by_contra hd
  exact hc ((mem_originalLargeTriples.mp ht).2.1.coprime_iff_not_dvd.mpr hd)

theorem originalLargeTriplesExceptional_source_injOn (N : ℕ) (a η : ℝ) :
    Set.InjOn (fun t : ℕ × ℕ × ℕ => t.2.1)
      (originalLargeTriplesExceptional N a η : Set (ℕ × ℕ × ℕ)) := by
  intro t ht u hu hr
  change t.2.1 = u.2.1 at hr
  have hp : t.1 = u.1 := by
    rw [originalLargeTriple_exceptional_prime_eq_source ht,
      originalLargeTriple_exceptional_prime_eq_source hu]
    exact hr
  apply originalLargeTripleIndex_injOn N a η (mem_filter.mp ht).1 (mem_filter.mp hu).1
  change (⟨t.2.1, t.1⟩ : Σ _ : ℕ, ℕ) = ⟨u.2.1, u.1⟩
  rw [hr, hp]

theorem originalLargeTriplesExceptional_card_le (N : ℕ) (a η : ℝ) :
    (originalLargeTriplesExceptional N a η).card ≤ ⌊Real.sqrt N⌋₊ + 1 := by
  apply le_trans
    (card_le_card_of_injOn (fun t : ℕ × ℕ × ℕ => t.2.1)
      (t := range (⌊Real.sqrt N⌋₊ + 1)) ?_
      (originalLargeTriplesExceptional_source_injOn N a η))
    (by rw [card_range])
  intro t ht
  change t.2.1 ∈ range (⌊Real.sqrt N⌋₊ + 1)
  simpa only [mem_range, Nat.lt_succ_iff, Nat.le_floor_iff (Real.sqrt_nonneg _)]
    using originalLargeTriple_source_le_sqrt (mem_filter.mp ht).1

theorem originalLargeTripleCount_eq_coprime_add_exceptional (N : ℕ) (a η : ℝ) :
    originalLargeTripleCount N a η =
      (originalLargeTriplesCoprime N a η).card +
        (originalLargeTriplesExceptional N a η).card := by
  exact (card_filter_add_card_filter_not _).symm

theorem originalLargeTripleCount_le_tail_add_sqrt {N : ℕ} {a η : ℝ}
    (ha : 1 < a) (hη : 0 ≤ η) :
    originalLargeTripleCount N a η ≤
      tailOriginalSum N (η ^ ((a - 1) / a)) ((a - 1) / a) η +
        (⌊Real.sqrt N⌋₊ + 1) := by
  rw [originalLargeTripleCount_eq_coprime_add_exceptional]
  exact Nat.add_le_add (originalLargeTriplesCoprime_card_le ha hη)
    (originalLargeTriplesExceptional_card_le N a η)

end
end Wu2004MeanValue
