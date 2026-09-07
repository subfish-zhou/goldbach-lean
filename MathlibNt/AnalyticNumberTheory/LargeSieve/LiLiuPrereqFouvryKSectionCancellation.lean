import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryKSectionPhase

/-!
# Individual cancellation on a real IV.3 paired section

Both floor cutoffs and all original filters are retained. Small-root
freezing and the exact sieve reduction connect this carrier to the
proved reciprocal interval theorem, with only `tau(|a|)` as sieve cost.
-/

noncomputable section
open Classical Finset

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

def wKSectionPairResidueSum
    (N : Finset ℕ) (a : ℤ) (x η R S M Z : ℝ) (K : WExtractedKey)
    (r n₁ n₂ n₂' s s' : ℕ) (h h' : ℤ) (b : ℕ)
    (j cap : Fin 5 → ℕ) (positive : Bool) (c : Finset (ℕ × ℕ)) (v : ℕ) : ℂ :=
  ∑ k ∈ (wKSectionCarrier N a x η R S M Z K r n₁ n₂ s h b j cap positive c ∩
      wKSectionCarrier N a x η R S M Z K r n₁ n₂' s' h' b j cap positive c).filter
        (fun k => k % K.D' = v % K.D'),
    (wActualSmallRootFactor a (wKSectionTuple K r n₁ n₂ s h k) *
      star (wActualSmallRootFactor a (wKSectionTuple K r n₁ n₂' s' h' k))) *
      wActualReciprocalCorrelation K a (wKSectionTuple K r n₁ n₂ s h k)
        (wKSectionTuple K r n₁ n₂' s' h' k)

def wKSectionPairSum
    (N : Finset ℕ) (a : ℤ) (x η R S M Z : ℝ) (K : WExtractedKey)
    (r n₁ n₂ n₂' s s' : ℕ) (h h' : ℤ) (b : ℕ)
    (j cap : Fin 5 → ℕ) (positive : Bool) (c : Finset (ℕ × ℕ)) : ℂ :=
  ∑ k ∈ wKSectionCarrier N a x η R S M Z K r n₁ n₂ s h b j cap positive c ∩
      wKSectionCarrier N a x η R S M Z K r n₁ n₂' s' h' b j cap positive c,
    (wActualSmallRootFactor a (wKSectionTuple K r n₁ n₂ s h k) *
      star (wActualSmallRootFactor a (wKSectionTuple K r n₁ n₂' s' h' k))) *
      wActualReciprocalCorrelation K a (wKSectionTuple K r n₁ n₂ s h k)
        (wKSectionTuple K r n₁ n₂' s' h' k)

theorem wKSectionPairSum_eq_residues
    (N : Finset ℕ) (a : ℤ) (x η R S M Z : ℝ) (K : WExtractedKey)
    (r n₁ n₂ n₂' s s' : ℕ) (h h' : ℤ) (b : ℕ)
    (j cap : Fin 5 → ℕ) (positive : Bool) (c : Finset (ℕ × ℕ))
    (hD : 0 < K.D') :
    wKSectionPairSum N a x η R S M Z K r n₁ n₂ n₂' s s' h h' b j cap positive c =
      ∑ v ∈ range K.D',
        wKSectionPairResidueSum N a x η R S M Z K r n₁ n₂ n₂' s s'
          h h' b j cap positive c v := by
  let T := wKSectionCarrier N a x η R S M Z K r n₁ n₂ s h b j cap positive c ∩
    wKSectionCarrier N a x η R S M Z K r n₁ n₂' s' h' b j cap positive c
  let F := fun k =>
    (wActualSmallRootFactor a (wKSectionTuple K r n₁ n₂ s h k) *
      star (wActualSmallRootFactor a (wKSectionTuple K r n₁ n₂' s' h' k))) *
      wActualReciprocalCorrelation K a (wKSectionTuple K r n₁ n₂ s h k)
        (wKSectionTuple K r n₁ n₂' s' h' k)
  change ∑ k ∈ T, F k = ∑ v ∈ range K.D',
    ∑ k ∈ T.filter (fun k => k % K.D' = v % K.D'), F k
  calc
    _ = ∑ v ∈ range K.D', ∑ k ∈ T.filter (fun k => k % K.D' = v), F k :=
      (sum_fiberwise_of_maps_to (fun k _ => mem_range.mpr (Nat.mod_lt k hD)) F).symm
    _ = _ := by
      apply sum_congr rfl
      intro v hv
      rw [Nat.mod_eq_of_lt (mem_range.mp hv)]

theorem wKSectionPairResidueSum_norm_eq
    {N : Finset ℕ} (hN : ∀ n ∈ N, 0 < n)
    {a : ℤ} {x η R S M Z : ℝ} (hR : 0 ≤ R) (hS : 0 ≤ S)
    (hM : 0 < M) (hZ : 0 < Z)
    {K : WExtractedKey} {r n₁ n₂ n₂' s s' : ℕ} {h h' : ℤ} {b k₀ : ℕ}
    [NeZero (n₁ * r * s * s')]
    (hf : wKSectionFixedCanonical K r n₁ n₂ s)
    (hf' : wKSectionFixedCanonical K r n₁ n₂' s')
    (hΔ : 0 < K.2) (hΔ' : 0 < wKSectionDeltaPrime K)
    (he : K.2 * wKSectionDeltaPrime K = K.1.2.2.1 * K.1.2.2.2.2)
    (j cap : Fin 5 → ℕ) (positive : Bool) (c : Finset (ℕ × ℕ))
    (hk₀ : k₀ ∈
      wKSectionCarrier N a x η R S M Z K r n₁ n₂ s h b j cap positive c ∩
      wKSectionCarrier N a x η R S M Z K r n₁ n₂' s' h' b j cap positive c) :
    ‖wKSectionPairResidueSum N a x η R S M Z K r n₁ n₂ n₂' s s'
      h h' b j cap positive c k₀‖ =
    ‖sievedReciprocalInterval (n₁ * r * s * s')
      (iv3CorrelationNumerator K.1.2.1 n₁ n₂ n₂' s s' a h h' *
        wPhaseInverse (K.D' * n₂ * n₂') (n₁ * r * s * s'))
      k₀ K.D' a.natAbs
      (max (wKSectionGridLower M Z K r s h j) (wKSectionGridLower M Z K r s' h' j))
      (wKSectionGridUpper R S K j cap)‖ := by
  let U := wAnalyticPrefix (wAnalyticDyadicBlock
    (wExtractedKeyFiber (wFloorCutoff M Z) N (Ioc 0 ⌊R * S⌋₊) a
      (c2FiveSmallMask x η) R S (highOmegaCutoff x) b K) j positive) cap
  have hU : U ⊆ wExtractedKeyFiber (wFloorCutoff M Z) N (Ioc 0 ⌊R * S⌋₊) a
      (c2FiveSmallMask x η) R S (highOmegaCutoff x) b K := by
    intro t ht
    exact (mem_filter.mp (mem_filter.mp ht).1).1
  have hQ : ∀ q ∈ Ioc 0 ⌊R * S⌋₊, 0 < q := fun _ hq => (mem_Ioc.mp hq).1
  have hmem (k : ℕ) := wKSectionTuple_mem_filtered_iff (k := k) (h := h) (b := b)
    (a := a) (x := x) (η := η) hN hR hS hM hZ hf hΔ hΔ' he j cap positive c
  have hmem' (k : ℕ) := wKSectionTuple_mem_filtered_iff (k := k) (h := h') (b := b)
    (a := a) (x := x) (η := η) hN hR hS hM hZ hf' hΔ hΔ' he j cap positive c
  have ht₀ := (hmem k₀).mpr (mem_inter.mp hk₀).1
  have hu₀ := (hmem' k₀).mpr (mem_inter.mp hk₀).2
  have hdata₀ := wKSectionPair_phase_data hN hQ hU hf hf' ht₀ hu₀
  have hp := (mem_filter.mp (mem_inter.mp hk₀).1).2
  have hp' := (mem_filter.mp (mem_inter.mp hk₀).2).2
  let root := wActualSmallRootFactor a (wKSectionTuple K r n₁ n₂ s h k₀) *
    star (wActualSmallRootFactor a (wKSectionTuple K r n₁ n₂' s' h' k₀))
  have heq : wKSectionPairResidueSum N a x η R S M Z K r n₁ n₂ n₂' s s'
      h h' b j cap positive c k₀ =
      root * sievedReciprocalInterval (n₁ * r * s * s')
        (iv3CorrelationNumerator K.1.2.1 n₁ n₂ n₂' s s' a h h' *
          wPhaseInverse (K.D' * n₂ * n₂') (n₁ * r * s * s'))
        k₀ K.D' a.natAbs
        (max (wKSectionGridLower M Z K r s h j) (wKSectionGridLower M Z K r s' h' j))
        (wKSectionGridUpper R S K j cap) := by
    unfold wKSectionPairResidueSum sievedReciprocalInterval
    rw [wKSectionCarrier_inter, filter_filter, sum_filter, mul_sum]
    apply sum_congr rfl
    intro k hk
    by_cases hmod : k % K.D' = k₀ % K.D'
    · have hkD : k.Coprime K.D' :=
        (Nat.ModEq.gcd_eq hmod).trans hdata₀.2.2.1
      by_cases hcp : wKSectionCoprime K a r n₁ s k ∧ wKSectionCoprime K a r n₁ s' k
      · have hck : k ∈
            wKSectionCarrier N a x η R S M Z K r n₁ n₂ s h b j cap positive c ∩
            wKSectionCarrier N a x η R S M Z K r n₁ n₂' s' h' b j cap positive c := by
          rw [wKSectionCarrier_inter]
          exact mem_filter.mpr ⟨hk, ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, hcp.1⟩,
            ⟨hp'.1, hp'.2.1, hp'.2.2.1, hp'.2.2.2.1, hcp.2⟩⟩
        have ht := (hmem k).mpr (mem_inter.mp hck).1
        have hu := (hmem' k).mpr (mem_inter.mp hck).2
        have hdata := wKSectionPair_phase_data hN hQ hU hf hf' ht hu
        have hroot := wKSectionTuple_smallRoot_congr hN hQ hf
          (hU (mem_filter.mp ht).1) (hU (mem_filter.mp ht₀).1) hmod
        have hroot' := wKSectionTuple_smallRoot_congr hN hQ hf'
          (hU (mem_filter.mp hu).1) (hU (mem_filter.mp hu₀).1) hmod
        have hka : k.Coprime a.natAbs := hcp.1.2.2.1.symm
        simp only [hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, hp'.1, hp'.2.1,
          hp'.2.2.1, hp'.2.2.2.1, hcp.1, hcp.2, hmod, and_self, if_true, true_and,
          hroot, hroot', hdata.2.2.2, root]
        rw [if_pos hka]
      · have hz := wKSection_sieved_phase_eq (a := a) (r := r) (n₁ := n₁)
          (s := s) (s' := s') hkD
          (iv3CorrelationNumerator K.1.2.1 n₁ n₂ n₂' s s' a h h' *
            wPhaseInverse (K.D' * n₂ * n₂') (n₁ * r * s * s'))
        simp only [if_neg hcp] at hz
        simp only [hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, hp'.1, hp'.2.1,
          hp'.2.2.1, hp'.2.2.2.1, true_and, hmod, and_true, if_neg hcp,
          ← hz, mul_zero]
    · simp only [hmod, and_false, false_and, if_false, mul_zero]
  rw [heq, norm_mul]
  have hroot : ‖root‖ = 1 := by
    simp only [root, norm_mul, norm_star, norm_wActualSmallRootFactor, mul_one]
  rw [hroot, one_mul]

/-- Uniform individual cancellation on every residue section of the
actual paired carrier, including empty sections. The common inverse and
the admissible progression step are proved from a member, not assumed. -/
theorem wKSectionPairResidueSum_fouvry {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (N : Finset ℕ) (a : ℤ) (x η R S M Z : ℝ) (K : WExtractedKey)
      (r n₁ n₂ n₂' s s' : ℕ) (h h' : ℤ) (b : ℕ)
      (j cap : Fin 5 → ℕ) (positive : Bool) (c : Finset (ℕ × ℕ)) (v : ℕ),
      (∀ n ∈ N, 0 < n) → a ≠ 0 → 0 ≤ R → 0 ≤ S → 0 < M → 0 < Z →
      wKSectionFixedCanonical K r n₁ n₂ s →
      wKSectionFixedCanonical K r n₁ n₂' s' →
      0 < K.2 → 0 < wKSectionDeltaPrime K →
      K.2 * wKSectionDeltaPrime K = K.1.2.2.1 * K.1.2.2.2.2 →
      ‖wKSectionPairResidueSum N a x η R S M Z K r n₁ n₂ n₂' s s'
        h h' b j cap positive c v‖ ≤
        C * (a.natAbs.divisors.card : ℝ) *
          (1 + ((wKSectionGridUpper R S K j cap -
            max (wKSectionGridLower M Z K r s h j)
              (wKSectionGridLower M Z K r s' h' j) + 1 : ℕ) : ℝ) /
              ((K.D' : ℝ) * (n₁ * r * s * s' : ℕ))) *
          Real.sqrt ((n₁ * r * s * s').gcd
            (iv3CorrelationNumerator K.1.2.1 n₁ n₂ n₂' s s' a h h').natAbs) *
          (n₁ * r * s * s' : ℕ) ^ (1 / 2 + ε : ℝ) := by
  obtain ⟨C, hC, hbound⟩ := sievedReciprocalInterval_fouvry hε
  refine ⟨C, hC, ?_⟩
  intro N a x η R S M Z K r n₁ n₂ n₂' s s' h h' b j cap positive c v
    hN ha hR hS hM hZ hf hf' hΔ hΔ' he
  let T := wKSectionCarrier N a x η R S M Z K r n₁ n₂ s h b j cap positive c ∩
    wKSectionCarrier N a x η R S M Z K r n₁ n₂' s' h' b j cap positive c
  by_cases hne : (T.filter (fun k => k % K.D' = v % K.D')).Nonempty
  · obtain ⟨k₀, hk⟩ := hne
    obtain ⟨hk₀, hkv⟩ := mem_filter.mp hk
    have hq : 0 < n₁ * r * s * s' :=
      Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hf.2.2.2.2.2.2.2.1
        hf.2.2.2.2.2.1) hf.2.2.2.2.2.2.1) hf'.2.2.2.2.2.2.1
    let : NeZero (n₁ * r * s * s') := ⟨hq.ne'⟩
    have hsame : wKSectionPairResidueSum N a x η R S M Z K r n₁ n₂ n₂' s s'
        h h' b j cap positive c v =
        wKSectionPairResidueSum N a x η R S M Z K r n₁ n₂ n₂' s s'
          h h' b j cap positive c k₀ := by
      simp only [wKSectionPairResidueSum, hkv]
    rw [hsame, wKSectionPairResidueSum_norm_eq hN hR hS hM hZ
      hf hf' hΔ hΔ' he j cap positive c hk₀]
    let U := wAnalyticPrefix (wAnalyticDyadicBlock
      (wExtractedKeyFiber (wFloorCutoff M Z) N (Ioc 0 ⌊R * S⌋₊) a
        (c2FiveSmallMask x η) R S (highOmegaCutoff x) b K) j positive) cap
    have hU : U ⊆ wExtractedKeyFiber (wFloorCutoff M Z) N (Ioc 0 ⌊R * S⌋₊) a
        (c2FiveSmallMask x η) R S (highOmegaCutoff x) b K := by
      intro t ht
      exact (mem_filter.mp (mem_filter.mp ht).1).1
    have ht := (wKSectionTuple_mem_filtered_iff hN hR hS hM hZ hf hΔ hΔ' he
      j cap positive c).mpr (mem_inter.mp hk₀).1
    have hu := (wKSectionTuple_mem_filtered_iff hN hR hS hM hZ hf' hΔ hΔ' he
      j cap positive c).mpr (mem_inter.mp hk₀).2
    have hd := wKSectionPair_phase_data hN (fun _ hq => (mem_Ioc.mp hq).1)
      hU hf hf' ht hu
    have hb := hbound (n₁ * r * s * s') inferInstance
      (iv3CorrelationNumerator K.1.2.1 n₁ n₂ n₂' s s' a h h' *
        wPhaseInverse (K.D' * n₂ * n₂') (n₁ * r * s * s')) k₀ K.D' a.natAbs
      (max (wKSectionGridLower M Z K r s h j) (wKSectionGridLower M Z K r s' h' j))
      (wKSectionGridUpper R S K j cap) (wKSection_DPrime_pos hf) hd.2.1 hd.2.2.1
      (Nat.pos_of_ne_zero (Int.natAbs_ne_zero.mpr ha))
    rw [iv3_gcd_inverse_twist hd.1] at hb
    exact hb
  · have hempty := not_nonempty_iff_eq_empty.mp hne
    unfold wKSectionPairResidueSum
    change ‖∑ k ∈ T.filter (fun k => k % K.D' = v % K.D'), _‖ ≤ _
    rw [hempty, sum_empty, norm_zero]
    positivity

/-- The cost of freezing all small-root residues is explicit. After
summing them, it is `D' + span/q`, not a loss of the interval saving. -/
theorem wKSectionPairSum_fouvry {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (N : Finset ℕ) (a : ℤ) (x η R S M Z : ℝ) (K : WExtractedKey)
      (r n₁ n₂ n₂' s s' : ℕ) (h h' : ℤ) (b : ℕ)
      (j cap : Fin 5 → ℕ) (positive : Bool) (c : Finset (ℕ × ℕ)),
      (∀ n ∈ N, 0 < n) → a ≠ 0 → 0 ≤ R → 0 ≤ S → 0 < M → 0 < Z →
      wKSectionFixedCanonical K r n₁ n₂ s →
      wKSectionFixedCanonical K r n₁ n₂' s' →
      0 < K.2 → 0 < wKSectionDeltaPrime K →
      K.2 * wKSectionDeltaPrime K = K.1.2.2.1 * K.1.2.2.2.2 →
      ‖wKSectionPairSum N a x η R S M Z K r n₁ n₂ n₂' s s'
        h h' b j cap positive c‖ ≤
        C * (a.natAbs.divisors.card : ℝ) *
          ((K.D' : ℝ) + ((wKSectionGridUpper R S K j cap -
            max (wKSectionGridLower M Z K r s h j)
              (wKSectionGridLower M Z K r s' h' j) + 1 : ℕ) : ℝ) /
              (n₁ * r * s * s' : ℕ)) *
          Real.sqrt ((n₁ * r * s * s').gcd
            (iv3CorrelationNumerator K.1.2.1 n₁ n₂ n₂' s s' a h h').natAbs) *
          (n₁ * r * s * s' : ℕ) ^ (1 / 2 + ε : ℝ) := by
  obtain ⟨C, hC, hbound⟩ := wKSectionPairResidueSum_fouvry hε
  refine ⟨C, hC, ?_⟩
  intro N a x η R S M Z K r n₁ n₂ n₂' s s' h h' b j cap positive c
    hN ha hR hS hM hZ hf hf' hΔ hΔ' he
  have hD := wKSection_DPrime_pos hf
  rw [wKSectionPairSum_eq_residues N a x η R S M Z K r n₁ n₂ n₂' s s'
    h h' b j cap positive c hD]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _v ∈ range K.D',
        C * (a.natAbs.divisors.card : ℝ) *
          (1 + ((wKSectionGridUpper R S K j cap -
            max (wKSectionGridLower M Z K r s h j)
              (wKSectionGridLower M Z K r s' h' j) + 1 : ℕ) : ℝ) /
              ((K.D' : ℝ) * (n₁ * r * s * s' : ℕ))) *
          Real.sqrt ((n₁ * r * s * s').gcd
            (iv3CorrelationNumerator K.1.2.1 n₁ n₂ n₂' s s' a h h').natAbs) *
          (n₁ * r * s * s' : ℕ) ^ (1 / 2 + ε : ℝ) := by
      exact sum_le_sum (fun v _ => hbound N a x η R S M Z K r n₁ n₂ n₂' s s'
        h h' b j cap positive c v hN ha hR hS hM hZ hf hf' hΔ hΔ' he)
    _ = _ := by
      rw [sum_const, card_range, nsmul_eq_mul]
      have hDr : (K.D' : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hD.ne'
      field_simp

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
