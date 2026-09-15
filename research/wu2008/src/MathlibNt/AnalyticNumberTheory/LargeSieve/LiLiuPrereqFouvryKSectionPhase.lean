import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryKSectionPair
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvrySievedReciprocal

/-!
# Freezing the actual small root and reducing the paired sieve

The residue modulus is the small key modulus `D'`, not the reciprocal
modulus. Its unit conditions are derived from original tuple membership.
On a unit residue class, the only sieve cost not already supplied by
reciprocal nonunit vanishing is the divisor cost of `|a|`.
-/

noncomputable section
open Classical Finset

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

theorem wKSection_DPrime_pos {K : WExtractedKey} {r n₁ n₂ s : ℕ}
    (hf : wKSectionFixedCanonical K r n₁ n₂ s) : 0 < K.D' := by
  exact Nat.mul_pos (Nat.mul_pos hf.1 hf.2.1)
    (Nat.mul_pos (Nat.mul_pos hf.2.2.1 hf.2.2.2.1) hf.2.2.2.2.1)

/-- The original compatibility conditions force a unit residue modulo
the small root modulus. This is not an additional input to the producer. -/
theorem wKSectionTuple_coprime_DPrime
    {H : ℕ → ℕ → ℕ} {N Q : Finset ℕ}
    (hN : ∀ n ∈ N, 0 < n) (hQ : ∀ q ∈ Q, 0 < q)
    {a : ℤ} {P : WOriginalTuple → Prop} {R S ξ : ℝ} {b : ℕ}
    {K : WExtractedKey} {r n₁ n₂ s k : ℕ} {h : ℤ}
    (hf : wKSectionFixedCanonical K r n₁ n₂ s)
    (ht : wKSectionTuple K r n₁ n₂ s h k ∈
      wExtractedKeyFiber H N Q a P R S ξ b K) :
    k.Coprime K.D' := by
  have hcan := wKSectionTuple_canonical_of_mem hN hQ hf.1 hf.2.1
    hf.2.2.1 hf.2.2.2.1 ht
  have hz := (mem_wExtractedFrequencies_iff.mp
    (mem_filter.mp (mem_wExtractedKeyFiber_iff.mp ht).1).1).1
  obtain ⟨hv, hc⟩ := wExtractedOriginal_valid hN hQ hz
  rw [hcan] at hv
  have hp := (hv.phase_coprime hc).1
  change (n₁ * k * (r * s)).Coprime K.D' at hp
  exact (Nat.coprime_mul_iff_left.mp (Nat.coprime_mul_iff_left.mp hp).1).2

/-- Two real section members in the same `D'` residue have exactly the
same small-root factor, for either sign of the frequency and residue. -/
theorem wKSectionTuple_smallRoot_congr
    {H : ℕ → ℕ → ℕ} {N Q : Finset ℕ}
    (hN : ∀ n ∈ N, 0 < n) (hQ : ∀ q ∈ Q, 0 < q)
    {a : ℤ} {P : WOriginalTuple → Prop} {R S ξ : ℝ} {b : ℕ}
    {K : WExtractedKey} {r n₁ n₂ s k l : ℕ} {h : ℤ}
    (hf : wKSectionFixedCanonical K r n₁ n₂ s)
    (ht : wKSectionTuple K r n₁ n₂ s h k ∈
      wExtractedKeyFiber H N Q a P R S ξ b K)
    (hu : wKSectionTuple K r n₁ n₂ s h l ∈
      wExtractedKeyFiber H N Q a P R S ξ b K)
    (hkl : Nat.ModEq K.D' k l) :
    wActualSmallRootFactor a (wKSectionTuple K r n₁ n₂ s h k) =
      wActualSmallRootFactor a (wKSectionTuple K r n₁ n₂ s h l) := by
  have htcan := wKSectionTuple_canonical_of_mem hN hQ hf.1 hf.2.1
    hf.2.2.1 hf.2.2.2.1 ht
  have hucan := wKSectionTuple_canonical_of_mem hN hQ hf.1 hf.2.1
    hf.2.2.1 hf.2.2.2.1 hu
  have htz := (mem_wExtractedFrequencies_iff.mp
    (mem_filter.mp (mem_wExtractedKeyFiber_iff.mp ht).1).1).1
  have huz := (mem_wExtractedFrequencies_iff.mp
    (mem_filter.mp (mem_wExtractedKeyFiber_iff.mp hu).1).1).1
  obtain ⟨hvt, hct⟩ := wExtractedOriginal_valid hN hQ htz
  obtain ⟨hvu, hcu⟩ := wExtractedOriginal_valid hN hQ huz
  rw [htcan] at hvt
  rw [hucan] at hvu
  have he := wSmallRootPhase_congr hvt.d_pos hvt.d₁_pos hvt.D_pos
    hvt.δ_coprime (hvt.small_compatible hct) (hvu.small_compatible hcu)
    hvt.k_D hvu.k_D (hvt.phase_coprime hct).1 (hvu.phase_coprime hcu).1
    (Nat.ModEq.refl _) (Nat.ModEq.refl _) (hkl.mul_right (r * s)) a
  unfold wActualSmallRootFactor
  rw [htcan, hucan]
  exact congrArg (fourier h) he

/-- After the two inherent unit conditions, only `|a|` remains in the
paired arithmetic sieve. No divisor cost of `n₁*r*s*s'` is introduced. -/
theorem wKSectionCoprime_pair_iff_of_units
    (K : WExtractedKey) (a : ℤ) (r n₁ s s' k : ℕ)
    (hkD : k.Coprime K.D') (hkq : k.Coprime (n₁ * r * s * s')) :
    (wKSectionCoprime K a r n₁ s k ∧ wKSectionCoprime K a r n₁ s' k) ↔
      k.Coprime a.natAbs := by
  rw [wKSectionCoprime_iff, wKSectionCoprime_iff]
  dsimp only [WExtractedKey.D', WExtractedKey.D] at hkD
  simp only [Nat.coprime_mul_iff_right] at hkD hkq ⊢
  tauto

/-- Conversely, the actual paired sieve itself supplies the phase unit
condition, even before a residue class has been selected. -/
theorem wKSectionCoprime_pair_coprime_modulus
    {K : WExtractedKey} {a : ℤ} {r n₁ s s' k : ℕ}
    (hk : wKSectionCoprime K a r n₁ s k)
    (hk' : wKSectionCoprime K a r n₁ s' k) :
    k.Coprime (n₁ * r * s * s') := by
  rw [wKSectionCoprime_iff] at hk hk'
  simp only [Nat.coprime_mul_iff_right] at hk hk' ⊢
  tauto

/-- Exact sieve reduction with the nonunit-zero extension of the phase.
Thus nonunit points can be added back before using the analytic theorem. -/
theorem wKSection_sieved_phase_eq
    {K : WExtractedKey} {a : ℤ} {r n₁ s s' k : ℕ}
    [NeZero (n₁ * r * s * s')]
    (hkD : k.Coprime K.D') (d : ℤ) :
    (if wKSectionCoprime K a r n₁ s k ∧ wKSectionCoprime K a r n₁ s' k
      then reciprocalPhase (n₁ * r * s * s') d k else 0) =
      if k.Coprime a.natAbs then reciprocalPhase (n₁ * r * s * s') d k else 0 := by
  by_cases hkq : k.Coprime (n₁ * r * s * s')
  · simp only [wKSectionCoprime_pair_iff_of_units K a r n₁ s s' k hkD hkq]
  · have hz : reciprocalPhase (n₁ * r * s * s') d k = 0 := by
      rw [reciprocalPhase, if_neg]
      exact fun hu => hkq ((ZMod.isUnit_iff_coprime k _).mp hu)
    simp only [hz, ite_self]

/-- The reciprocal twist and the small residue step are units on a real
paired section. The displayed phase equality uses the zero-extended
reciprocal function only at its legitimate unit points. -/
theorem wKSectionPair_phase_data
    {H : ℕ → ℕ → ℕ} {N Q : Finset ℕ}
    (hN : ∀ n ∈ N, 0 < n) (hQ : ∀ q ∈ Q, 0 < q)
    {a : ℤ} {x η R S : ℝ} {b : ℕ} {K : WExtractedKey}
    {U : Finset (WExtractedTuple × ℤ)}
    (hU : U ⊆ wExtractedKeyFiber H N Q a (c2FiveSmallMask x η)
      R S (highOmegaCutoff x) b K)
    {c : Finset (ℕ × ℕ)} {r n₁ n₂ n₂' s s' k : ℕ} {h h' : ℤ}
    [NeZero (n₁ * r * s * s')]
    (hf : wKSectionFixedCanonical K r n₁ n₂ s)
    (hf' : wKSectionFixedCanonical K r n₁ n₂' s')
    (ht : wKSectionTuple K r n₁ n₂ s h k ∈ wCoprimeFiber x N S U c)
    (hu : wKSectionTuple K r n₁ n₂' s' h' k ∈ wCoprimeFiber x N S U c) :
    (K.D' * n₂ * n₂').Coprime (n₁ * r * s * s') ∧
      K.D'.Coprime (n₁ * r * s * s') ∧ k.Coprime K.D' ∧
      wActualReciprocalCorrelation K a
        (wKSectionTuple K r n₁ n₂ s h k) (wKSectionTuple K r n₁ n₂' s' h' k) =
        reciprocalPhase (n₁ * r * s * s')
          (iv3CorrelationNumerator K.1.2.1 n₁ n₂ n₂' s s' a h h' *
            wPhaseInverse (K.D' * n₂ * n₂') (n₁ * r * s * s')) k := by
  have htf := hU (mem_filter.mp ht).1
  have huf := hU (mem_filter.mp hu).1
  have htcan := wKSectionTuple_canonical_of_mem hN hQ hf.1 hf.2.1
    hf.2.2.1 hf.2.2.2.1 htf
  have hucan := wKSectionTuple_canonical_of_mem hN hQ hf'.1 hf'.2.1
    hf'.2.2.1 hf'.2.2.2.1 huf
  have hp := wCoprimeFiber_common_inverse_coprime hN hQ hU ht hu
    (by rw [htcan, hucan]; rfl) rfl (by rw [htcan, hucan]; rfl)
  rw [htcan, hucan] at hp
  change (K.D' * n₂ * n₂' * k).Coprime (n₁ * r * s * s') at hp
  obtain ⟨hB, hk⟩ := Nat.coprime_mul_iff_left.mp hp
  refine ⟨hB, (Nat.coprime_mul_iff_left.mp (Nat.coprime_mul_iff_left.mp hB).1).1,
    wKSectionTuple_coprime_DPrime hN hQ hf htf, ?_⟩
  unfold wActualReciprocalCorrelation wActualCorrelationModulus
    wActualCorrelationNumerator
  rw [htcan, hucan]
  exact iv3ReciprocalCircle_eq_reciprocalPhase hB hk _

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
