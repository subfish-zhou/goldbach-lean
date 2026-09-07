import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryFactorExtraction
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryFactorHighOmegaReduction

/-!
# Canonical divisor extraction in the actual delayed W

Fouvry (1987), p. 627, §III.5: extract `δ δ₂` from `q₂ = r s`.
The explicit finite target retains the original support, compatibility, mask,
low omega of `s`, signed first coefficient, and exactly the same cutoff `H`.
This is a finite preprocessing identity, not (3.12) or an IV.3 estimate.
-/

noncomputable section
open Classical Finset

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

/-- This is `δ δ₂`, not `WGCDData.D = δ δ₁ δ₂`. -/
def wSecondExtractionDivisor (t : WOriginalTuple) : ℕ :=
  (wGCDTuple t).δ * (wGCDTuple t).δ₂

/-- Positivity of the original second modulus alone suffices. No conditions
on the beta indices, mask, or first modulus are hidden in this construction. -/
theorem wSecondExtractionDivisor_pos_dvd {t : WOriginalTuple} (ht : 0 < t.1.2) :
    0 < wSecondExtractionDivisor t ∧ wSecondExtractionDivisor t ∣ t.1.2 := by
  let δ := t.1.1.gcd t.1.2
  have hδ : 0 < δ := Nat.gcd_pos_of_pos_right t.1.1 ht
  have hd : δ ∣ t.1.2 := Nat.gcd_dvd_right t.1.1 t.1.2
  have hquot : 0 < t.1.2 / δ := Nat.div_pos (Nat.le_of_dvd ht hd) hδ
  change 0 < δ * supportedPart (t.1.2 / δ) δ ∧
    δ * supportedPart (t.1.2 / δ) δ ∣ t.1.2
  refine ⟨Nat.mul_pos hδ (supportedPart_pos _ _), coprimePart (t.1.2 / δ) δ, ?_⟩
  rw [mul_assoc, supportedPart_mul_coprimePart hquot, Nat.mul_div_cancel' hd]

/-- The auxiliary coordinates range over the original `q₁,n₁,n₂` box.
The remaining tests include low omega on the original second factor `s`. -/
def wFactorExtractionMask (Q : Finset ℕ) (a : ℤ) (P : WOriginalTuple → Prop)
    (ξ : ℝ) (r s : ℕ) (u : ℕ × (ℕ × ℕ)) : Prop :=
  (s.primeFactors.card : ℝ) ≤ ξ ∧ r * s ∈ reducedModuli Q a ∧
    WCompatible u.1 (r * s) u.2.1 u.2.2 ∧ P ((u.1, r * s), u.2)

def wFactorExtractionTuples (N Q : Finset ℕ) (a : ℤ) (P : WOriginalTuple → Prop)
    (R S ξ : ℝ) : Finset (FactorExtractionTuple × (ℕ × (ℕ × ℕ))) :=
  factorExtractionTarget ⌊R⌋₊ ⌊S⌋₊ (reducedModuli Q a ×ˢ (N ×ˢ N))
    (fun r s u => wSecondExtractionDivisor ((u.1, r * s), u.2))
    (wFactorExtractionMask Q a P ξ)

theorem mem_wFactorExtractionTuples_iff {N Q : Finset ℕ} {a : ℤ}
    {P : WOriginalTuple → Prop} {R S ξ : ℝ}
    {z : FactorExtractionTuple × (ℕ × (ℕ × ℕ))} :
    z ∈ wFactorExtractionTuples N Q a P R S ξ ↔
      let r := z.1.1.1 * z.1.2.1
      let s := z.1.1.2 * z.1.2.2
      z.1.1.1 ∈ Ioc 0 ⌊R⌋₊ ∧ z.1.1.2 ∈ Ioc 0 ⌊S⌋₊ ∧
      z.1.2.1 ∈ Ioc 0 ⌊R⌋₊ ∧ z.1.2.2 ∈ Ioc 0 ⌊S⌋₊ ∧
      r ≤ ⌊R⌋₊ ∧ s ≤ ⌊S⌋₊ ∧
      z.2.1 ∈ reducedModuli Q a ∧ z.2.2.1 ∈ N ∧ z.2.2.2 ∈ N ∧
      r * s ∈ reducedModuli Q a ∧
      WCompatible z.2.1 (r * s) z.2.2.1 z.2.2.2 ∧ P ((z.2.1, r * s), z.2.2) ∧
      (s.primeFactors.card : ℝ) ≤ ξ ∧
      wSecondExtractionDivisor ((z.2.1, r * s), z.2.2) = z.1.1.1 * z.1.1.2 ∧
      z.1.2.2.Coprime z.1.1.1 := by
  simp only [wFactorExtractionTuples, factorExtractionTarget, mem_filter, mem_product]
  simp only [wFactorExtractionMask]
  tauto

/-- The actual W after the unique arithmetic extraction. In particular the
second modulus is `(Δ*r')*(Δ'*s')`, not a free or enlarged modulus variable. -/
def wMaskedFactorExtractedTruncated (M : ℝ) (H : ℕ → ℕ → ℕ)
    (N Q : Finset ℕ) (β c₁ γ ζ : ℕ → ℝ) (a : ℤ)
    (P : WOriginalTuple → Prop) (R S ξ : ℝ) : ℝ :=
  ∑ z ∈ wFactorExtractionTuples N Q a P R S ξ,
    γ (z.1.1.1 * z.1.2.1) * ζ (z.1.1.2 * z.1.2.2) *
      wSecondModulusKernel M H β c₁ a
        ((z.2.1, (z.1.1.1 * z.1.2.1) * (z.1.1.2 * z.1.2.2)), z.2.2)

/-- Exact transport of the accepted delayed sum, with no sign assumptions
and no new support or coprimality premises supplied by the caller. -/
theorem wMaskedFactoredTruncated_eq_extracted
    (M : ℝ) (H : ℕ → ℕ → ℕ) (N Q : Finset ℕ)
    (β c₁ γ ζ : ℕ → ℝ) (a : ℤ) (P : WOriginalTuple → Prop) (R S ξ : ℝ) :
    wMaskedFactoredTruncated M H N Q β c₁ γ ζ a P R S ξ =
      wMaskedFactorExtractedTruncated M H N Q β c₁ γ ζ a P R S ξ := by
  let U := reducedModuli Q a ×ˢ (N ×ˢ N)
  let D := fun r s (u : ℕ × (ℕ × ℕ)) =>
    wSecondExtractionDivisor ((u.1, r * s), u.2)
  let mask := wFactorExtractionMask Q a P ξ
  let F := fun z : (ℕ × ℕ) × (ℕ × (ℕ × ℕ)) =>
    γ z.1.1 * ζ z.1.2 *
      wSecondModulusKernel M H β c₁ a ((z.2.1, z.1.1 * z.1.2), z.2.2)
  have hd : ∀ z ∈ factorExtractionSource ⌊R⌋₊ ⌊S⌋₊ U mask,
      0 < D z.1.1 z.1.2 z.2 ∧ D z.1.1 z.1.2 z.2 ∣ z.1.1 * z.1.2 := by
    intro z hz
    obtain ⟨hz, _⟩ := mem_filter.mp hz
    obtain ⟨hp, _⟩ := mem_product.mp hz
    obtain ⟨hr, hs⟩ := mem_product.mp hp
    exact wSecondExtractionDivisor_pos_dvd
      (Nat.mul_pos (mem_Ioc.mp hr).1 (mem_Ioc.mp hs).1)
  calc
    _ = ∑ z ∈ factorExtractionSource ⌊R⌋₊ ⌊S⌋₊ U mask, F z := by
      simp only [wMaskedFactoredTruncated, factorExtractionSource, sum_filter, sum_product]
      apply sum_congr rfl
      intro r _
      apply sum_congr rfl
      intro s _
      by_cases hs : (s.primeFactors.card : ℝ) ≤ ξ
      · simp [mask, wFactorExtractionMask, hs, U, F, wDelayedTuples, sum_filter]
      · simp [mask, wFactorExtractionMask, hs]
    _ = _ := sum_factorExtraction ⌊R⌋₊ ⌊S⌋₊ U D mask hd F

/-- The same exact transport starting from the original masked retained W.
Only its second coefficient is expanded, and the first copy of `c` survives. -/
theorem wMaskedTruncated_eq_factorExtracted_of_eq
    {R S ξ : ℝ} {γ ζ c : ℕ → ℝ}
    (hγ : factorSupported R γ) (hζ : factorSupported S ζ)
    (hc : c = factorConvolution γ (betaLowOmega ζ ξ))
    (M : ℝ) (H : ℕ → ℕ → ℕ) (N Q : Finset ℕ)
    (β : ℕ → ℝ) (a : ℤ) (P : WOriginalTuple → Prop) :
    wMaskedTruncated M H N Q β c a P =
      wMaskedFactorExtractedTruncated M H N Q β c γ ζ a P R S ξ := by
  rw [wMaskedTruncated_eq_factored_of_eq hγ hζ hc,
    wMaskedFactoredTruncated_eq_extracted]

/-- The exact W which occurs at the accepted C.2 preprocessing endpoint:
the first coefficient remains the trimmed convolution, beta remains clean,
all five-small conditions survive, and the cutoff is unchanged. -/
theorem c2FiveSmall_factored_eq_extracted
    (M x η R S : ℝ) (N Q : Finset ℕ) (β γ ζ : ℕ → ℝ) (a : ℤ) :
    wMaskedFactoredTruncated M (wUniformCutoff M (x ^ η)) N Q
      (betaClean β a) (factorConvolution γ (betaLowOmega ζ (highOmegaCutoff x)))
      γ ζ a (c2FiveSmallMask x η) R S (highOmegaCutoff x) =
    wMaskedFactorExtractedTruncated M (wUniformCutoff M (x ^ η)) N Q
      (betaClean β a) (factorConvolution γ (betaLowOmega ζ (highOmegaCutoff x)))
      γ ζ a (c2FiveSmallMask x η) R S (highOmegaCutoff x) :=
  wMaskedFactoredTruncated_eq_extracted M _ N Q _ _ γ ζ a _ R S _

open Filter
open scoped Topology

/-- Original WF error at the constructed canonical-extraction endpoint.
All factors are chosen before the changing residue, and no interval
structure or estimate of the surviving oscillatory sum is assumed. -/
theorem wellFactorable_signedError_sq_le_five_small_extracted_c2
    {ι : Type*} {κ k i j : ℕ} (A : ℕ)
    {T : ι → ℝ} {N : ι → Finset ℕ} {β : ι → ℕ → ℝ}
    (hSW : BetaCoprimeSWFamily κ T N β) (hT : ∀ z, 1 ≤ T z)
    (hN : ∀ z, ∀ n ∈ N z, T z ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * T z)
    (hβ : ∀ z, ∀ n ∈ N z, |β z n| ≤ (fouvryTau k n : ℝ))
    {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∀ᶠ x : ℝ in atTop, ∀ z : ι, ∀ M ν : ℝ,
      1 ≤ M → 4 * M * T z = x →
      ε ≤ ν → ν ≤ 1 / 10 → T z = x ^ ν →
      ∀ S Q : Finset ℕ,
      (∀ m ∈ S, M ≤ (m : ℝ) ∧ (m : ℝ) ≤ 2 * M) →
      Q ⊆ Ioc 0 ⌊x ^ ((5 - 5 * ν) / 9 - ε)⌋₊ →
      ∀ α c : ℕ → ℝ,
      (∀ m ∈ S, |α m| ≤ (fouvryTau i m : ℝ)) →
      SignedWellFactorable j (x ^ ((5 - 5 * ν) / 9 - ε)) c →
      let R₀ := x ^ c2RExponent ν ε
      let S₀ := x ^ c2SExponent ν ε
      R₀ * S₀ = x ^ ((5 - 5 * ν) / 9 - ε) ∧
        ∃ γ ζ : ℕ → ℝ,
          factorSupported R₀ γ ∧ factorSupported S₀ ζ ∧
          (∀ r, |γ r| ≤ (fouvryTau j r : ℝ)) ∧
          (∀ s, |ζ s| ≤ (fouvryTau j s : ℝ)) ∧ c = factorConvolution γ ζ ∧
          ∀ a : ℤ, a ≠ 0 → |(a : ℝ)| ≤ x →
          signedError S (N z) Q α (β z) c a ^ 2 ≤
            8 * (∑ m ∈ S, α m ^ 2) *
              wMaskedFactorExtractedTruncated M (wUniformCutoff M (x ^ η)) (N z) Q
                (betaClean (β z) a)
                (factorConvolution γ (betaLowOmega ζ (highOmegaCutoff x)))
                γ ζ a (c2FiveSmallMask x η) R₀ S₀ (highOmegaCutoff x) +
              x ^ 2 / Real.log x ^ A := by
  simpa only [c2FiveSmall_factored_eq_extracted] using
    (wellFactorable_signedError_sq_le_five_small_factored_c2
      (i := i) (j := j) A hSW hT hN hβ hε hη)

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
