import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryFactorConvolution
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryMaskedW

/-!
# Delayed decomposition of the second modulus coefficient

Fouvry (1987), p. 627, §III.5, decomposes only the second coefficient,
after all arithmetic restrictions and the frequency truncation are fixed.
The finite identities below retain signed coefficients, the original mask,
and the original modulus-dependent cutoff. No factorability of the
low-omega convolution, or interval structure of an arithmetic fiber, is used.
The further canonical `Δ, Δ'` extraction and Fourier estimates are not
asserted here.
-/

noncomputable section
open Classical Finset

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

/-- Closed positive factor supports turn the divisor antidiagonal into an
exact rectangular sum, including at modulus zero. -/
theorem factorConvolution_eq_sum_box {R S : ℝ} {γ ζ : ℕ → ℝ}
    (hγ : factorSupported R γ) (hζ : factorSupported S ζ) (q : ℕ) :
    factorConvolution γ ζ q =
      ∑ r ∈ Ioc 0 ⌊R⌋₊, ∑ s ∈ Ioc 0 ⌊S⌋₊,
        if r * s = q then γ r * ζ s else 0 := by
  let B := ((Ioc 0 ⌊R⌋₊) ×ˢ (Ioc 0 ⌊S⌋₊)).filter
    (fun p : ℕ × ℕ => p.1 * p.2 = q)
  have hB : B ⊆ q.divisorsAntidiagonal := by
    intro p hp
    obtain ⟨hp, he⟩ := mem_filter.mp hp
    obtain ⟨hr, hs⟩ := mem_product.mp hp
    exact Nat.mem_divisorsAntidiagonal.mpr
      ⟨he, he ▸ (Nat.mul_pos (mem_Ioc.mp hr).1 (mem_Ioc.mp hs).1).ne'⟩
  have he :
      (∑ p ∈ B, γ p.1 * ζ p.2) =
        ∑ p ∈ q.divisorsAntidiagonal, γ p.1 * ζ p.2 := by
    apply sum_subset hB
    intro p hp hnot
    by_cases hg : γ p.1 = 0
    · simp [hg]
    by_cases hz : ζ p.2 = 0
    · simp [hz]
    obtain ⟨hr0, hrR⟩ := hγ _ hg
    obtain ⟨hs0, hsS⟩ := hζ _ hz
    exact (hnot (mem_filter.mpr
      ⟨mem_product.mpr ⟨mem_Ioc.mpr ⟨hr0, Nat.le_floor hrR⟩,
        mem_Ioc.mpr ⟨hs0, Nat.le_floor hsS⟩⟩,
        (Nat.mem_divisorsAntidiagonal.mp hp).1⟩)).elim
  rw [factorConvolution, ← he]
  simp only [B, sum_filter, sum_product]

/-- Reindex before taking absolute values: factors are the outer variables,
and the remaining finite set is the exact product fiber. -/
theorem sum_factorConvolution_eq_box_fibers {ι : Type*}
    {R S : ℝ} {γ ζ : ℕ → ℝ}
    (hγ : factorSupported R γ) (hζ : factorSupported S ζ)
    (T : Finset ι) (q : ι → ℕ) (F : ι → ℝ) :
    (∑ t ∈ T, factorConvolution γ ζ (q t) * F t) =
      ∑ r ∈ Ioc 0 ⌊R⌋₊, ∑ s ∈ Ioc 0 ⌊S⌋₊,
        ∑ t ∈ T.filter (fun t => q t = r * s), γ r * ζ s * F t := by
  simp only [factorConvolution_eq_sum_box hγ hζ, sum_mul, sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro r _
  rw [sum_comm]
  apply sum_congr rfl
  intro s _
  apply sum_congr rfl
  intro t _
  by_cases h : q t = r * s
  · simp [h]
  · simp [h, Ne.symm h]

/-- The same rectangular reindexing with low omega on the second factor,
not on the product modulus and not on the first factor. -/
theorem sum_factorConvolution_lowOmega_eq_box_fibers {ι : Type*}
    {R S : ℝ} {γ ζ : ℕ → ℝ}
    (hγ : factorSupported R γ) (hζ : factorSupported S ζ)
    (ξ : ℝ) (T : Finset ι) (q : ι → ℕ) (F : ι → ℝ) :
    (∑ t ∈ T, factorConvolution γ (betaLowOmega ζ ξ) (q t) * F t) =
      ∑ r ∈ Ioc 0 ⌊R⌋₊,
        ∑ s ∈ (Ioc 0 ⌊S⌋₊).filter (fun s => (s.primeFactors.card : ℝ) ≤ ξ),
          ∑ t ∈ T.filter (fun t => q t = r * s), γ r * ζ s * F t := by
  rw [sum_factorConvolution_eq_box_fibers hγ (factorLowOmega_supported hζ ξ)]
  apply sum_congr rfl
  intro r _
  rw [sum_filter]
  apply sum_congr rfl
  intro s _
  by_cases h : (s.primeFactors.card : ℝ) ≤ ξ
  · simp [betaLowOmega, h]
  · simp [betaLowOmega, h]

/-- The surviving variables are `(q₁,n₁,n₂)`; the second modulus is `r*s`.
All original reduced-modulus, beta-support, compatibility, and mask tests
are retained. This finite set is not asserted to be an interval. -/
def wDelayedTuples (N Q : Finset ℕ) (a : ℤ) (P : WOriginalTuple → Prop)
    (r s : ℕ) : Finset (ℕ × (ℕ × ℕ)) :=
  (reducedModuli Q a ×ˢ (N ×ˢ N)).filter (fun u =>
    r * s ∈ reducedModuli Q a ∧
      WCompatible u.1 (r * s) u.2.1 u.2.2 ∧ P ((u.1, r * s), u.2))

theorem mem_wDelayedTuples_iff {N Q : Finset ℕ} {a : ℤ}
    {P : WOriginalTuple → Prop} {r s : ℕ} {u : ℕ × (ℕ × ℕ)} :
    u ∈ wDelayedTuples N Q a P r s ↔
      ((u.1, r * s), u.2) ∈ wMaskedTuples N Q a P := by
  simp only [wDelayedTuples, wMaskedTuples, wOriginalTuples,
    mem_filter, mem_product]
  tauto

theorem wDelayedTuples_spec {N Q : Finset ℕ} {a : ℤ}
    {P : WOriginalTuple → Prop} {r s : ℕ} {u : ℕ × (ℕ × ℕ)}
    (hu : u ∈ wDelayedTuples N Q a P r s) :
    u.1 ∈ reducedModuli Q a ∧ r * s ∈ reducedModuli Q a ∧
      u.2.1 ∈ N ∧ u.2.2 ∈ N ∧
      WCompatible u.1 (r * s) u.2.1 u.2.2 ∧ P ((u.1, r * s), u.2) := by
  obtain ⟨⟨hq₁, hn₁, hn₂⟩, hq₂, hcompat, hP⟩ :=
    (show (u.1 ∈ reducedModuli Q a ∧ u.2.1 ∈ N ∧ u.2.2 ∈ N) ∧
        r * s ∈ reducedModuli Q a ∧
        WCompatible u.1 (r * s) u.2.1 u.2.2 ∧ P ((u.1, r * s), u.2) from
      by simpa only [wDelayedTuples, mem_filter, mem_product] using hu)
  exact ⟨hq₁, hq₂, hn₁, hn₂, hcompat, hP⟩

/-- Eliminate the second modulus from its exact product fiber. -/
theorem sum_wMaskedTuples_productFiber {A : Type*} [AddCommMonoid A]
    (N Q : Finset ℕ) (a : ℤ) (P : WOriginalTuple → Prop)
    (r s : ℕ) (F : WOriginalTuple → A) :
    (∑ t ∈ (wMaskedTuples N Q a P).filter (fun t => t.1.2 = r * s), F t) =
      ∑ u ∈ wDelayedTuples N Q a P r s, F ((u.1, r * s), u.2) := by
  have hrec (t : WOriginalTuple)
      (ht : t ∈ (wMaskedTuples N Q a P).filter (fun t => t.1.2 = r * s)) :
      ((t.1.1, r * s), t.2) = t :=
    Prod.ext (Prod.ext rfl (mem_filter.mp ht).2.symm) rfl
  refine sum_bij (fun t _ => (t.1.1, t.2)) ?_ ?_ ?_ ?_
  · intro t ht
    apply mem_wDelayedTuples_iff.mpr
    rw [hrec t ht]
    exact (mem_filter.mp ht).1
  · intro t ht v hv he
    have he' := congrArg (fun u : ℕ × (ℕ × ℕ) => ((u.1, r * s), u.2)) he
    simpa only [hrec t ht, hrec v hv] using he'
  · intro u hu
    exact ⟨((u.1, r * s), u.2),
      mem_filter.mpr ⟨mem_wDelayedTuples_iff.mp hu, rfl⟩, rfl⟩
  · intro t ht
    rw [hrec t ht]

/-- The first modulus coefficient and the original frequency cutoff remain
inside the kernel; only the second modulus coefficient is removed. -/
def wSecondModulusKernel (M : ℝ) (H : ℕ → ℕ → ℕ)
    (β c₁ : ℕ → ℝ) (a : ℤ) (t : WOriginalTuple) : ℝ :=
  (c₁ t.1.1 * β t.2.1 * β t.2.2) *
    (∑ h ∈ Icc (-(H t.1.1 t.1.2 : ℤ)) (H t.1.1 t.1.2),
      wPoissonFrequency M a t.1.1 t.1.2 t.2.1 t.2.2 h).re

/-- The actual factored retained-frequency sum. The outer factor supports
are closed and positive, low omega is imposed only on `s`, and `q₂` has
been eliminated. The first coefficient is the arbitrary signed `c₁`. -/
def wMaskedFactoredTruncated (M : ℝ) (H : ℕ → ℕ → ℕ)
    (N Q : Finset ℕ) (β c₁ γ ζ : ℕ → ℝ) (a : ℤ)
    (P : WOriginalTuple → Prop) (R S ξ : ℝ) : ℝ :=
  ∑ r ∈ Ioc 0 ⌊R⌋₊,
    ∑ s ∈ (Ioc 0 ⌊S⌋₊).filter (fun s => (s.primeFactors.card : ℝ) ≤ ξ),
      ∑ u ∈ wDelayedTuples N Q a P r s,
        γ r * ζ s * wSecondModulusKernel M H β c₁ a ((u.1, r * s), u.2)

/-- A general signed first coefficient is untouched by delayed expansion. -/
theorem sum_secondModulusConvolution_eq_factored
    {R S : ℝ} {γ ζ : ℕ → ℝ}
    (hγ : factorSupported R γ) (hζ : factorSupported S ζ)
    (M : ℝ) (H : ℕ → ℕ → ℕ) (N Q : Finset ℕ)
    (β c₁ : ℕ → ℝ) (a : ℤ) (P : WOriginalTuple → Prop) (ξ : ℝ) :
    (∑ t ∈ wMaskedTuples N Q a P,
      factorConvolution γ (betaLowOmega ζ ξ) t.1.2 *
        wSecondModulusKernel M H β c₁ a t) =
      wMaskedFactoredTruncated M H N Q β c₁ γ ζ a P R S ξ := by
  rw [sum_factorConvolution_lowOmega_eq_box_fibers hγ hζ]
  unfold wMaskedFactoredTruncated
  apply sum_congr rfl
  intro r _
  apply sum_congr rfl
  intro s _
  exact sum_wMaskedTuples_productFiber N Q a P r s
    (fun t => γ r * ζ s * wSecondModulusKernel M H β c₁ a t)

/-- Exact delayed expansion of the actual `wMaskedTruncated`, decomposing
only its second coefficient. No sign, positivity-of-scale, or support
conditions beyond the two factor supports are needed for this identity. -/
theorem wMaskedTruncated_factorConvolution
    {R S : ℝ} {γ ζ : ℕ → ℝ}
    (hγ : factorSupported R γ) (hζ : factorSupported S ζ)
    (M : ℝ) (H : ℕ → ℕ → ℕ) (N Q : Finset ℕ)
    (β : ℕ → ℝ) (a : ℤ) (P : WOriginalTuple → Prop) (ξ : ℝ) :
    wMaskedTruncated M H N Q β (factorConvolution γ (betaLowOmega ζ ξ)) a P =
      wMaskedFactoredTruncated M H N Q β
        (factorConvolution γ (betaLowOmega ζ ξ)) γ ζ a P R S ξ := by
  unfold wMaskedTruncated
  calc
    _ = ∑ t ∈ wMaskedTuples N Q a P,
        factorConvolution γ (betaLowOmega ζ ξ) t.1.2 *
          wSecondModulusKernel M H β
            (factorConvolution γ (betaLowOmega ζ ξ)) a t := by
      apply sum_congr rfl
      intro t _
      simp only [wOriginalTerm, wSecondModulusKernel]
      ring
    _ = _ := sum_secondModulusConvolution_eq_factored hγ hζ M H N Q β
      (factorConvolution γ (betaLowOmega ζ ξ)) a P ξ

theorem wMaskedTruncated_eq_factored_of_eq
    {R S ξ : ℝ} {γ ζ c : ℕ → ℝ}
    (hγ : factorSupported R γ) (hζ : factorSupported S ζ)
    (hc : c = factorConvolution γ (betaLowOmega ζ ξ))
    (M : ℝ) (H : ℕ → ℕ → ℕ) (N Q : Finset ℕ)
    (β : ℕ → ℝ) (a : ℤ) (P : WOriginalTuple → Prop) :
    wMaskedTruncated M H N Q β c a P =
      wMaskedFactoredTruncated M H N Q β c γ ζ a P R S ξ := by
  subst c
  exact wMaskedTruncated_factorConvolution hγ hζ M H N Q β a P ξ

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
