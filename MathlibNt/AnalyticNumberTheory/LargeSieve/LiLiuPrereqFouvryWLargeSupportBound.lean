import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryLargeSupportDensity
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryWPairMaskBound

/-!
# Original and zero-mode bounds for a large supported beta factor

The canonical `d₁` condition gives a sparse square-divisor strip in the first
beta coordinate. Cauchy--Schwarz then saves a fourth root of the cutoff.
The original and zero-mode estimates apply to the identical arbitrary mask;
no symmetry or preservation of well-factorability under masking is assumed.
-/

noncomputable section

open Classical Finset

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

/-- The signed coefficient mass on the large-`d₁` pair set has an explicit
fourth-root saving, using only the global divisor second moment. -/
theorem sum_abs_largeSupportPairs_le {k : ℕ} (hk : 1 ≤ k) {T Y : ℝ}
    (hT : 1 ≤ T) (hY : 0 < Y)
    (N : Finset ℕ) (hN : N ⊆ Ioc 0 ⌊T⌋₊) (β : ℕ → ℝ)
    (hβ : ∀ n ∈ N, |β n| ≤ (fouvryTau k n : ℝ)) :
    (∑ p ∈ largeSupportPairs N Y, |β p.1 * β p.2|) ≤
      T ^ 2 * (1 + Real.log T) ^ (k ^ 2 - 1) *
        Real.sqrt (2 / Real.sqrt Y) := by
  have hT0 : 0 ≤ T := by linarith
  have hcard :
      Real.sqrt ((largeSupportPairs N Y).card : ℝ) ≤
        T * Real.sqrt (2 / Real.sqrt Y) := by
    calc
      _ ≤ Real.sqrt (2 * T ^ 2 / Real.sqrt Y) :=
        Real.sqrt_le_sqrt (card_largeSupportPairs_le hT0 hY N hN)
      _ = Real.sqrt (T ^ 2 * (2 / Real.sqrt Y)) := by congr 1; ring
      _ = _ := by rw [Real.sqrt_mul (sq_nonneg T), Real.sqrt_sq hT0]
  calc
    _ ≤ Real.sqrt ((largeSupportPairs N Y).card : ℝ) * ∑ n ∈ N, β n ^ 2 :=
      sum_abs_pair_mul_le_sqrt_card N (largeSupportPairs N Y) (filter_subset _ _) β
    _ ≤ (T * Real.sqrt (2 / Real.sqrt Y)) *
        (T * (1 + Real.log T) ^ (k ^ 2 - 1)) :=
      mul_le_mul hcard (sum_alpha_sq_le_fouvryTau hk hT N hN β hβ)
        (sum_nonneg (fun _ _ => sq_nonneg _)) (by positivity)
    _ = _ := by ring

/-- A large canonical supported factor is exactly the pair condition needed
by the sparse envelope, regardless of the modulus coordinates. -/
theorem mem_largeSupportPairs_of_wOriginalTuple {N Q : Finset ℕ} {a : ℤ}
    {t : WOriginalTuple} (ht : t ∈ wOriginalTuples N Q a) {Y : ℝ}
    (hlarge : Y < ((wGCDData t.1.1 t.1.2 t.2.1 t.2.2).d₁ : ℝ)) :
    t.2 ∈ largeSupportPairs N Y :=
  mem_filter.mpr ⟨(mem_product.mp (mem_filter.mp ht).1).2, hlarge⟩

/-- Uniform large-`d₁` exclusion for the actual original progression sum.
The nondivisibility condition is supplied later by `betaClean`. -/
theorem wMaskedOriginal_abs_le_largeSupport
    {k : ℕ} (hk : 1 ≤ k) (j : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ M T Y x : ℝ,
      1 ≤ M → 1 ≤ T → 0 < Y → 1 ≤ x → M * T ≤ x →
      ∀ N Q : Finset ℕ, N ⊆ Ioc 0 ⌊T⌋₊ →
      ∀ β c : ℕ → ℝ, (∀ n ∈ N, |β n| ≤ (fouvryTau k n : ℝ)) →
        (∀ q ∈ Q, |c q| ≤ (fouvryTau j q : ℝ)) →
      ∀ a : ℤ, |(a : ℝ)| ≤ x → (∀ n ∈ N, β n ≠ 0 → ¬(n : ℤ) ∣ a) →
      ∀ P : WOriginalTuple → Prop,
        (∀ t ∈ wOriginalTuples N Q a, P t →
          Y < ((wGCDData t.1.1 t.1.2 t.2.1 t.2.2).d₁ : ℝ)) →
      |wMaskedOriginal M N Q β c a P| ≤ C * M * x ^ ε *
        (T ^ 2 * (1 + Real.log T) ^ (k ^ 2 - 1) *
          Real.sqrt (2 / Real.sqrt Y)) := by
  obtain ⟨C, hC, hb⟩ := wMaskedOriginal_abs_le_pair_mass j hε
  refine ⟨C, hC, ?_⟩
  intro M T Y x hM hT hY hx hMT N Q hN β c hβ hc a ha hs P hP
  exact (hb M T x hM hT hx hMT N Q hN β c hc a ha hs
    (largeSupportPairs N Y) (filter_subset _ _) P
    (fun t ht hp => mem_largeSupportPairs_of_wOriginalTuple ht (hP t ht hp))).trans
      (mul_le_mul_of_nonneg_left (sum_abs_largeSupportPairs_le hk hT hY N hN β hβ)
        (by positivity))

/-- Absolute control of the same masked zero mode, without restricting the
unmasked SW cancellation or assuming that the mask is symmetric. -/
theorem wMaskedZeroMode_abs_le_largeSupport
    {k : ℕ} (hk : 1 ≤ k) (j : ℕ) {T L Y : ℝ}
    (hT : 1 ≤ T) (hL : 1 ≤ L) (hY : 0 < Y)
    (M : ℝ) (N Q : Finset ℕ)
    (hN : N ⊆ Ioc 0 ⌊T⌋₊) (hQ : Q ⊆ Ioc 0 ⌊L⌋₊)
    (β c : ℕ → ℝ) (hβ : ∀ n ∈ N, |β n| ≤ (fouvryTau k n : ℝ))
    (hc : ∀ q ∈ Q, |c q| ≤ (fouvryTau j q : ℝ)) (a : ℤ)
    (P : WOriginalTuple → Prop)
    (hP : ∀ t ∈ wOriginalTuples N Q a, P t →
      Y < ((wGCDData t.1.1 t.1.2 t.2.1 t.2.2).d₁ : ℝ)) :
    |wMaskedZeroMode M N Q β c a P| ≤
      |M * dyadicCutoffMass| *
        (T ^ 2 * (1 + Real.log T) ^ (k ^ 2 - 1) *
          Real.sqrt (2 / Real.sqrt Y)) *
        (1 + Real.log L) ^ (2 * j ^ 2 + 1) := by
  apply (wMaskedZeroMode_abs_le_pair_mass j hL M N Q hQ β c hc a P
    (largeSupportPairs N Y)
    (fun t ht hp => mem_largeSupportPairs_of_wOriginalTuple ht (hP t ht hp))).trans
  apply mul_le_mul_of_nonneg_right _ (by have := Real.log_nonneg hL; positivity)
  exact mul_le_mul_of_nonneg_left (sum_abs_largeSupportPairs_le hk hT hY N hN β hβ)
    (abs_nonneg _)

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
