import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryMaskedW
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryLargeGCDBetaMass
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryHighDeltaWeights

/-!
# The zero mode of the large beta-gcd exclusion

The bound applies to every further submask of `gcd(n₁,n₂)>Y`.
It is an absolute zero-mode bound, not a restriction of the signed
unmasked Siegel--Walfisz cancellation. The original progression sum
and the other four gcd exclusions still require separate estimates.
-/

noncomputable section

open Classical Finset

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

theorem wMaskedZeroMode_eq_modulus_sum
    (M : ℝ) (N Q : Finset ℕ) (β c : ℕ → ℝ) (a : ℤ) (P : WOriginalTuple → Prop) :
    wMaskedZeroMode M N Q β c a P =
      (M * dyadicCutoffMass) *
        ∑ q ∈ reducedModuli Q a, ∑ r ∈ reducedModuli Q a,
          (c q * c r / (q.lcm r : ℝ)) *
            ∑ p ∈ N ×ˢ N,
              if WCompatible q r p.1 p.2 ∧ P ((q, r), p)
                then β p.1 * β p.2 else 0 := by
  unfold wMaskedZeroMode wMaskedTuples wOriginalTuples
  simp only [sum_filter, sum_product, mul_sum]
  apply sum_congr rfl
  intro q _
  apply sum_congr rfl
  intro r _
  apply sum_congr rfl
  intro n₁ _
  apply sum_congr rfl
  intro n₂ _
  simp only [wTupleCoefficient]
  split_ifs <;> simp_all
  ring

/-- Discarding compatibility or imposing further masks only enlarges the
absolute beta-pair majorant, so the large-gcd gain survives every submask. -/
theorem masked_beta_pair_abs_le_largeGCD
    (N Q : Finset ℕ) (β : ℕ → ℝ) (a : ℤ) (P : WOriginalTuple → Prop) (Y : ℝ)
    (hP : ∀ t ∈ wOriginalTuples N Q a, P t → Y < (t.2.1.gcd t.2.2 : ℝ))
    {q r : ℕ} (hq : q ∈ reducedModuli Q a) (hr : r ∈ reducedModuli Q a) :
    |∑ p ∈ N ×ˢ N, if WCompatible q r p.1 p.2 ∧ P ((q, r), p)
      then β p.1 * β p.2 else 0| ≤
      ∑ p ∈ largeGCDPairs N Y, |β p.1 * β p.2| := by
  rw [← sum_filter]
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum_of_subset_of_nonneg
  · intro p hp
    obtain ⟨hp, hc, hm⟩ := mem_filter.mp hp
    exact mem_filter.mpr ⟨hp, hP ((q, r), p)
      (mem_filter.mpr ⟨mem_product.mpr ⟨mem_product.mpr ⟨hq, hr⟩, hp⟩, hc⟩) hm⟩
  · intro p _ _
    exact abs_nonneg _

/-- Uniform inverse-square-root saving for the actual zero mode under
any submask of a large beta gcd. Both coefficient signs are retained. -/
theorem wMaskedZeroMode_abs_le_largeGCD
    {k : ℕ} (hk : 1 ≤ k) (j : ℕ) {T L Y : ℝ}
    (hT : 1 ≤ T) (hL : 1 ≤ L) (hY : 0 < Y)
    (M : ℝ) (N Q : Finset ℕ)
    (hN : N ⊆ Ioc 0 ⌊T⌋₊) (hQ : Q ⊆ Ioc 0 ⌊L⌋₊)
    (β c : ℕ → ℝ) (hβ : ∀ n ∈ N, |β n| ≤ (fouvryTau k n : ℝ))
    (hc : ∀ q ∈ Q, |c q| ≤ (fouvryTau j q : ℝ)) (a : ℤ)
    (P : WOriginalTuple → Prop)
    (hP : ∀ t ∈ wOriginalTuples N Q a, P t → Y < (t.2.1.gcd t.2.2 : ℝ)) :
    |wMaskedZeroMode M N Q β c a P| ≤
      |M * dyadicCutoffMass| *
        (T ^ 2 * (1 + Real.log T) ^ (k ^ 2 - 1) *
          Real.sqrt ((1 + Real.log T) / Y)) *
        (1 + Real.log L) ^ (2 * j ^ 2 + 1) := by
  let B := T ^ 2 * (1 + Real.log T) ^ (k ^ 2 - 1) *
    Real.sqrt ((1 + Real.log T) / Y)
  have hB : 0 ≤ B := by
    have := Real.log_nonneg hT
    dsimp [B]
    positivity
  rw [wMaskedZeroMode_eq_modulus_sum, abs_mul]
  calc
    _ ≤ |M * dyadicCutoffMass| *
        ∑ q ∈ reducedModuli Q a, ∑ r ∈ reducedModuli Q a,
          |c q * c r / (q.lcm r : ℝ)| * B := by
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      apply (abs_sum_le_sum_abs _ _).trans
      apply sum_le_sum
      intro q hq
      apply (abs_sum_le_sum_abs _ _).trans
      apply sum_le_sum
      intro r hr
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left
        ((masked_beta_pair_abs_le_largeGCD N Q β a P Y hP hq hr).trans
          (sum_abs_largeGCDPairs_le hk hT hY N hN β hβ)) (abs_nonneg _)
    _ = |M * dyadicCutoffMass| *
        ((∑ q ∈ reducedModuli Q a, ∑ r ∈ reducedModuli Q a,
          |c q * c r / (q.lcm r : ℝ)|) * B) := by simp only [sum_mul]
    _ ≤ |M * dyadicCutoffMass| * ((1 + Real.log L) ^ (2 * j ^ 2 + 1) * B) := by
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      apply mul_le_mul_of_nonneg_right _ hB
      exact sum_abs_lcm_weight_le_log j hL (reducedModuli Q a)
        ((filter_subset _ _).trans hQ) c (fun q hq ↦ hc q (mem_filter.mp hq).1)
    _ = _ := by dsimp [B]; ring

/-- Direct specialization to the first exclusion `d=gcd(N₁,N₂)>Y`. -/
theorem wLargeBetaGCDZeroMode_abs_le
    {k : ℕ} (hk : 1 ≤ k) (j : ℕ) {T L Y : ℝ}
    (hT : 1 ≤ T) (hL : 1 ≤ L) (hY : 0 < Y)
    (M : ℝ) (N Q : Finset ℕ)
    (hN : N ⊆ Ioc 0 ⌊T⌋₊) (hQ : Q ⊆ Ioc 0 ⌊L⌋₊)
    (β c : ℕ → ℝ) (hβ : ∀ n ∈ N, |β n| ≤ (fouvryTau k n : ℝ))
    (hc : ∀ q ∈ Q, |c q| ≤ (fouvryTau j q : ℝ)) (a : ℤ) :
    |wMaskedZeroMode M N Q β c a (fun t ↦ Y < (t.2.1.gcd t.2.2 : ℝ))| ≤
      |M * dyadicCutoffMass| *
        (T ^ 2 * (1 + Real.log T) ^ (k ^ 2 - 1) *
          Real.sqrt ((1 + Real.log T) / Y)) *
        (1 + Real.log L) ^ (2 * j ^ 2 + 1) :=
  wMaskedZeroMode_abs_le_largeGCD hk j hT hL hY M N Q hN hQ β c hβ hc a
    _ (fun _ _ h ↦ h)

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
