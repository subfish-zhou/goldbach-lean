import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryWLargeSupportBound

/-!
# Fixed-residue-scale large-supported-factor bound

Only the auxiliary divisor-growth scale is enlarged to `Cscale * x`.
The progression sum, beta endpoint, arbitrary mask and supported-factor
threshold `Y` are unchanged. The fixed enlargement is paid in the constant.
-/

noncomputable section
open Classical Finset
namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

/-- The large-support original-sum estimate for a fixed larger residue range.
The constant is chosen before all varying scales, coefficients and masks. -/
theorem wMaskedOriginal_abs_le_largeSupport_kscale
    {k : ℕ} (hk : 1 ≤ k) (j : ℕ) {ε Cscale : ℝ}
    (hε : 0 < ε) (hCscale : 1 ≤ Cscale) :
    ∃ C : ℝ, 0 < C ∧ ∀ M T Y x : ℝ,
      1 ≤ M → 1 ≤ T → 0 < Y → 1 ≤ x → M * T ≤ x →
      ∀ N Q : Finset ℕ, N ⊆ Ioc 0 ⌊T⌋₊ →
      ∀ β c : ℕ → ℝ, (∀ n ∈ N, |β n| ≤ (fouvryTau k n : ℝ)) →
        (∀ q ∈ Q, |c q| ≤ (fouvryTau j q : ℝ)) →
      ∀ a : ℤ, |(a : ℝ)| ≤ Cscale * x →
        (∀ n ∈ N, β n ≠ 0 → ¬(n : ℤ) ∣ a) →
      ∀ P : WOriginalTuple → Prop,
        (∀ t ∈ wOriginalTuples N Q a, P t →
          Y < ((wGCDData t.1.1 t.1.2 t.2.1 t.2.2).d₁ : ℝ)) →
      |wMaskedOriginal M N Q β c a P| ≤ C * M * x ^ ε *
        (T ^ 2 * (1 + Real.log T) ^ (k ^ 2 - 1) *
          Real.sqrt (2 / Real.sqrt Y)) := by
  obtain ⟨D, hD, hb⟩ := wMaskedOriginal_abs_le_largeSupport hk j hε
  refine ⟨D * Cscale ^ ε, by positivity, ?_⟩
  intro M T Y x hM hT hY hx hMT N Q hN β c hβ hc a ha hs P hP
  have hxx : x ≤ Cscale * x := le_mul_of_one_le_left (by linarith) hCscale
  have hbound := hb M T Y (Cscale * x) hM hT hY (hx.trans hxx)
    (hMT.trans hxx) N Q hN β c hβ hc a ha hs P hP
  rw [Real.mul_rpow (by linarith : 0 ≤ Cscale) (by linarith : 0 ≤ x)] at hbound
  convert hbound using 1
  ring

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

#print axioms MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry.wMaskedOriginal_abs_le_largeSupport_kscale
