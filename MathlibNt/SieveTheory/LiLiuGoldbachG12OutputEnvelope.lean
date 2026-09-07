import MathlibNt.SieveTheory.LiLiuGoldbachG12PaidRosser

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
open Finset
open MathlibNt.SieveTheory.SwitchingPrinciple
open scoped BigOperators
noncomputable section

/-- Paid upper sieve for the literal original G12 output-prime fibres.
All constants and thresholds precede epsilon, the sieve cutoff and its level.
The Euler product is the actual inherited Goldbach product, not an asymptotic surrogate. -/
theorem goldbachG12OutputTotal_le_paidRosser_actualEuler
    (A ρ : ℝ) (hA : 0 < A) (hρ : 0 < ρ) :
    ∃ B C z₀ : ℝ, 0 < B ∧ 0 < C ∧ ∃ N₀ : ℕ, 4 ≤ N₀ ∧
      ∀ N ≥ N₀, ∀ (_hEven : Even N) (ε Z Δ s : ℝ),
      z₀ ≤ Z → 2 ≤ Z → 0 < Δ → s = Real.log Δ/Real.log Z →
      3/2 ≤ s → s ≤ 4 → Δ ≤ Real.sqrt N / Real.log (N : ℝ)^B →
      (400 * ∑ m ∈ goldbachG12ActiveProductSupport N,
        goldbachG12NormalizedCoefficient N m *
          ((goldbachG11ProductFirstPrimeFiber N ε ((N : ℝ)^(4/53 : ℝ)) m).card : ℝ)) ≤
        400*goldbachG12PrimeWindowMainMass N ε*
          (jurkatRichertUpperLinearSieveFactor s+ρ)*goldbachB10PrimeProduct N Z +
          400*C*N/Real.log (N : ℝ)^A + 8000*(Nat.ceil Z : ℝ) := by
  obtain ⟨B,C,z₀,hB,hC,N₀,hN₀,h⟩ := goldbachG12OutputTotal_le_paidRosser A ρ hA hρ
  refine ⟨B,C,z₀,hB,hC,N₀,hN₀,?_⟩
  intro N hN hEven ε Z Δ s hz hZ hΔ hs hslo hshi hlevel
  simpa only [goldbachG12Linked_sieveProduct_eq] using
    h N hN hEven ε Z Δ s hz hZ hΔ hs hslo hshi hlevel

/-- Equivalent endpoint in the original integer product count; no G11 large-domain
count is substituted for the G12 mother. -/
theorem goldbachG12ProductPrimeTotal_le_paidRosser_actualEuler
    (A ρ : ℝ) (hA : 0 < A) (hρ : 0 < ρ) :
    ∃ B C z₀ : ℝ, 0 < B ∧ 0 < C ∧ ∃ N₀ : ℕ, 4 ≤ N₀ ∧
      ∀ N ≥ N₀, ∀ (_hEven : Even N) (ε Z Δ s : ℝ),
      z₀ ≤ Z → 2 ≤ Z → 0 < Δ → s = Real.log Δ/Real.log Z →
      3/2 ≤ s → s ≤ 4 → Δ ≤ Real.sqrt N / Real.log (N : ℝ)^B →
      (goldbachG12ProductPrimeTotal N ε ((N : ℝ)^(4/53 : ℝ))
        ((N : ℝ)^(4/33 : ℝ)) ((N : ℝ)^(3/11 : ℝ)) : ℝ) ≤
        400*goldbachG12PrimeWindowMainMass N ε*
          (jurkatRichertUpperLinearSieveFactor s+ρ)*goldbachB10PrimeProduct N Z +
          400*C*N/Real.log (N : ℝ)^A + 8000*(Nat.ceil Z : ℝ) := by
  obtain ⟨B,C,z₀,hB,hC,N₀,hN₀,h⟩ :=
    goldbachG12OutputTotal_le_paidRosser_actualEuler A ρ hA hρ
  refine ⟨B,C,z₀,hB,hC,N₀,hN₀,?_⟩
  intro N hN hEven ε Z Δ s hz hZ hΔ hs hslo hshi hlevel
  rw [goldbachG12ProductPrimeTotal_eq_active N ε (by omega)]
  exact h N hN hEven ε Z Δ s hz hZ hΔ hs hslo hshi hlevel

end
end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
