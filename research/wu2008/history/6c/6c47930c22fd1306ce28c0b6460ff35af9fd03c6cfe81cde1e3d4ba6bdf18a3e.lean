import MathlibNt.Wu2004MeanValue.SelectedHighAggregate

/-!
# Actual finite prefix maxima of the high-conductor source amplitudes

The maximum is outside the complete coefficient sum. Its attainment is used
to select a prefix for each primitive character, then the unconditional
selected-prefix producer bounds all those choices simultaneously.
-/

noncomputable section
open Classical Complex Finset
open AnalyticNumberTheory.LargeSieve
open AnalyticNumberTheory.LargeSieve.ChenLiuCoprimeProducer
open scoped BigOperators

namespace Wu2004MeanValue

def sourcePrefixMax {q : ℕ} (f : ℕ → ℂ) (m x A₁ A₂ : ℕ)
    (χ : PrimitiveCharacter q) : ℝ :=
  (range (x + 1)).sup' ⟨0, mem_range.mpr (Nat.zero_lt_succ x)⟩
    (fun y => ‖panSourceCharacterAmplitude (panSourceG f m) (panSourceD m) y A₁ A₂ χ‖)

def maximalHighSource (f : ℕ → ℂ) (m x A₁ A₂ : ℕ) (B : ℝ) : ℝ :=
  ∑ q ∈ Ioc ⌊lowConductor x B⌋₊ ⌊upperConductor x B⌋₊,
    (q.totient : ℝ)⁻¹ * ∑ χ : PrimitiveCharacter q, sourcePrefixMax f m x A₁ A₂ χ

/-- Genuine finite prefix maxima, with the same logarithmic saving and
explicit remainder as the selected-prefix producer. The maximizing endpoint
may depend on the conductor and primitive character, but not on an individual
coefficient inside the amplitude. -/
theorem chosen_high_source_prefix_max_log_saving :
    ∃ C : ℝ, 0 < C ∧ ∀ B ε : ℝ, 0 ≤ B → 0 < ε →
      ∃ X₀ : ℕ, ∀ x : ℕ, X₀ ≤ x →
      ∀ (m A₁ A₂ : ℕ) (f : ℕ → ℂ),
      A₂ ≤ x → (A₂ : ℝ) ≤ (x : ℝ) ^ (1 - ε) →
      Real.log x ^ (2 * B) ≤ A₁ → (∀ n, ‖f n‖ ≤ 1) →
      maximalHighSource f m x A₁ A₂ B ≤
        C * (x : ℝ) * Real.log x ^ (6 - B) +
          6984 * (Real.log x) ^ 2 / (x : ℝ) := by
  obtain ⟨C, hC, hselected⟩ := chosen_high_source_selected_prefix_log_saving
  refine ⟨C, hC, ?_⟩
  intro B ε hB hε
  obtain ⟨X₀, hX⟩ := hselected B ε hB hε
  refine ⟨X₀, ?_⟩
  intro x hx m A₁ A₂ f hAx hApower hAlow hf
  have hchoose (q : ℕ) (χ : PrimitiveCharacter q) :
      ∃ y : ℕ, y ≤ x ∧ sourcePrefixMax f m x A₁ A₂ χ =
        ‖panSourceCharacterAmplitude (panSourceG f m) (panSourceD m) y A₁ A₂ χ‖ := by
    obtain ⟨y, hy, heq⟩ := exists_mem_eq_sup'
      (show (range (x + 1)).Nonempty from ⟨0, mem_range.mpr (Nat.zero_lt_succ x)⟩)
      (fun y => ‖panSourceCharacterAmplitude (panSourceG f m) (panSourceD m) y A₁ A₂ χ‖)
    exact ⟨y, Nat.le_of_lt_succ (mem_range.mp hy), heq⟩
  choose y hy heq using hchoose
  have hmain := hX x hx m A₁ A₂ f y hy hAx hApower hAlow hf
  unfold maximalHighSource
  simp_rw [heq]
  exact hmain

end Wu2004MeanValue
