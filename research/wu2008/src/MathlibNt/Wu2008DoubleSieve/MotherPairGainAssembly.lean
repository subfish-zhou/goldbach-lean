import MathlibNt.Wu2008DoubleSieve.MotherPairGainMass
import MathlibNt.Wu2008DoubleSieve.Gamma5GainAssembly
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalMotherPairClassicalSource

namespace Wu2008DoubleSieve.MotherPair
open Finset Set Real Filter
open scoped Classical Topology

theorem packing_sample_bounds {p : SecondFunctionalParameters} {j : Term}
    (r : GainRectangle p j) {δ : ℝ} (hδ : 0<δ) (hδhi : δ<1/2) :
    0 ≤ wuImprovementLimit true δ r.sample ∧ wuImprovementLimit true δ r.sample ≤ 1 := by
  simpa only [gamma5GainH, gamma5Gain_clip_eq ⟨r.sample_lower.le,r.sample_upper.le⟩]
    using gamma5Gain_H_bounds hδ hδhi r.sample

theorem term_count_partition {α : Type*} [Fintype α] {i : ℕ}
    (p : SecondFunctionalParameters) (j : Term) (N : ℕ) (δ : ℝ) (W : Fin i → Finset ℕ)
    (L : Finset Gamma5ClassicalLabel) (P : α → Finset Gamma5ClassicalLabel)
    (hd : Pairwise (fun a b => Disjoint (P a) (P b))) (hs : ∀ a, P a ⊆ L) :
    termCount p j N δ W L = termCount p j N δ W (L \ univ.biUnion P) +
      ∑ a, termCount p j N δ W (P a) := by
  cases j <;> exact gamma5Gain_partition_sum L P hd hs _

/-- Exact finite recombination retains every uncovered prime atom in the complement. -/
theorem packing_finite_upper {p : SecondFunctionalParameters} (h : AnalyticParameters p)
    (j : Term) {α : Type*} [Fintype α] {i k N : ℕ} {δ Δ ρ : ℝ} {V : Fin i → ℝ}
    (hN : 2 ≤ N) (hδ : 0<δ) (hδhi : δ<1/2) (hb : wuSourceBox k δ N i Δ V)
    (hρ : 0 ≤ ρ) (P : α → Finset Gamma5ClassicalLabel) (H : α → ℝ)
    (hd : Pairwise (fun a b => Disjoint (P a) (P b)))
    (hs : ∀ a, P a ⊆ termLabels p j N δ (convolutionWuWindows N Δ V))
    (hclass : termCount p j N δ (convolutionWuWindows N Δ V)
        (termLabels p j N δ (convolutionWuWindows N Δ V) \ univ.biUnion P) ≤
      (1+ρ)^2*gamma5ClassicalMainMass N δ (convolutionWuWindows N Δ V)
        (termLabels p j N δ (convolutionWuWindows N Δ V) \ univ.biUnion P) +
      ρ*boxTheta N ((N:ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V))
    (hcell : ∀ a, termCount p j N δ (convolutionWuWindows N Δ V) (P a) ≤
      (1-H a+ρ)*gamma5ClassicalMainMass N δ (convolutionWuWindows N Δ V) (P a)) :
    termCount p j N δ (convolutionWuWindows N Δ V)
        (termLabels p j N δ (convolutionWuWindows N Δ V)) ≤
      (1+ρ)^2*gamma5ClassicalMainMass N δ (convolutionWuWindows N Δ V)
        (termLabels p j N δ (convolutionWuWindows N Δ V)) -
      ∑ a, H a*gamma5ClassicalMainMass N δ (convolutionWuWindows N Δ V) (P a) +
      ρ*boxTheta N ((N:ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) := by
  exact gamma5Gain_finite_upper hρ
    (term_count_partition p j N δ _ _ P hd hs)
    (gamma5Gain_main_mass_partition N δ _ _ P hd hs)
    (fun a => term_mask_mass_nonneg h j hN hδ hδhi hb (hs a)) hclass hcell

end Wu2008DoubleSieve.MotherPair
