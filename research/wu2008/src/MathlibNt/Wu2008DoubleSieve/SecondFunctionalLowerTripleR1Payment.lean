import MathlibNt.Wu2008DoubleSieve.SecondFunctionalLowerTripleFixedCofactor
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalLabelledR1Relative
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalLabelledRestriction

namespace Wu2008DoubleSieve.LowerTripleGrouped
open Finset
open scoped BigOperators Classical

/-- Reinstantiate the signed remainder theorem on each arbitrarily restricted actual family. -/
theorem source_restricted_R1_theta (k : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible → ∀ j : Fin 6,
      ∀ P : Label → Prop, ∀ Z : ℝ,
      ((sourceFamily N δ Δ V p j).restrictLabels P).R1
        (⌊(N:ℝ)^(1/2-δ)⌋₊+1) Z ≤
        ε * boxTheta N ((N:ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) := by
  let η := wuLocalExponent k δ / 10
  let H := max 1 (1/η)
  have hη : 0 < η := div_pos (wuLocalExponent_pos k hδ hδhi) (by norm_num)
  obtain ⟨T1,hT1,hr⟩ := LabelledPhysical.Family.R1_theta_relative k hδ hδhi hε hη
    (show 0 ≤ H^(k+2) by dsimp [H]; positivity)
  obtain ⟨T2,_,hm⟩ := source_fixed_cofactor_uniform k hδ hδhi
  refine ⟨max T1 T2,hT1.trans (le_max_left _ _),?_⟩
  intro N hN i Δ V hb p hp j P Z
  have hN1 := (le_max_left T1 T2).trans hN
  have hN2 := (le_max_right T1 T2).trans hN
  have hNtwo : 2 ≤ N := by have := hT1.trans hN1; omega
  apply hr N hN1 i Δ V hb Label ((sourceFamily N δ Δ V p j).restrictLabels P)
    _ _ _ Z
  · intro x hx
    have hg := source_geometry hNtwo hδ hδhi hb p hp j (mem_filter.mp hx).1
    exact ⟨hg.power_lower,hg.power_upper⟩
  · intro x hx
    exact source_weight_one_le p j (mem_filter.mp hx).1
  · intro E
    exact ((sourceFamily N δ Δ V p j).restrictLabels_fibre_le P E).trans
      (hm N hN2 i Δ V hb p hp j E)

/-- One total epsilon, with six independent predicates and cutoffs chosen after T. -/
theorem source_restricted_R1_six_theta (k : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible →
      ∀ P : Fin 6 → Label → Prop, ∀ Z : Fin 6 → ℝ,
      (∑ j : Fin 6, ((sourceFamily N δ Δ V p j).restrictLabels (P j)).R1
        (⌊(N:ℝ)^(1/2-δ)⌋₊+1) (Z j)) ≤
        ε * boxTheta N ((N:ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨T,hT,hr⟩ := source_restricted_R1_theta k hδ hδhi
    (show 0 < ε/6 by positivity)
  refine ⟨T,hT,?_⟩
  intro N hN i Δ V hb p hp P Z
  calc
    _ ≤ ∑ _j : Fin 6, (ε/6) *
        boxTheta N ((N:ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) :=
      sum_le_sum (fun j _ => hr N hN i Δ V hb p hp j (P j) (Z j))
    _ = _ := by simp; ring

end Wu2008DoubleSieve.LowerTripleGrouped
