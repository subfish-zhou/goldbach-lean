import MathlibNt.Wu2008DoubleSieve.SecondFunctionalFourPrimeSieveSmall
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalLabelledR1Relative
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalLabelledRestriction

namespace Wu2008DoubleSieve.FourPrimeNonunit
open Finset
open scoped Classical

/-- Reinstantiate the signed remainder theorem on the restricted family itself. -/
theorem source_restricted_R1_theta (k : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible → ∀ j : Fin 4,
      ∀ P : Gamma16Profile → Prop, ∀ Z : ℝ,
      ((sourceFamily N δ Δ V p j).restrictLabels P).R1
        (⌊(N:ℝ)^(1/2-δ)⌋₊+1) Z ≤
        ε * boxTheta N ((N:ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) := by
  let η := wuLocalExponent k δ / 10
  let H := max 1 (1/η)
  have hη : 0 < η := div_pos (wuLocalExponent_pos k hδ hδhi) (by norm_num)
  obtain ⟨T1,hT1,hr⟩ := LabelledPhysical.Family.R1_theta_relative k hδ hδhi hε hη
    (show 0 ≤ H^(k+3) by dsimp [H]; positivity)
  obtain ⟨T2,_,hm⟩ := source_all_multiplicities k hδ hδhi
  refine ⟨max T1 T2,hT1.trans (le_max_left _ _),?_⟩
  intro N hN i Δ V hb p hp j P Z
  have hN1 := (le_max_left T1 T2).trans hN
  have hN2 := (le_max_right T1 T2).trans hN
  have hNtwo : 2 ≤ N := by have := hT1.trans hN1; omega
  have hf := ((hm N hN2 i Δ V hb p hp).1 j).2.2.1
  apply hr N hN1 i Δ V hb Gamma16Profile ((sourceFamily N δ Δ V p j).restrictLabels P)
    _ _ _ Z
  · intro x hx
    have hg := actual_source_geometry hNtwo hδ hδhi hb p hp j (mem_filter.mp hx).1
    exact ⟨hg.power_lower,hg.power_upper⟩
  · intro x hx
    have hprof : x ∈ actualProfiles N δ p (convolutionWuWindows N Δ V) j :=
      (mem_filter.mp (mem_filter.mp hx).1).1
    change (1 : ℝ) ≤ (convolutionCoeff (convolutionWuWindows N Δ V) x.1 : ℝ)
    exact_mod_cast (mem_boxConvolutionSupport.mp (profile_data hprof).1)
  · intro e
    exact ((sourceFamily N δ Δ V p j).restrictLabels_fibre_le P e).trans (hf e)

/-- All four independently chosen predicates occur after the same threshold. -/
theorem source_restricted_R1_four_theta (k : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible →
      ∀ P : Fin 4 → Gamma16Profile → Prop, ∀ Z : ℝ,
      (∑ j : Fin 4, ((sourceFamily N δ Δ V p j).restrictLabels (P j)).R1
        (⌊(N:ℝ)^(1/2-δ)⌋₊+1) Z) ≤
        ε * boxTheta N ((N:ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨T,hT,hr⟩ := source_restricted_R1_theta k hδ hδhi
    (show 0 < ε/4 by positivity)
  refine ⟨T,hT,?_⟩
  intro N hN i Δ V hb p hp P Z
  calc
    _ ≤ ∑ _j : Fin 4, (ε/4) *
        boxTheta N ((N:ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) :=
      sum_le_sum (fun j _ => hr N hN i Δ V hb p hp j (P j) Z)
    _ = _ := by simp; ring

theorem source_restrict_true {N : ℕ} (L : LabelledPhysical.Family Gamma16Profile N) :
    L.restrictLabels (fun _ => True) = L := by
  cases L
  simp [LabelledPhysical.Family.restrictLabels]

/-- The original four families, without any coprimality or roughness restriction. -/
theorem source_R1_four_theta (k : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible → ∀ Z : ℝ,
      (∑ j : Fin 4, (sourceFamily N δ Δ V p j).R1
        (⌊(N:ℝ)^(1/2-δ)⌋₊+1) Z) ≤
        ε * boxTheta N ((N:ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨T,hT,hr⟩ := source_restricted_R1_four_theta k hδ hδhi hε
  refine ⟨T,hT,?_⟩
  intro N hN i Δ V hb p hp Z
  simpa only [source_restrict_true] using hr N hN i Δ V hb p hp (fun _ _ => True) Z

end Wu2008DoubleSieve.FourPrimeNonunit
