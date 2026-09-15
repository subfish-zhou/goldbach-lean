import Wu18938Campaign.M1.Confirmed.TripleDensity
import Wu18938Campaign.M1.Confirmed.LabelledExceptions
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalLowerTripleRoughPurification

noncomputable section

namespace Wu18938Campaign.M1.Confirmed.Triple

open Wu2008DoubleSieve LowerTripleGrouped Finset Real
open scoped Classical

theorem primeMass_rough (m : ℕ) {η δ ε : ℝ}
    (hη : 0 < η) (hδ : 0 < δ) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible → ∀ j : Fin 6,
      (sourceFamily N δ Δ V p j).primeMass ≤ (roughFamily N δ Δ V p j).primeMass +
        ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  have hpos : 0 < max 1 (1 / (η / 10)) := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  obtain ⟨T,hT4,ht⟩ := roughBox_labelled_exceptions m hη hδ
    (show 0 < η / 10 by positivity) (pow_pos hpos (m + 2)) (pow_pos hpos (m + 3)) he
  refine ⟨T,hT4,?_⟩
  intro N hN i Δ V hb p hp j
  let L := sourceFamily N δ Δ V p j
  have hf := L.primeMass_le_restrict_add_square_add_bad profileRough
    ((N : ℝ) ^ (η / 10)) (by
      intro x hx hc hn
      exact masked_good_nonrough_square (source_mask p j hx).2 hc hn
        (relative_roughness hb (by omega) hη hδ p hp j hx))
  have herr := ht N hN i Δ V hb Label L
    (fixed_cofactor hb (by omega) hη hδ p hp j)
    (fun ell _ => fixed_output hb (by omega) hη hδ p hp j ell)
  change L.primeMass ≤ (roughFamily N δ Δ V p j).primeMass + _ + _ at hf
  linarith only [hf,herr]

theorem rough_density (m : ℕ) {η δ ρ ε : ℝ}
    (hη : 0 < η) (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hρ : 0 < ρ) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible → ∀ j : Fin 6,
      (sourceFamily N δ Δ V p j).primeMass ≤ (roughFamily N δ Δ V p j).mass *
        (((1 + ρ) * (1 + ρ * exp (-eulerMascheroniConstant)) * (8 / (1 - 2 * δ))) *
          wuSingularSeries N / log N) +
        ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨T0,hT04,hpur⟩ := primeMass_rough m hη hδ (half_pos he)
  obtain ⟨T1,_,hden⟩ := restricted_density m hη hδ hδhi hρ (half_pos he)
  refine ⟨max T0 T1,hT04.trans (le_max_left _ _),?_⟩
  intro N hN heven i Δ V hb p hp j
  have hp' := hpur N (by omega) i Δ V hb p hp j
  have hd := hden N (by omega) heven i Δ V hb p hp j profileRough
  change (roughFamily N δ Δ V p j).primeMass ≤ (roughFamily N δ Δ V p j).mass * _ + _ at hd
  linarith only [hp',hd]

end Wu18938Campaign.M1.Confirmed.Triple
