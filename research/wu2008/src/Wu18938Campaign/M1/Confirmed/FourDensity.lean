import Wu18938Campaign.M1.Confirmed.FourGeometry

noncomputable section

namespace Wu18938Campaign.M1.Confirmed.Four

open Wu2008DoubleSieve FourPrimeNonunit Finset Real
open scoped Classical

theorem restricted_density (m : ℕ) {η δ ρ ε : ℝ}
    (hη : 0 < η) (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hρ : 0 < ρ) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible → ∀ j : Fin 4,
      ∀ P : Gamma16Profile → Prop,
      let G := (sourceFamily N δ Δ V p j).restrictLabels P
      G.primeMass ≤ G.mass *
        (((1 + ρ) * (1 + ρ * exp (-eulerMascheroniConstant)) * (8 / (1 - 2 * δ))) *
          wuSingularSeries N / log N) +
        ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  have hpos : 0 < max 1 (1 / (η / 10)) := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  obtain ⟨T, hT4, ht⟩ := roughBox_labelled_density m hη hδ hδhi
    (show 0 < η / 10 by positivity) (pow_pos hpos (m + 3)) (pow_pos hpos (m + 4)) hρ he
  refine ⟨T, hT4, ?_⟩
  intro N hN heven i Δ V hb p hp j P G
  have hN2 : 2 ≤ N := by omega
  let L := sourceFamily N δ Δ V p j
  apply ht N hN heven i Δ V hb Gamma16Profile G
  · intro x hx
    have hg := geometry hb hN2 hη hδ p hp j (mem_filter.mp hx).1
    exact ⟨hg.power_lower, hg.power_upper⟩
  · intro x hx
    have hd := (profile_data (mem_filter.mp (mem_filter.mp hx).1).1).1
    change 1 ≤ (convolutionCoeff (convolutionWuWindows N Δ V) x.1 : ℝ)
    exact_mod_cast (Nat.succ_le_of_lt (mem_boxConvolutionSupport.mp hd))
  · intro e
    exact (L.restrictLabels_fibre_le P e).trans (family_fibre hb hN2 hη hδ p hp j e)
  · intro x hx
    exact relative_roughness hb hN2 hη hδ p hp j (mem_filter.mp hx).1
  · intro ell hell
    have hsub : G.weightAt ell ≤ L.weightAt ell :=
      L.restrictLabels_sum_le P _ (fun x hx =>
        mul_nonneg (L.weight_nonneg x hx) (Nat.cast_nonneg _))
    exact hsub.trans (by
      rw [sourceFamily_weightAt_prime V p j hell]
      exact fixed_output hb hN2 hη hδ p hp j ell)

theorem actual_nonunit_density (m : ℕ) {η δ ρ ε : ℝ}
    (hη : 0 < η) (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hρ : 0 < ρ) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible → ∀ j : Fin 4,
      actualSource N δ p (convolutionWuWindows N Δ V) j ≤
        (sourceFamily N δ Δ V p j).mass *
          (((1 + ρ) * (1 + ρ * exp (-eulerMascheroniConstant)) * (8 / (1 - 2 * δ))) *
            wuSingularSeries N / log N) +
          ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨T, hT4, ht⟩ := restricted_density m hη hδ hδhi hρ he
  refine ⟨T, hT4, ?_⟩
  intro N hN heven i Δ V hb p hp j
  have hd := ht N hN heven i Δ V hb p hp j (fun _ => True)
  have hid : (sourceFamily N δ Δ V p j).restrictLabels (fun _ => True) =
      sourceFamily N δ Δ V p j := by
    unfold LabelledPhysical.Family.restrictLabels
    simp only [filter_true]
  rw [hid] at hd
  dsimp only at hd
  have ha := actual_source_le (N := N) (δ := δ) p (convolutionWuWindows N Δ V)
    (fun _ h => hb.support_pos h) (hT4.trans hN) heven j
  rw [(sourceFamily_dictionary N δ Δ V p j).1] at hd
  exact ha.trans hd

end Wu18938Campaign.M1.Confirmed.Four
