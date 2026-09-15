import Wu18938Campaign.M1.Confirmed.TripleGeometry

noncomputable section

namespace Wu18938Campaign.M1.Confirmed.Triple

open Wu2008DoubleSieve LowerTripleGrouped Finset Real
open scoped Classical

theorem restricted_density (m : ℕ) {η δ ρ ε : ℝ}
    (hη : 0 < η) (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hρ : 0 < ρ) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible → ∀ j : Fin 6,
      ∀ P : Label → Prop,
      let G := (sourceFamily N δ Δ V p j).restrictLabels P
      G.primeMass ≤ G.mass *
        (((1 + ρ) * (1 + ρ * exp (-eulerMascheroniConstant)) * (8 / (1 - 2 * δ))) *
          wuSingularSeries N / log N) +
        ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  have hpos : 0 < max 1 (1 / (η / 10)) := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  obtain ⟨T, hT4, ht⟩ := roughBox_labelled_density m hη hδ hδhi
    (show 0 < η / 10 by positivity) (pow_pos hpos (m + 2)) (pow_pos hpos (m + 3)) hρ he
  refine ⟨T, hT4, ?_⟩
  intro N hN heven i Δ V hb p hp j P G
  have hN2 : 2 ≤ N := by omega
  let L := sourceFamily N δ Δ V p j
  apply ht N hN heven i Δ V hb Label G
  · intro x hx
    have hg := geometry hb hN2 hη hδ p hp j (mem_filter.mp hx).1
    exact ⟨hg.power_lower, hg.power_upper⟩
  · intro x hx
    exact source_weight_one_le p j (mem_filter.mp hx).1
  · intro e
    exact (L.restrictLabels_fibre_le P e).trans (fixed_cofactor hb hN2 hη hδ p hp j e)
  · intro x hx
    exact relative_roughness hb hN2 hη hδ p hp j (mem_filter.mp hx).1
  · intro ell _
    exact (L.restrictLabels_sum_le P _ (fun x hx =>
      mul_nonneg (L.weight_nonneg x hx) (Nat.cast_nonneg _))).trans
      (fixed_output hb hN2 hη hδ p hp j ell)

theorem gamma_dictionary {m i N : ℕ} {η δ Δ : ℝ} {V : Fin i → ℝ}
    (hb : RoughBox m η δ N i Δ V) (hN : 2 ≤ N) (hη : 0 < η) (hδ : 0 < δ)
    (p : SecondFunctionalParameters) (hp : p.MotherAdmissible) (j : Fin 6) :
    secondFunctionalMotherGammaSum p N δ (convolutionWuWindows N Δ V) (10 + j.val) =
      actualSourceMass N δ Δ V p j := by
  unfold secondFunctionalMotherGammaSum actualSourceMass sourceMass
  apply sum_congr rfl
  intro d hd
  have hs0 : 0 < p.s := by linarith [hp.one_le_s]
  have h30 := hs0.trans_le hp.s_le_kappa3
  have h20 := h30.trans hp.kappa3_lt_kappa2
  have h10 := h20.trans hp.kappa2_lt_kappa1
  have hab := hb.cutoff_antitone hN hη hδ hd h10 hp.kappa1_le_S
  have hbc := hb.cutoff_antitone hN hη hδ hd h20 hp.kappa2_lt_kappa1.le
  have hce := hb.cutoff_antitone hN hη hδ hd h30 hp.kappa3_lt_kappa2.le
  have hef := hb.cutoff_antitone hN hη hδ hd hs0 hp.s_le_kappa3
  fin_cases j
  all_goals norm_num only [Fin.val_zero, Fin.val_mk, Nat.reduceAdd]
  all_goals first
    | rw [secondFunctionalMother_gamma10_ordered_source N d N hab hbc hce hef]
    | rw [secondFunctionalMother_gamma11_ordered_source N d N hab hbc hce hef]
    | rw [secondFunctionalMother_gamma12_ordered_source N d N hab hbc hce hef]
    | rw [secondFunctionalMother_gamma13_ordered_source N d N hab hbc hce hef]
    | rw [secondFunctionalMother_gamma14_ordered_source N d N hab hbc hce hef]
    | rw [secondFunctionalMother_gamma15_ordered_source N d N hab hbc hce hef]
  all_goals simp [actualPre, actualBands, bands, and_assoc]

theorem gamma_source {m i N : ℕ} {η δ Δ : ℝ} {V : Fin i → ℝ}
    (hb : RoughBox m η δ N i Δ V) (hN : 4 ≤ N) (hη : 0 < η) (hδ : 0 < δ)
    (heven : Even N) (p : SecondFunctionalParameters) (hp : p.MotherAdmissible) (j : Fin 6) :
    secondFunctionalMotherGammaSum p N δ (convolutionWuWindows N Δ V) (10 + j.val) ≤
      (sourceFamily N δ Δ V p j).primeMass := by
  rw [gamma_dictionary hb (by omega) hη hδ p hp j]
  exact source_upper (fun _ hd => hb.support_pos hd) hN heven

theorem gamma_density (m : ℕ) {η δ ρ ε : ℝ}
    (hη : 0 < η) (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hρ : 0 < ρ) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible → ∀ j : Fin 6,
      secondFunctionalMotherGammaSum p N δ (convolutionWuWindows N Δ V) (10 + j.val) ≤
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
  exact (gamma_source hb (hT4.trans hN) hη hδ heven p hp j).trans hd

end Wu18938Campaign.M1.Confirmed.Triple
