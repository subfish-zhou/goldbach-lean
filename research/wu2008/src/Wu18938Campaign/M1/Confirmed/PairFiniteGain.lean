import Wu18938Campaign.M1.Confirmed.PairGainMass

noncomputable section

namespace Wu18938Campaign.M1.Confirmed.Pair

open Wu2008DoubleSieve MotherPair Finset Real
open scoped Classical

theorem term_packing_seed (p : SecondFunctionalParameters) (hp : AnalyticParameters p)
    (j : Term) (r : GainRectangle p j) (hrs : r.sample ≤ 13 / 5)
    (m : ℕ) {η δ τ ε : ℝ} (hη : 0 < η) (hδ : 0 < δ) (hδhi : δ ≤ 1 / 100)
    (hτ : 0 < τ) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      termCount p j N δ (convolutionWuWindows N Δ V)
        (termLabels p j N δ (convolutionWuWindows N Δ V)) ≤
        (1 + τ) ^ 2 * gamma5ClassicalMainMass N δ (convolutionWuWindows N Δ V)
          (termLabels p j N δ (convolutionWuWindows N Δ V)) -
        HighSixPhase7.seed * gamma5ClassicalMainMass N δ (convolutionWuWindows N Δ V)
          (packing N δ Δ V r) +
        ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨T0,hT04,h0⟩ := packing_seed p hp j r hrs m hη hδ hδhi hτ
  obtain ⟨T1,_,h1⟩ := term_mask_upper p hp m hη hδ hτ he
  refine ⟨max T0 T1,hT04.trans (le_max_left _ _),?_⟩
  intro N hN heven i Δ V hb
  let W := convolutionWuWindows N Δ V
  let X := termLabels p j N δ W
  let C := packing N δ Δ V r
  obtain ⟨hsub,hc⟩ := h0 N (by omega) heven i Δ V hb
  have hr := h1 N (by omega) heven i Δ V hb j (X \ C) sdiff_subset
  have hdis : Disjoint C (X \ C) := disjoint_sdiff_self_right
  have hu : C ∪ (X \ C) = X := union_sdiff_of_subset hsub
  have hcount : termCount p j N δ W X =
      termCount p j N δ W C + termCount p j N δ W (X \ C) := by
    conv_lhs => rw [← hu]
    cases j <;> simp only [termCount,fixedCount] <;> exact sum_union hdis
  have hmass : gamma5ClassicalMainMass N δ W X =
      gamma5ClassicalMainMass N δ W C + gamma5ClassicalMainMass N δ W (X \ C) := by
    unfold gamma5ClassicalMainMass
    conv_lhs => rw [← hu,sum_union hdis,mul_add]
  have hC0 : 0 ≤ gamma5ClassicalMainMass N δ W C := by
    have hh := term_mass_mono hb (by omega) hη hδ p hp j (empty_subset C) hsub
    simpa only [gamma5ClassicalMainMass,sum_empty,mul_zero] using hh
  have hpay := mul_le_mul_of_nonneg_right
    (show 1 - HighSixPhase7.seed + τ ≤ (1 + τ) ^ 2 - HighSixPhase7.seed by nlinarith) hC0
  rw [hcount,hmass]
  nlinarith only [hc,hr,hpay]

theorem gamma_rectangle_seed (p : SecondFunctionalParameters) (hp : AnalyticParameters p)
    (j : Term) (r : GainRectangle p j) (hrs : r.sample ≤ 13 / 5)
    (m : ℕ) {η δ τ ε : ℝ} (hη : 0 < η) (hδ : 0 < δ) (hδhi : δ ≤ 1 / 100)
    (hτ : 0 < τ) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      secondFunctionalMotherGammaSum p N δ (convolutionWuWindows N Δ V) j.index ≤
        ((1 + τ) ^ 2 * classicalIntegral p j -
          HighSixPhase7.seed * rectIntegral r.A r.B r.C r.D + ε) *
          boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  have hτp : 0 < (1 + τ) ^ 2 := by positivity
  obtain ⟨T0,hT04,h0⟩ := term_packing_seed p hp j r hrs m hη hδ hδhi hτ
    (show 0 < ε / 3 by positivity)
  obtain ⟨T1,_,h1⟩ := term_mass p hp m hη hδ
    (show 0 < ε / (3 * (1 + τ) ^ 2) by positivity)
  obtain ⟨T2,_,h2⟩ := packing_mass_lower p hp j r m hη hδ
    (show 0 < ε / (3 * HighSixPhase7.seed) from
      div_pos he (mul_pos (by norm_num) HighSixPhase7.seed_pos))
  refine ⟨max T0 (max T1 T2),hT04.trans (le_max_left _ _),?_⟩
  intro N hN heven i Δ V hb
  have hc := h0 N (by omega) heven i Δ V hb
  have hm := mul_le_mul_of_nonneg_left
    ((le_abs_self _).trans (h1 N (by omega) i Δ V hb j)) hτp.le
  have hg := mul_le_mul_of_nonneg_left (h2 N (by omega) i Δ V hb) HighSixPhase7.seed_pos.le
  have heq : (1 + τ) ^ 2 * (ε / (3 * (1 + τ) ^ 2)) = ε / 3 := by field_simp
  have heq' : HighSixPhase7.seed * (ε / (3 * HighSixPhase7.seed)) = ε / 3 := by
    field_simp [HighSixPhase7.seed_pos.ne']
  rw [← mul_assoc,heq] at hm
  have hg' : HighSixPhase7.seed * rectIntegral r.A r.B r.C r.D *
      boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) -
      (ε / 3) * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) ≤
      HighSixPhase7.seed * gamma5ClassicalMainMass N δ (convolutionWuWindows N Δ V)
        (packing N δ Δ V r) := by
    calc
      _ = (HighSixPhase7.seed * (rectIntegral r.A r.B r.C r.D -
          ε / (3 * HighSixPhase7.seed))) *
          boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
        rw [mul_sub,heq']
        ring
      _ ≤ _ := by simpa only [mul_assoc] using hg
  rw [gamma_dictionary hb (by omega) hη hδ p hp j] at hc
  nlinarith only [hc,hm,hg']

end Wu18938Campaign.M1.Confirmed.Pair
