import Wu18938Campaign.M1.Confirmed.FiniteSeed
import Wu18938Campaign.M1.Confirmed.PairPacking

noncomputable section

namespace Wu18938Campaign.M1.Confirmed.Pair

open Wu2008DoubleSieve MotherPair Finset Real
open scoped Classical

theorem cell_seed (p : SecondFunctionalParameters) (hp : AnalyticParameters p)
    (m : ℕ) {η δ ε : ℝ} (hη : 0 < η) (hδ : 0 < δ) (hδhi : δ ≤ 1 / 100) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ P Q : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      (N : ℝ) ^ (η * min (1 / p.S) ((1 - 2 / p.kappa3) / 2)) ≤ P / Δ →
      (N : ℝ) ^ (η * min (1 / p.S) ((1 - 2 / p.kappa3) / 2)) ≤ Q / Δ →
      P ≤ N → Q ≤ N → ∀ j : Term,
      gamma5GainCell N Δ P Q (convolutionWuWindows N Δ V) ⊆
        termLabels p j N δ (convolutionWuWindows N Δ V) →
      (∀ x ∈ gamma5GainCell N Δ P Q (convolutionWuWindows N Δ V),
        Hratio p j (gamma5MassCoordinate ((N : ℝ) ^ (1 / 2 - δ) / x.1) x.2.1)
          (gamma5MassCoordinate ((N : ℝ) ^ (1 / 2 - δ) / x.1) x.2.2) ≤ 13 / 5) →
      termCount p j N δ (convolutionWuWindows N Δ V)
        (gamma5GainCell N Δ P Q (convolutionWuWindows N Δ V)) ≤
        (1 - HighSixPhase7.seed + ε) *
          gamma5ClassicalMainMass N δ (convolutionWuWindows N Δ V)
            (gamma5GainCell N Δ P Q (convolutionWuWindows N Δ V)) := by
  have hc := classical_cap hp
  have hζ : 0 < η * min (1 / p.S) ((1 - 2 * (1 / p.kappa3)) / 2) :=
    mul_pos hη (lt_min (by have := hc.three_le_S; positivity) (by linarith [hc.cap_lt_half]))
  obtain ⟨T,hT4,hT⟩ := Rebox.seed_upper (m + 2) hζ hδ hδhi he
  refine ⟨T,hT4,?_⟩
  intro N hN heven i Δ P Q V hb hP hQ hPN hQN j hsub hv
  have hsub' := hsub.trans (term_cap hb (by omega) hη hδ p hp j)
  have hchild := child_rough hb (by omega) hη hδ hc
    (by simpa only [mul_one_div] using hP) (by simpa only [mul_one_div] using hQ) hPN hQN hsub'
  have hbound := hT N hN heven (i + 2) Δ (Fin.cons P (Fin.cons Q V)) hchild
    (13 / 5) (by norm_num) le_rfl
  rw [child_theta] at hbound
  exact (cell_count hb (by omega) hη hδ p hp j (by norm_num) hsub hv).trans hbound

theorem term_seed_subtract (p : SecondFunctionalParameters) (hp : AnalyticParameters p)
    (m : ℕ) {η δ τ ε : ℝ} (hη : 0 < η) (hδ : 0 < δ) (hδhi : δ ≤ 1 / 100)
    (hτ : 0 < τ) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ P Q : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      (N : ℝ) ^ (η * min (1 / p.S) ((1 - 2 / p.kappa3) / 2)) ≤ P / Δ →
      (N : ℝ) ^ (η * min (1 / p.S) ((1 - 2 / p.kappa3) / 2)) ≤ Q / Δ →
      P ≤ N → Q ≤ N → ∀ j : Term,
      gamma5GainCell N Δ P Q (convolutionWuWindows N Δ V) ⊆
        termLabels p j N δ (convolutionWuWindows N Δ V) →
      (∀ x ∈ gamma5GainCell N Δ P Q (convolutionWuWindows N Δ V),
        Hratio p j (gamma5MassCoordinate ((N : ℝ) ^ (1 / 2 - δ) / x.1) x.2.1)
          (gamma5MassCoordinate ((N : ℝ) ^ (1 / 2 - δ) / x.1) x.2.2) ≤ 13 / 5) →
      termCount p j N δ (convolutionWuWindows N Δ V)
        (termLabels p j N δ (convolutionWuWindows N Δ V)) ≤
        (1 + τ) ^ 2 * gamma5ClassicalMainMass N δ (convolutionWuWindows N Δ V)
          (termLabels p j N δ (convolutionWuWindows N Δ V)) -
        HighSixPhase7.seed * gamma5ClassicalMainMass N δ (convolutionWuWindows N Δ V)
          (gamma5GainCell N Δ P Q (convolutionWuWindows N Δ V)) +
        ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨T0,hT04,h0⟩ := cell_seed p hp m hη hδ hδhi hτ
  obtain ⟨T1,_,h1⟩ := term_mask_upper p hp m hη hδ hτ he
  refine ⟨max T0 T1,hT04.trans (le_max_left _ _),?_⟩
  intro N hN heven i Δ P Q V hb hP hQ hPN hQN j hsub hv
  let W := convolutionWuWindows N Δ V
  let X := termLabels p j N δ W
  let C := gamma5GainCell N Δ P Q W
  have hc := h0 N (by omega) heven i Δ P Q V hb hP hQ hPN hQN j hsub hv
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

end Wu18938Campaign.M1.Confirmed.Pair
