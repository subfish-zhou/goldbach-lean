import Wu18938Campaign.M1.Confirmed.PairMass

noncomputable section

namespace Wu18938Campaign.M1.Confirmed.Pair

open Wu2008DoubleSieve MotherPair Finset Real
open scoped Classical

def classicalIntegral (p : SecondFunctionalParameters) : Term → ℝ
  | .gammaFive => rectIntegral (1 / p.S) (1 / p.kappa2) (1 / p.S) (1 / p.kappa2)
  | .gammaSix => rectIntegral (1 / p.S) (1 / p.kappa1) (1 / p.kappa2) (1 / p.kappa3)
  | .gammaSeven => rectIntegral (1 / p.S) (1 / p.kappa1) (1 / p.S) (1 / p.kappa1)
  | .gammaEight => rectIntegral (1 / p.S) (1 / p.kappa1) (1 / p.kappa1) (1 / p.kappa2)

theorem term_mass (p : SecondFunctionalParameters) (hp : AnalyticParameters p)
    (m : ℕ) {η δ ε : ℝ} (hη : 0 < η) (hδ : 0 < δ) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      ∀ j : Term,
      |gamma5ClassicalMainMass N δ (convolutionWuWindows N Δ V)
          (termLabels p j N δ (convolutionWuWindows N Δ V)) -
        classicalIntegral p j * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V)| ≤
        ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  have hc := classical_cap hp
  have ha : 1 / 10 ≤ 1 / p.S :=
    one_div_le_one_div_of_le (by linarith [hc.three_le_S]) (by linarith [hc.S_le_five])
  obtain ⟨T,hT4,hT⟩ := rectangle_mass ha hc.cap_lt_half m hη hδ he
  refine ⟨T,hT4,?_⟩
  intro N hN i Δ V hb j
  obtain ⟨_,hab,hbc,hce,_,_⟩ := parameter_order hp
  have hr := hT N hN i Δ V hb
  cases j with
  | gammaFive =>
    exact hr _ _ _ _ le_rfl (hab.trans hbc.le) hce.le le_rfl (hab.trans hbc.le) hce.le
  | gammaSix =>
    exact hr _ _ _ _ le_rfl hab (hbc.le.trans hce.le) (hab.trans hbc.le) hce.le le_rfl
  | gammaSeven =>
    exact hr _ _ _ _ le_rfl hab (hbc.le.trans hce.le) le_rfl hab (hbc.le.trans hce.le)
  | gammaEight =>
    exact hr _ _ _ _ le_rfl hab (hbc.le.trans hce.le) hab hbc.le hce.le

theorem gamma_integral (p : SecondFunctionalParameters) (hp : AnalyticParameters p)
    (m : ℕ) {η δ τ ε : ℝ}
    (hη : 0 < η) (hδ : 0 < δ) (hτ : 0 < τ) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      ∀ j : Term,
      secondFunctionalMotherGammaSum p N δ (convolutionWuWindows N Δ V) j.index ≤
        (1 + τ) ^ 2 * classicalIntegral p j *
          boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) +
        ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  have hP : 0 < (1 + τ) ^ 2 := by positivity
  obtain ⟨T0,hT04,h0⟩ := gamma_classical p hp m hη hδ hτ (half_pos he)
  obtain ⟨T1,_,h1⟩ := term_mass p hp m hη hδ
    (show 0 < ε / (2 * (1 + τ) ^ 2) by positivity)
  refine ⟨max T0 T1,hT04.trans (le_max_left _ _),?_⟩
  intro N hN heven i Δ V hb j
  have hc := h0 N (by omega) heven i Δ V hb j
  have hm := (le_abs_self _).trans (h1 N (by omega) i Δ V hb j)
  have hm' := mul_le_mul_of_nonneg_left hm hP.le
  have heq : (1 + τ) ^ 2 * (ε / (2 * (1 + τ) ^ 2)) = ε / 2 := by
    field_simp
  rw [← mul_assoc,heq] at hm'
  nlinarith only [hc,hm']

end Wu18938Campaign.M1.Confirmed.Pair
