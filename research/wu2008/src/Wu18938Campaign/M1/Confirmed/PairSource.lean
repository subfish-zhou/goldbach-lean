import Wu18938Campaign.M1.Confirmed.PairClassical
import Wu18938Campaign.M1.Confirmed.FiniteMother
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalMotherPairClassicalPorts

noncomputable section

namespace Wu18938Campaign.M1.Confirmed.Pair

open Wu2008DoubleSieve MotherPair Finset Real
open scoped Classical

theorem term_cap {m i N : ℕ} {η δ Δ : ℝ} {V : Fin i → ℝ}
    (hb : RoughBox m η δ N i Δ V) (hN : 2 ≤ N) (hη : 0 < η) (hδ : 0 < δ)
    (p : SecondFunctionalParameters) (hp : AnalyticParameters p) (j : Term) :
    termLabels p j N δ (convolutionWuWindows N Δ V) ⊆
      capLabels p.S (1 / p.kappa3) N δ (convolutionWuWindows N Δ V) := by
  have hr {B C D : ℝ} (hD : D ≤ 1 / p.kappa3) :
      rectLabels N δ (convolutionWuWindows N Δ V) (1 / p.S) B C D ⊆
        capLabels p.S (1 / p.kappa3) N δ (convolutionWuWindows N Δ V) := by
    intro x hx
    obtain ⟨hx,hp',hq',hpN,hqN,hpa,_,_,hqd,hpq⟩ := mem_filter.mp hx
    have hR := (hb.support_geometry hN hη hδ (mem_product.mp hx).1).2.2.1
    exact mem_filter.mpr ⟨hx,hp',hq',hpN,hqN,hpa,hpq,
      hqd.trans_le (rpow_le_rpow_of_exponent_le hR.le hD)⟩
  obtain ⟨_,_,hbc,hce,_,_⟩ := parameter_order hp
  cases j with
  | gammaFive => exact hr hce.le
  | gammaSix => exact hr le_rfl
  | gammaSeven => exact hr (hbc.le.trans hce.le)
  | gammaEight => exact hr hce.le

theorem gamma_dictionary {m i N : ℕ} {η δ Δ : ℝ} {V : Fin i → ℝ}
    (hb : RoughBox m η δ N i Δ V) (hN : 2 ≤ N) (hη : 0 < η) (hδ : 0 < δ)
    (p : SecondFunctionalParameters) (hp : AnalyticParameters p) (j : Term) :
    termCount p j N δ (convolutionWuWindows N Δ V) (termLabels p j N δ (convolutionWuWindows N Δ V)) =
      secondFunctionalMotherGammaSum p N δ (convolutionWuWindows N Δ V) j.index := by
  obtain ⟨_,_,hbc,hce,hef,hf⟩ := parameter_order hp
  have hbound {x : ℝ} (hx : x ≤ 1) (d : ℕ)
      (hd : d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V)) :
      ((N : ℝ) ^ (1 / 2 - δ) / d) ^ x ≤ N := by
    have hg := hb.support_geometry hN hη hδ hd
    exact (show ((N : ℝ) ^ (1 / 2 - δ) / d) ^ x ≤ (N : ℝ) ^ (1 / 2 - δ) / d by
      simpa only [rpow_one] using rpow_le_rpow_of_exponent_le hg.2.2.1.le hx).trans hg.2.2.2
  have hB := hbound (show 1 / p.kappa1 ≤ 1 by linarith)
  have hC := hbound (show 1 / p.kappa2 ≤ 1 by linarith)
  have hE := hbound (show 1 / p.kappa3 ≤ 1 by linarith)
  cases j with
  | gammaFive =>
    simp only [termCount,termLabels,fixedCount,Term.index]
    rw [rect_sum N δ _ _ _ _ _ _ hC hC]
    unfold secondFunctionalMotherGammaSum
    apply sum_congr rfl
    intro d _
    rw [secondFunctionalMotherGamma,fourthRowMotherPair,sum_comm]
    simp only [mul_sum,mul_ite,mul_zero,wuLocalCutoff,gamma5ClassicalProduct]
  | gammaSix =>
    simp only [termCount,termLabels,fixedCount,Term.index]
    rw [rect_sum N δ _ _ _ _ _ _ hB hE]
    unfold secondFunctionalMotherGammaSum
    apply sum_congr rfl
    intro d _
    rw [secondFunctionalMotherGamma,fourthRowMotherPair,sum_comm]
    simp only [mul_sum,mul_ite,mul_zero,wuLocalCutoff,gamma5ClassicalProduct]
  | gammaSeven =>
    simp only [termCount,termLabels,Term.index]
    rw [rect_sum N δ _ _ _ _ _ _ hB hB]
    unfold secondFunctionalMotherGammaSum
    apply sum_congr rfl
    intro d hd
    obtain ⟨_,hbc,hce,hef⟩ := roughBox_mother_cutoffs hb hN hη hδ p hp.mother hd
    rw [raw_seven N d N (hbc.trans (hce.trans hef))]
    simp only [mul_sum,mul_ite,mul_zero,wuLocalCutoff,gamma5ClassicalProduct]
  | gammaEight =>
    simp only [termCount,termLabels,Term.index]
    rw [rect_sum N δ _ _ _ _ _ _ hB hC]
    unfold secondFunctionalMotherGammaSum
    apply sum_congr rfl
    intro d hd
    obtain ⟨hab,hbc,hce,hef⟩ := roughBox_mother_cutoffs hb hN hη hδ p hp.mother hd
    rw [raw_eight N d N hab (hbc.trans (hce.trans hef)) (hce.trans hef)]
    simp only [mul_sum,mul_ite,mul_zero,wuLocalCutoff,gamma5ClassicalProduct]

theorem term_mask_upper (p : SecondFunctionalParameters) (hp : AnalyticParameters p)
    (m : ℕ) {η δ τ ε : ℝ} (hη : 0 < η) (hδ : 0 < δ) (hτ : 0 < τ) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      ∀ j : Term, ∀ X : Finset Gamma5ClassicalLabel,
      X ⊆ termLabels p j N δ (convolutionWuWindows N Δ V) →
      termCount p j N δ (convolutionWuWindows N Δ V) X ≤
        (1 + τ) ^ 2 * gamma5ClassicalMainMass N δ (convolutionWuWindows N Δ V) X +
        ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨T,hT4,hT⟩ := mask_upper (classical_cap hp) m hη hδ hτ he
  refine ⟨T,hT4,?_⟩
  intro N hN heven i Δ V hb j X hX
  have hcap := hX.trans (term_cap hb (by omega) hη hδ p hp j)
  exact (termCount_le_fixedCount p j N δ _ _ X hcap).trans (hT N hN heven i Δ V hb X hcap)

theorem gamma_classical (p : SecondFunctionalParameters) (hp : AnalyticParameters p)
    (m : ℕ) {η δ τ ε : ℝ} (hη : 0 < η) (hδ : 0 < δ) (hτ : 0 < τ) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      ∀ j : Term,
      secondFunctionalMotherGammaSum p N δ (convolutionWuWindows N Δ V) j.index ≤
        (1 + τ) ^ 2 * gamma5ClassicalMainMass N δ (convolutionWuWindows N Δ V)
          (termLabels p j N δ (convolutionWuWindows N Δ V)) +
        ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨T,hT4,hT⟩ := term_mask_upper p hp m hη hδ hτ he
  refine ⟨T,hT4,?_⟩
  intro N hN heven i Δ V hb j
  rw [← gamma_dictionary hb (by omega) hη hδ p hp j]
  exact hT N hN heven i Δ V hb j _ (Subset.refl _)

end Wu18938Campaign.M1.Confirmed.Pair
