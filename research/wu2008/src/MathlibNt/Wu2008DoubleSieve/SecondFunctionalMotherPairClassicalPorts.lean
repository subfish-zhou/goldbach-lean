import MathlibNt.Wu2008DoubleSieve.SecondFunctionalMotherPairSource
import MathlibNt.Wu2008DoubleSieve.MotherPairClassicalUpper
import MathlibNt.Wu2008DoubleSieve.MotherPairMassMain

namespace Wu2008DoubleSieve.MotherPair
open Finset Real
open scoped Classical

/-- The actual rectangle integral, with no supremum substituted for its value. -/
noncomputable def classicalIntegral (p : SecondFunctionalParameters) : Term → ℝ
  | .gammaFive => rectIntegral (1/p.S) (1/p.kappa2) (1/p.S) (1/p.kappa2)
  | .gammaSix => rectIntegral (1/p.S) (1/p.kappa1) (1/p.kappa2) (1/p.kappa3)
  | .gammaSeven => rectIntegral (1/p.S) (1/p.kappa1) (1/p.S) (1/p.kappa1)
  | .gammaEight => rectIntegral (1/p.S) (1/p.kappa1) (1/p.kappa1) (1/p.kappa2)

theorem classical_cap {p : SecondFunctionalParameters} (hp : AnalyticParameters p) :
    CapAdmissible p.S (1/p.kappa3) := by
  obtain ⟨_,hab,hbc,hce,hef,hf⟩ := parameter_order hp
  exact ⟨hp.three_le_S,hp.S_le_five,(hab.trans hbc.le).trans hce.le,hef.trans_lt hf⟩

theorem classicalIntegral_bounds {p : SecondFunctionalParameters} (hp : AnalyticParameters p)
    (j : Term) : 0 ≤ classicalIntegral p j ∧
      classicalIntegral p j ≤ 16*(1/(1-2*(1/p.kappa3))) := by
  obtain ⟨ha,hab,hbc,hce,hef,hf⟩ := parameter_order hp
  have hU := hef.trans_lt hf
  have hA : (1/10:ℝ) ≤ 1/p.S := by linarith
  have hB := hA.trans hab
  have hC := hB.trans hbc.le
  have hAE := (hab.trans hbc.le).trans hce.le
  cases j with
  | gammaFive => exact rectIntegral_bounds hU hA (hab.trans hbc.le) hce.le hA (hab.trans hbc.le) hce.le
  | gammaSix => exact rectIntegral_bounds hU hA hab (hbc.le.trans hce.le) hC hce.le le_rfl
  | gammaSeven => exact rectIntegral_bounds hU hA hab (hbc.le.trans hce.le) hA hab (hbc.le.trans hce.le)
  | gammaEight => exact rectIntegral_bounds hU hA hab (hbc.le.trans hce.le) hB hbc.le hce.le

theorem rectLabels_subset_cap {S U B C D : ℝ} (hDU : D ≤ U)
    {i k N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hN : 2 ≤ N) (hδ : 0<δ) (hδhi : δ<1/2) (hb : wuSourceBox k δ N i Δ V) :
    rectLabels N δ (convolutionWuWindows N Δ V) (1/S) B C D ⊆
      capLabels S U N δ (convolutionWuWindows N Δ V) := by
  intro x hx
  obtain ⟨hx,hp,hq,hpN,hqN,hpa,_hpb,_hqc,hqd,hpq⟩ := mem_filter.mp hx
  have hR := (gamma5Mass_support_geometry hN hδ hδhi hb (mem_product.mp hx).1).2.2.1
  exact mem_filter.mpr ⟨hx,hp,hq,hpN,hqN,hpa,hpq,
    hqd.trans_le (rpow_le_rpow_of_exponent_le hR.le hDU)⟩

theorem termLabels_subset_cap {p : SecondFunctionalParameters} (hp : AnalyticParameters p)
    (j : Term) {i k N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hN : 2 ≤ N) (hδ : 0<δ) (hδhi : δ<1/2) (hb : wuSourceBox k δ N i Δ V) :
    termLabels p j N δ (convolutionWuWindows N Δ V) ⊆
      capLabels p.S (1/p.kappa3) N δ (convolutionWuWindows N Δ V) := by
  obtain ⟨_,_,hbc,hce,_,_⟩ := parameter_order hp
  cases j with
  | gammaFive => exact rectLabels_subset_cap hce.le hN hδ hδhi hb
  | gammaSix => exact rectLabels_subset_cap le_rfl hN hδ hδhi hb
  | gammaSeven => exact rectLabels_subset_cap (hbc.le.trans hce.le) hN hδ hδhi hb
  | gammaEight => exact rectLabels_subset_cap hce.le hN hδ hδhi hb

/-- Selected-prime sifting is compared before applying the fixed-cutoff sieve. -/
theorem termCount_le_fixedCount {i : ℕ} (p : SecondFunctionalParameters) (j : Term)
    (N : ℕ) (δ U : ℝ) (W : Fin i → Finset ℕ) (X : Finset Gamma5ClassicalLabel)
    (hX : X ⊆ capLabels p.S U N δ W) :
    termCount p j N δ W X ≤ fixedCount p.S N δ W X := by
  have hs : (∑ x ∈ X, (convolutionCoeff W x.1:ℝ)*
      (sourceSieveCount N (gamma5ClassicalProduct x) (x.1*N) (x.2.1:ℝ):ℝ)) ≤
      fixedCount p.S N δ W X := by
    apply sum_le_sum
    intro x hx
    have hz := (mem_filter.mp (hX hx)).2.2.2.2.2.1
    exact mul_le_mul_of_nonneg_left
      (gamma5Classical_source_count_antitone N (gamma5ClassicalProduct x) (x.1*N) hz)
      (Nat.cast_nonneg _)
  cases j with
  | gammaFive => exact le_rfl
  | gammaSix => exact le_rfl
  | gammaSeven => exact hs
  | gammaEight => exact hs

theorem term_mass (p : SecondFunctionalParameters) (hp : AnalyticParameters p) (k : ℕ)
    {δ ε : ℝ} (hδ : 0<δ) (hδhi : δ≤1/10) (hε : 0<ε) :
    ∃ T : ℕ, 4≤T ∧ ∀ N, T≤N → ∀ i Δ V, wuSourceBox k δ N i Δ V → ∀ j : Term,
      |gamma5ClassicalMainMass N δ (convolutionWuWindows N Δ V)
          (termLabels p j N δ (convolutionWuWindows N Δ V)) -
        classicalIntegral p j * boxTheta N ((N:ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V)| ≤
        ε*boxTheta N ((N:ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨ha,hab,hbc,hce,hef,hf⟩ := parameter_order hp
  have hA : (1/10:ℝ) ≤ 1/p.S := by linarith
  obtain ⟨T,hT,hm⟩ := rectangle_mass hA ((hab.trans hbc.le).trans hce.le)
    (hef.trans_lt hf) k hδ hδhi hε
  refine ⟨T,hT,?_⟩
  intro N hN i Δ V hb j
  have hm' := hm N hN i Δ V hb
  cases j with
  | gammaFive => exact hm' _ _ _ _ le_rfl (hab.trans hbc.le) hce.le le_rfl (hab.trans hbc.le) hce.le
  | gammaSix => exact hm' _ _ _ _ le_rfl hab (hbc.le.trans hce.le) (hab.trans hbc.le) hce.le le_rfl
  | gammaSeven => exact hm' _ _ _ _ le_rfl hab (hbc.le.trans hce.le) le_rfl hab (hbc.le.trans hce.le)
  | gammaEight => exact hm' _ _ _ _ le_rfl hab (hbc.le.trans hce.le) hab hbc.le hce.le

end Wu2008DoubleSieve.MotherPair
