import MathlibNt.Wu2008DoubleSieve.MotherPairGainAssembly

namespace Wu2008DoubleSieve.MotherPair
open Finset Set Real Filter
open scoped Classical Topology

theorem family_producers (p : SecondFunctionalParameters) (h : AnalyticParameters p)
    (j : Term) (F : Finset (GainRectangle p j)) (k : ℕ) (hk : 1 ≤ k) {δ ρ ζ : ℝ}
    (hδ : 0<δ) (hδhi : δ≤1/10) (hρ : 0<ρ) (hζ : 0<ζ) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ i : ℕ, ∀ Δ : ℝ, ∀ V : Fin i → ℝ, wuSourceBox k δ N i Δ V →
      1<Δ ∧ 1<gamma5GainScale N δ V ∧
      (∀ X : Finset Gamma5ClassicalLabel, X ⊆ termLabels p j N δ (convolutionWuWindows N Δ V) →
        termCount p j N δ (convolutionWuWindows N Δ V) X ≤
          (1+ρ)^2*gamma5ClassicalMainMass N δ (convolutionWuWindows N Δ V) X +
          ρ*boxTheta N ((N:ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V)) ∧
      |gamma5ClassicalMainMass N δ (convolutionWuWindows N Δ V)
          (termLabels p j N δ (convolutionWuWindows N Δ V)) -
          classicalIntegral p j*boxTheta N ((N:ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V)| ≤
        ρ*boxTheta N ((N:ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) ∧
      ∀ r : F,
        (packing N δ Δ V r.val ⊆ termLabels p j N δ (convolutionWuWindows N Δ V) ∧
        termCount p j N δ (convolutionWuWindows N Δ V) (packing N δ Δ V r.val) ≤
          (1-wuImprovementLimit true δ r.val.sample+ρ)*gamma5ClassicalMainMass N δ
            (convolutionWuWindows N Δ V) (packing N δ Δ V r.val)) ∧
        (rectIntegral r.val.A r.val.B r.val.C r.val.D-ζ)*
          boxTheta N ((N:ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) ≤
          gamma5ClassicalMainMass N δ (convolutionWuWindows N Δ V) (packing N δ Δ V r.val) := by
  choose TP hTP4 hTP using (fun r : F => packing_actual p h j r.val k hδ hδhi hρ)
  choose TM hTM4 hTM using (fun r : F => packing_mass p h j r.val k hδ hδhi hζ)
  obtain ⟨TC,hTC4,hTC⟩ := classical_term_mask_upper p h k hk hδ hδhi hρ hρ
  obtain ⟨TT,hTT4,hTT⟩ := term_mass p h k hδ hδhi hρ
  obtain ⟨TG,hTG⟩ := eventually_atTop.mp
    (gamma5Gain_mesh_eventually k hδ hδhi (by norm_num : (0:ℝ)<1))
  let T := max TC (max TT (max TG (max (univ.sup TP) (univ.sup TM))))
  refine ⟨T,hTC4.trans (le_max_left _ _),?_⟩
  intro N hN he i Δ V hb
  have hNC : TC ≤ N := (le_max_left _ _).trans hN
  have hNT : TT ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hNG : TG ≤ N := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hN))
  have hNP : ∀ r : F, TP r ≤ N := by
    intro r
    exact (le_sup (f := TP) (mem_univ r)).trans ((le_max_left _ _).trans
      ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hN))))
  have hNM : ∀ r : F, TM r ≤ N := by
    intro r
    exact (le_sup (f := TM) (mem_univ r)).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hN))))
  obtain ⟨hΔ,hR,_⟩ := hTG N hNG i Δ V hb
  refine ⟨hΔ,hR,hTC N hNC he i Δ V hb j,hTT N hNT i Δ V hb j,?_⟩
  intro r
  exact ⟨hTP r N (hNP r) he i Δ V hb,hTM r N (hNM r) i Δ V hb⟩

/-- Every fixed geometrically disjoint family gives its literal sampled H gain
for the original mother sum, with one error on the original Theta scale. -/
theorem fixed_family_original_upper (p : SecondFunctionalParameters) (h : AnalyticParameters p)
    (j : Term) (F : Finset (GainRectangle p j))
    (hF : (F : Set (GainRectangle p j)).Pairwise (fun r s => Disjoint (Set.Ico r.A r.B ×ˢ Set.Ico r.C r.D)
      (Set.Ico s.A s.B ×ˢ Set.Ico s.C s.D)))
    (k : ℕ) (hk : 1 ≤ k) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1/10) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ i : ℕ, ∀ Δ : ℝ, ∀ V : Fin i → ℝ, wuSourceBox k δ N i Δ V →
      secondFunctionalMotherGammaSum p N δ (convolutionWuWindows N Δ V) j.index ≤
        (classicalIntegral p j -
          (∑ r ∈ F, wuImprovementLimit true δ r.sample * rectIntegral r.A r.B r.C r.D) + ε) *
        boxTheta N ((N:ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) := by
  let C := classicalIntegral p j
  have hC : 0 ≤ C := (classicalIntegral_bounds h j).1
  let ρ := min 1 (ε/(16*(C+1)))
  have hρ : 0 < ρ := lt_min (by norm_num) (by positivity)
  have hρ1 : ρ ≤ 1 := min_le_left _ _
  have hpay : 16*(C+1)*ρ ≤ ε := by
    have hh := (le_div_iff₀ (show 0 < 16*(C+1) by positivity)).mp
      (min_le_right 1 (ε/(16*(C+1))))
    exact (mul_comm _ _).le.trans hh
  let ζ := ρ/((F.card:ℝ)+1)
  have hζ : 0 < ζ := by dsimp [ζ]; positivity
  have hζρ : (Fintype.card F:ℝ)*ζ ≤ ρ := by
    have heq : ((F.card:ℝ)+1)*ζ = ρ := mul_div_cancel₀ _ (by positivity)
    have hcard : Fintype.card F = F.card := Fintype.card_coe _
    rw [hcard]
    nlinarith only [heq,hζ.le]
  obtain ⟨T,hT4,hT⟩ := family_producers p h j F k hk hδ hδhi hρ hζ
  refine ⟨T,hT4,?_⟩
  intro N hN he i Δ V hb
  obtain ⟨hΔ,hR,hclass,htotal,hrect⟩ := hT N hN he i Δ V hb
  have hN2 : 2 ≤ N := by omega
  have hδhalf : δ < 1/2 := by linarith
  let W := convolutionWuWindows N Δ V
  let L := termLabels p j N δ W
  let P := fun r : F => packing N δ Δ V r.val
  let H := fun r : F => wuImprovementLimit true δ r.val.sample
  let J := fun r : F => rectIntegral r.val.A r.val.B r.val.C r.val.D
  let Θ := boxTheta N ((N:ℝ)^(1/2-δ)) W
  let M := gamma5ClassicalMainMass N δ W L
  let G := ∑ r : F, H r * J r
  have hs : ∀ r : F, P r ⊆ L := fun r => (hrect r).1.1
  have hd : Pairwise (fun r s : F => Disjoint (P r) (P s)) := by
    intro r s hrs
    apply packing_disjoint hR hΔ
    exact hF r.property s.property (fun heq => hrs (Subtype.ext heq))
  have hθ : 0 ≤ Θ := gamma5Mass_theta_nonneg hN2 hδ hδhalf hb
  have hupper := packing_finite_upper h j hN2 hδ hδhalf hb hρ.le P H hd hs
    (hclass _ sdiff_subset)
    (fun r => (hrect r).1.2)
  have hgain : (G-2*ρ)*Θ ≤ ∑ r : F, H r*gamma5ClassicalMainMass N δ W (P r) := by
    apply gamma5Gain_weighted_transport (H := H) (J := J)
      (m := fun r => gamma5ClassicalMainMass N δ W (P r)) (ρ := ρ) (G := G) hθ hζ.le
      (fun r => packing_sample_bounds r.val hδ hδhalf)
      (fun r => (hrect r).2) hζρ
    exact sub_le_self _ hρ.le
  have hmass : M ≤ (C+ρ)*Θ := by
    have hh := (abs_le.mp htotal).2
    change M-C*Θ ≤ ρ*Θ at hh
    linarith only [hh]
  have hmass' := mul_le_mul_of_nonneg_left hmass (sq_nonneg (1+ρ))
  have hbudget := mul_le_mul_of_nonneg_right
    (gamma5Gain_budget (G := G) hC hρ.le hρ1 hpay) hθ
  have hG : G = ∑ r ∈ F, wuImprovementLimit true δ r.sample * rectIntegral r.A r.B r.C r.D := by
    exact Finset.sum_coe_sort F (fun r => wuImprovementLimit true δ r.sample * rectIntegral r.A r.B r.C r.D)
  rw [← termCount_eq_original p h j hN2 hδ hδhalf hb, ← hG]
  change termCount p j N δ W L ≤ (C-G+ε)*Θ
  change termCount p j N δ W L ≤ (1+ρ)^2*M -
    (∑ r : F, H r*gamma5ClassicalMainMass N δ W (P r)) + ρ*Θ at hupper
  nlinarith only [hupper,hgain,hmass',hbudget]

end Wu2008DoubleSieve.MotherPair
