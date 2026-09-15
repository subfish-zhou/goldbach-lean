import MathlibNt.Wu2008DoubleSieve.Gamma78GainSufficiency
import MathlibNt.Wu2008DoubleSieve.Gamma78GainMass

namespace Wu2008DoubleSieve

open Finset Real Filter MeasureTheory
open scoped Classical Topology Interval

theorem gamma78Gain_denominator_pos {tri : Bool} {t u : ℝ}
    (hv : (t,u) ∈ gamma78GainRegion tri) : 0 < t*u*(1-t-u) :=
  (gamma5Gain_triangle_bounds (gamma78Gain_region_bounds hv).1).2.2.2.2

/-- The full actual source count, with selected-prime cutoff and an internally
constructed full-domain family, on every original source box. -/
theorem gamma78Gain_full_count_upper (tri : Bool) (k : ℕ) (hk : 1 ≤ k) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1/10) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ i : ℕ, ∀ Δ : ℝ, ∀ V : Fin i → ℝ, wuSourceBox k δ N i Δ V →
      gamma78GainCount N (convolutionWuWindows N Δ V)
        (gamma78GainLabels tri N δ (convolutionWuWindows N Δ V)) ≤
      (gamma78GainC tri - gamma78GainIntegral tri δ + ε) *
        boxTheta N ((N : ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) := by
  have hδhalf : δ < 1/2 := by linarith
  have hC : 0 ≤ gamma78GainC tri :=
    (gamma78Gain_integral_bounds tri hδ hδhalf).1.trans (gamma78Gain_integral_bounds tri hδ hδhalf).2
  let ρ := min 1 (ε/(16*(gamma78GainC tri+1)))
  have hρ : 0 < ρ := lt_min (by norm_num) (div_pos hε (by positivity))
  have hρ1 : ρ ≤ 1 := min_le_left _ _
  have hρε : 16*(gamma78GainC tri+1)*ρ ≤ ε := by
    have h := (le_div_iff₀ (by positivity : 0 < 16*(gamma78GainC tri+1))).mp
      (min_le_right (1 : ℝ) (ε/(16*(gamma78GainC tri+1))))
    simpa only [ρ,mul_comm] using h
  obtain ⟨n,hs⟩ := gamma78Gain_sufficient_family tri hδ hδhalf hρ
  let α := {j // j ∈ gamma78GainInner tri n}
  let r : α → Gamma78GainRectangle tri := gamma78GainInnerRectangle tri n
  let H : α → ℝ := fun j => wuImprovementLimit true δ (r j).s
  let J : α → ℝ := fun j => gamma5MassRectangleIntegral (r j).box.A (r j).box.B (r j).box.C (r j).box.D
  let ζ := ρ/(Fintype.card α+1 : ℕ)
  have hζ : 0 < ζ := div_pos hρ (by positivity)
  have hζρ : (Fintype.card α : ℝ)*ζ ≤ ρ := by
    have hmul : ((Fintype.card α+1 : ℕ) : ℝ)*ζ=ρ := by
      dsimp [ζ]
      exact mul_div_cancel₀ _ (by positivity)
    have hm : (Fintype.card α : ℝ) ≤ ((Fintype.card α+1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ _
    exact (mul_le_mul_of_nonneg_right hm hζ.le).trans_eq hmul
  have hH (j : α) : 0 ≤ H j ∧ H j ≤ 1 := by
    dsimp [H]
    rw [← gamma78Gain_rectangle_H δ (r j)]
    exact gamma5Gain_H_bounds hδ hδhalf _
  choose TP _hTP hp using (fun j : α => gamma78Gain_packing_actual k hδ hδhi hρ (r j))
  choose TM _hTM hm using (fun j : α => gamma5Gain_packing_mass k hk hδ hδhi hζ (r j).box)
  obtain ⟨TC,_hTC,hc⟩ := gamma5Classical_mask_upper k hk hδ hδhi hρ hρ
  obtain ⟨TF,_hTF,hf⟩ := gamma78Gain_full_mass_upper tri k hk hδ hδhi hρ
  obtain ⟨TG,hg⟩ := eventually_atTop.mp
    (gamma5Gain_mesh_eventually k hδ hδhi (by norm_num : (0 : ℝ) < 1))
  refine ⟨4+TC+TF+TG+(∑ j,TP j)+(∑ j,TM j),by omega,?_⟩
  intro N hN he i Δ V hb
  have hN2 : 2 ≤ N := by omega
  have hNC : TC ≤ N := by omega
  have hNF : TF ≤ N := by omega
  have hNG : TG ≤ N := by omega
  have hNP (j : α) : TP j ≤ N := by
    have hh := single_le_sum (fun l (_ : l ∈ (univ : Finset α)) => Nat.zero_le (TP l)) (mem_univ j)
    omega
  have hNM (j : α) : TM j ≤ N := by
    have hh := single_le_sum (fun l (_ : l ∈ (univ : Finset α)) => Nat.zero_le (TM l)) (mem_univ j)
    omega
  let W := convolutionWuWindows N Δ V
  let L := gamma78GainLabels tri N δ W
  let P : α → Finset Gamma5ClassicalLabel := fun j => gamma5GainPacking N δ Δ V (r j).box
  let Θ := boxTheta N ((N : ℝ)^(1/2-δ)) W
  let m : α → ℝ := fun j => gamma5ClassicalMainMass N δ W (P j)
  have hP (j : α) := hp j N (hNP j) he i Δ V hb
  have hsub (j : α) : P j ⊆ L := (hP j).1
  have hL : L ⊆ gamma5ClassicalLabels N δ W := filter_subset _ _
  have hmesh := hg N hNG i Δ V hb
  have hdis : Pairwise (fun j l => Disjoint (P j) (P l)) :=
    gamma78Gain_inner_packings_disjoint hmesh.2.1 hmesh.1
  have hΘ : 0 ≤ Θ := gamma5Mass_theta_nonneg hN2 hδ hδhalf hb
  have hm0 (j : α) : 0 ≤ m j := gamma5Gain_mass_nonneg hN2 hδ hδhalf hb ((hsub j).trans hL)
  have hcomp := (gamma78Gain_count_le_classical (sdiff_subset.trans hL)).trans
    (hc N hNC he i Δ V hb (L \ univ.biUnion P) (sdiff_subset.trans hL))
  have hcount := gamma5Gain_finite_upper hρ.le
    (gamma78Gain_count_partition N W L P hdis hsub)
    (gamma5Gain_main_mass_partition N δ W L P hdis hsub)
    hm0 hcomp (fun j => (hP j).2)
  have htransport : (gamma78GainIntegral tri δ-2*ρ)*Θ ≤ ∑ j,H j*m j :=
    gamma5Gain_weighted_transport hΘ hζ.le hH
      (fun j => hm j N (hNM j) i Δ V hb) hζρ hs.le
  have hmass : gamma5ClassicalMainMass N δ W L ≤ (gamma78GainC tri+ρ)*Θ := hf N hNF i Δ V hb
  have hpaid := mul_le_mul_of_nonneg_left hmass (sq_nonneg (1+ρ))
  have hbudget := mul_le_mul_of_nonneg_right
    (gamma5Gain_budget (G := gamma78GainIntegral tri δ) hC hρ.le hρ1 hρε) hΘ
  change gamma78GainCount N W L ≤ (gamma78GainC tri-gamma78GainIntegral tri δ+ε)*Θ
  change gamma78GainCount N W L ≤
    (1+ρ)^2*gamma5ClassicalMainMass N δ W L-(∑ j,H j*m j)+ρ*Θ at hcount
  nlinarith

theorem gamma78Gain_C7_literal :
    gamma78GainC true = ∫ t in (25/103 : ℝ)..(25/89),
      ∫ u in t..(25/89), 1/(t*u*(1-t-u)) := by
  norm_num [gamma78GainC,gamma78GainStart,gamma78GainUpper,gamma5MassKernel,
    gamma5MassA,gamma5ClassicalS,gamma6BaseB]

theorem gamma78Gain_C8_literal :
    gamma78GainC false = ∫ t in (25/103 : ℝ)..(25/89),
      ∫ u in (25/89 : ℝ)..(100/291), 1/(t*u*(1-t-u)) := by
  norm_num [gamma78GainC,gamma78GainStart,gamma78GainUpper,gamma5MassKernel,
    gamma5MassA,gamma5ClassicalS,gamma6BaseB,gamma5ClassicalB]

theorem gamma78Gain_G7_literal (δ : ℝ) :
    gamma78GainIntegral true δ = ∫ t in (25/103 : ℝ)..(25/89),
      ∫ u in t..(25/89), wuImprovementLimit true δ ((1-t-u)/t)/(t*u*(1-t-u)) := by
  norm_num [gamma78GainIntegral,gamma78GainLiteral,gamma78GainStart,gamma78GainUpper,
    gamma78GainV,gamma5MassA,gamma5ClassicalS,gamma6BaseB]

theorem gamma78Gain_G8_literal (δ : ℝ) :
    gamma78GainIntegral false δ = ∫ t in (25/103 : ℝ)..(25/89),
      ∫ u in (25/89 : ℝ)..(100/291), wuImprovementLimit true δ ((1-t-u)/t)/(t*u*(1-t-u)) := by
  norm_num [gamma78GainIntegral,gamma78GainLiteral,gamma78GainStart,gamma78GainUpper,
    gamma78GainV,gamma5MassA,gamma5ClassicalS,gamma6BaseB,gamma5ClassicalB]

theorem gamma78Gain_gamma7_full_count_upper (k : ℕ) (hk : 1 ≤ k) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1/10) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ i : ℕ, ∀ Δ : ℝ, ∀ V : Fin i → ℝ, wuSourceBox k δ N i Δ V →
      gamma78GainCount N (convolutionWuWindows N Δ V)
        (gamma78GainLabels true N δ (convolutionWuWindows N Δ V)) ≤
      ((∫ t in (25/103 : ℝ)..(25/89), ∫ u in t..(25/89), 1/(t*u*(1-t-u))) -
        (∫ t in (25/103 : ℝ)..(25/89), ∫ u in t..(25/89),
          wuImprovementLimit true δ ((1-t-u)/t)/(t*u*(1-t-u))) + ε) *
        boxTheta N ((N : ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) := by
  rw [← gamma78Gain_C7_literal,← gamma78Gain_G7_literal]
  exact gamma78Gain_full_count_upper true k hk hδ hδhi hε

theorem gamma78Gain_gamma8_full_count_upper (k : ℕ) (hk : 1 ≤ k) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1/10) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ i : ℕ, ∀ Δ : ℝ, ∀ V : Fin i → ℝ, wuSourceBox k δ N i Δ V →
      gamma78GainCount N (convolutionWuWindows N Δ V)
        (gamma78GainLabels false N δ (convolutionWuWindows N Δ V)) ≤
      ((∫ t in (25/103 : ℝ)..(25/89), ∫ u in (25/89 : ℝ)..(100/291), 1/(t*u*(1-t-u))) -
        (∫ t in (25/103 : ℝ)..(25/89), ∫ u in (25/89 : ℝ)..(100/291),
          wuImprovementLimit true δ ((1-t-u)/t)/(t*u*(1-t-u))) + ε) *
        boxTheta N ((N : ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) := by
  rw [← gamma78Gain_C8_literal,← gamma78Gain_G8_literal]
  exact gamma78Gain_full_count_upper false k hk hδ hδhi hε

/-- The two full source counts share one total epsilon and one threshold. -/
theorem gamma78Gain_joint_full_count_upper (k : ℕ) (hk : 1 ≤ k) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1/10) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ i : ℕ, ∀ Δ : ℝ, ∀ V : Fin i → ℝ, wuSourceBox k δ N i Δ V →
      gamma78GainCount N (convolutionWuWindows N Δ V)
          (gamma78GainLabels true N δ (convolutionWuWindows N Δ V)) +
        gamma78GainCount N (convolutionWuWindows N Δ V)
          (gamma78GainLabels false N δ (convolutionWuWindows N Δ V)) ≤
      (gamma78GainC true+gamma78GainC false -
        gamma78GainIntegral true δ-gamma78GainIntegral false δ+ε) *
        boxTheta N ((N : ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨T7,hT7,h7⟩ := gamma78Gain_full_count_upper true k hk hδ hδhi (half_pos hε)
  obtain ⟨T8,_hT8,h8⟩ := gamma78Gain_full_count_upper false k hk hδ hδhi (half_pos hε)
  refine ⟨max T7 T8,hT7.trans (le_max_left _ _),?_⟩
  intro N hN he i Δ V hb
  have hh := add_le_add
    (h7 N ((le_max_left _ _).trans hN) he i Δ V hb)
    (h8 N ((le_max_right _ _).trans hN) he i Δ V hb)
  nlinarith

end Wu2008DoubleSieve
