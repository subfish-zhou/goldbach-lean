import MathlibNt.Wu2008DoubleSieve.Gamma6GainSufficiency

/-!
# Full actual Gamma6 count with the full-rectangle H gain

All families, microcell admissions, mass transportation and thresholds
are produced internally. The complete original complement is retained.
-/

namespace Wu2008DoubleSieve

open Finset Real Filter MeasureTheory
open scoped Classical Topology Interval

theorem gamma6Gain_full_count_upper (k : ℕ) (hk : 1 ≤ k) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ i : ℕ, ∀ Δ : ℝ, ∀ V : Fin i → ℝ, wuSourceBox k δ N i Δ V →
      gamma5ClassicalCount N δ (convolutionWuWindows N Δ V)
        (gamma6BaseLabels N δ (convolutionWuWindows N Δ V)) ≤
      (gamma6BaseC6 - gamma6GainIntegral δ + ε) *
        boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  have hδhalf : δ < 1 / 2 := by linarith
  have hC : 0 ≤ gamma6BaseC6 := gamma6Base_C6_bounds.1
  let ρ := min 1 (ε / (16 * (gamma6BaseC6 + 1)))
  have hρ : 0 < ρ := lt_min (by norm_num) (div_pos hε (by positivity))
  have hρ1 : ρ ≤ 1 := min_le_left _ _
  have hρε : 16 * (gamma6BaseC6 + 1) * ρ ≤ ε := by
    have h := (le_div_iff₀ (by positivity : 0 < 16 * (gamma6BaseC6 + 1))).mp
      (min_le_right (1 : ℝ) (ε / (16 * (gamma6BaseC6 + 1))))
    simpa only [ρ, mul_comm] using h
  obtain ⟨n, hs⟩ := gamma6Gain_sufficient_family hδ hδhalf hρ
  let α := {j // j ∈ gamma6GainInner n}
  let r : α → Gamma6GainRectangle := gamma6GainInnerRectangle n
  let H : α → ℝ := fun j => wuImprovementLimit true δ (r j).s
  let J : α → ℝ := fun j => gamma6BaseIntegral (r j).A (r j).B (r j).C (r j).D
  let ζ := ρ / (Fintype.card α + 1 : ℕ)
  have hζ : 0 < ζ := div_pos hρ (by positivity)
  have hζρ : (Fintype.card α : ℝ) * ζ ≤ ρ := by
    have hmul : ((Fintype.card α + 1 : ℕ) : ℝ) * ζ = ρ := by
      dsimp [ζ]
      exact mul_div_cancel₀ _ (by positivity)
    have hm : (Fintype.card α : ℝ) ≤ ((Fintype.card α + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.le_succ _
    exact (mul_le_mul_of_nonneg_right hm hζ.le).trans_eq hmul
  have hH (j : α) : 0 ≤ H j ∧ H j ≤ 1 := by
    dsimp [H]
    rw [← gamma6Gain_rectangle_H δ (r j)]
    exact gamma5Gain_H_bounds hδ hδhalf _
  choose TP _hTP hp using (fun j : α => gamma6Gain_packing_actual k hδ hδhi hρ (r j))
  choose TM _hTM hm using (fun j : α => gamma6Gain_packing_mass k hk hδ hδhi hζ (r j))
  obtain ⟨TC, _hTC, hc⟩ := gamma6Base_mask_upper k hk hδ hδhi hρ hρ
  obtain ⟨TF, _hTF, hf⟩ := gamma6Base_full_mass k hk hδ hδhi hρ
  obtain ⟨TG, hg⟩ := eventually_atTop.mp
    (gamma5Gain_mesh_eventually k hδ hδhi (by norm_num : (0 : ℝ) < 1))
  refine ⟨4 + TC + TF + TG + (∑ j, TP j) + (∑ j, TM j), by omega, ?_⟩
  intro N hN he i Δ V hb
  have hN2 : 2 ≤ N := by omega
  have hNC : TC ≤ N := by omega
  have hNF : TF ≤ N := by omega
  have hNG : TG ≤ N := by omega
  have hNP (j : α) : TP j ≤ N := by
    have h := single_le_sum (fun l (_ : l ∈ (univ : Finset α)) => Nat.zero_le (TP l)) (mem_univ j)
    omega
  have hNM (j : α) : TM j ≤ N := by
    have h := single_le_sum (fun l (_ : l ∈ (univ : Finset α)) => Nat.zero_le (TM l)) (mem_univ j)
    omega
  let W := convolutionWuWindows N Δ V
  let L := gamma6BaseLabels N δ W
  let P : α → Finset Gamma5ClassicalLabel := fun j => gamma6GainPacking N δ Δ V (r j)
  let Θ := boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) W
  let m : α → ℝ := fun j => gamma5ClassicalMainMass N δ W (P j)
  have hP (j : α) := hp j N (hNP j) he i Δ V hb
  have hsub (j : α) : P j ⊆ L := (hP j).1
  have hmesh := hg N hNG i Δ V hb
  have hdis : Pairwise (fun j l => Disjoint (P j) (P l)) :=
    gamma6Gain_inner_packings_disjoint hmesh.2.1 hmesh.1
  have hΘ : 0 ≤ Θ := gamma5Mass_theta_nonneg hN2 hδ hδhalf hb
  have hm0 (j : α) : 0 ≤ m j := gamma6Gain_mass_nonneg hN2 hδ hδhalf hb (hsub j)
  have hcomp := hc N hNC he i Δ V hb (L \ univ.biUnion P) sdiff_subset
  have hcount := gamma5Gain_finite_upper hρ.le
    (gamma5Gain_count_partition N δ W L P hdis hsub)
    (gamma5Gain_main_mass_partition N δ W L P hdis hsub)
    hm0 hcomp (fun j => (hP j).2)
  have htransport : (gamma6GainIntegral δ - 2 * ρ) * Θ ≤ ∑ j, H j * m j :=
    gamma5Gain_weighted_transport hΘ hζ.le hH
      (fun j => hm j N (hNM j) i Δ V hb) hζρ hs.le
  have hmass : gamma5ClassicalMainMass N δ W L ≤ (gamma6BaseC6 + ρ) * Θ := by
    have hh := (le_abs_self _).trans (hf N hNF i Δ V hb)
    change gamma5ClassicalMainMass N δ W L - gamma6BaseC6 * Θ ≤ ρ * Θ at hh
    nlinarith
  have hpaid := mul_le_mul_of_nonneg_left hmass (sq_nonneg (1 + ρ))
  have hbudget := mul_le_mul_of_nonneg_right
    (gamma5Gain_budget (G := gamma6GainIntegral δ) hC hρ.le hρ1 hρε) hΘ
  change gamma5ClassicalCount N δ W L ≤ (gamma6BaseC6 - gamma6GainIntegral δ + ε) * Θ
  change gamma5ClassicalCount N δ W L ≤
    (1 + ρ) ^ 2 * gamma5ClassicalMainMass N δ W L - (∑ j, H j * m j) + ρ * Θ at hcount
  nlinarith

theorem gamma6Gain_integral_literal (δ : ℝ) :
    gamma6GainIntegral δ =
      ∫ t in (25 / 103 : ℝ)..(25 / 89), ∫ u in (100 / 291 : ℝ)..(2 / 5),
        wuImprovementLimit true δ ((103 / 25) * (1 - t - u)) / (t * u * (1 - t - u)) := by
  norm_num [gamma6GainIntegral, gamma6GainLiteral, gamma5GainV, gamma5ClassicalS,
    gamma5MassA, gamma6BaseB, gamma6BaseC, gamma6BaseF]

theorem gamma6Gain_full_count_literal (k : ℕ) (hk : 1 ≤ k) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ i : ℕ, ∀ Δ : ℝ, ∀ V : Fin i → ℝ, wuSourceBox k δ N i Δ V →
      gamma5ClassicalCount N δ (convolutionWuWindows N Δ V)
        (gamma6BaseLabels N δ (convolutionWuWindows N Δ V)) ≤
      (gamma6BaseC6 -
        (∫ t in (25 / 103 : ℝ)..(25 / 89), ∫ u in (100 / 291 : ℝ)..(2 / 5),
          wuImprovementLimit true δ ((103 / 25) * (1 - t - u)) / (t * u * (1 - t - u))) + ε) *
        boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  rw [← gamma6Gain_integral_literal]
  exact gamma6Gain_full_count_upper k hk hδ hδhi hε

end Wu2008DoubleSieve
