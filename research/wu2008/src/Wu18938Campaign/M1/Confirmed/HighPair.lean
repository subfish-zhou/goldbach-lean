import Wu18938Campaign.M1.Confirmed.PayloadNormalization
import Wu18938Campaign.M1.Confirmed.FiniteMother
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighUnitJDensity

noncomputable section

namespace Wu18938Campaign.M1.Confirmed

open Wu2008DoubleSieve HighNonunit HighSourcePayload Finset Real
open scoped Classical

theorem roughBox_high_pair_mass (m : ℕ) {η δ ρ ε : ℝ}
    (hη : 0 < η) (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hρ : 0 < ρ) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible → 2 ≤ p.s →
      secondFunctionalMotherGammaSum p N δ (convolutionWuWindows N Δ V) 20 +
        secondFunctionalMotherGammaSum p N δ (convolutionWuWindows N Δ V) 21 ≤
        mass N δ Δ V (fun d => paired N d δ p) *
          (((1 + ρ) * (1 + ρ * exp (-eulerMascheroniConstant)) * (8 / (1 - 2 * δ))) *
            wuSingularSeries N / log N) +
          ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  let A := (1 + ρ) * (1 + ρ * exp (-eulerMascheroniConstant)) * (8 / (1 - 2 * δ))
  have hD : 0 < 1 - 2 * δ := by linarith
  have hA : 0 < A := by dsimp [A]; positivity
  let τ := ε / (3 * A)
  have hτ : 0 < τ := by dsimp [τ]; positivity
  obtain ⟨T0, hT04, hgam⟩ := roughBox_gamma_buchstab m hη hδ hδhi hρ
    (show 0 < ε / 6 by positivity)
  obtain ⟨T1, _, hunit⟩ := roughBox_unit_pair_density m hη hδ hδhi hρ
    (show 0 < ε / 3 by positivity)
  obtain ⟨T2, _, hJ⟩ := roughBox_boxed_unit_integral m hη hδ hτ
  obtain ⟨T3, _, hK⟩ := roughBox_nonunit_integral m hη hδ hτ
  refine ⟨max T0 (max T1 (max T2 T3)), hT04.trans (le_max_left _ _), ?_⟩
  intro N hN heven i Δ V hb p hp hs
  let W := convolutionWuWindows N Δ V
  have hC : 0 ≤ wuSingularSeries N / log N := div_nonneg
    (wuSingularSeries_pos N (by omega)).le
    (log_pos (by exact_mod_cast (show 1 < N by omega))).le
  have hg0 := hgam N (by omega) heven i Δ V hb p hp hs false
  have hg1 := hgam N (by omega) heven i Δ V hb p hp hs true
  have hu := hunit N (by omega) heven i Δ V hb p hp hs
  have hj := (abs_le.mp (hJ N (by omega) i Δ V hb
    (fun _ => 1 / p.kappa2) (fun _ => 1 / p.kappa3) (fun _ => 1 / p.s)
    (fun _ _ => HighUnitSource.parameter_outer_bounds hp hs))).2
  have hk := hK N (by omega) i Δ V hb p hp hs
  rw [← unit_mass_eq_boxed] at hj
  have hj' := mul_le_mul_of_nonneg_right hj (mul_nonneg hA.le hC)
  have hk' := mul_le_mul_of_nonneg_right hk (mul_nonneg hA.le hC)
  have hnorm := mul_le_mul_of_nonneg_left
    (roughBox_reciprocal_theta hb (by omega) hη hδ) (show 0 ≤ ε / 3 by positivity)
  have hcancel : τ * ((N : ℝ) / log N) * boxConvolutionReciprocalMass W *
      (A * (wuSingularSeries N / log N)) =
      (ε / 3) * (wuSingularSeries N / log N * ((N : ℝ) / log N) *
        boxConvolutionReciprocalMass W) := by
    dsimp only [τ]
    field_simp
  have heq : mass N δ Δ V (fun d => paired N d δ p) =
      mass N δ Δ V (fun d => unitPair N d δ p) +
        mass N δ Δ V (fun d => sourceLegalK N d δ p false + sourceLegalK N d δ p true) := by
    simp only [mass, paired, mul_add, sum_add_distrib]
  simp only [add_mul] at hk'
  change _ ≤ _ + τ * ((N : ℝ) / log N) * boxConvolutionReciprocalMass W *
    (A * (wuSingularSeries N / log N)) at hk'
  rw [hcancel] at hk'
  have hj'' : (HighUnit.boxedSigma20 N δ W (fun _ => 1 / p.kappa2)
        (fun _ => 1 / p.kappa3) (fun _ => 1 / p.s) +
      HighUnit.boxedSigma21 N δ W (fun _ => 1 / p.kappa3) (fun _ => 1 / p.s)) *
      (A * (wuSingularSeries N / log N)) ≤
      mass N δ Δ V (fun d => unitPair N d δ p) * (A * (wuSingularSeries N / log N)) +
      (ε / 3) * (wuSingularSeries N / log N * ((N : ℝ) / log N) *
        boxConvolutionReciprocalMass W) := by
    rw [← hcancel]
    nlinarith only [hj']
  simp only [Bool.false_eq_true, ↓reduceIte] at hg0 hg1
  change _ ≤ _ + _ * (A * wuSingularSeries N / log N) + _ at hg0 hg1
  change _ ≤ _ * (A * wuSingularSeries N / log N) + _ at hu ⊢
  rw [mul_div_assoc] at hg0 hg1 hu ⊢
  rw [heq, add_mul]
  dsimp only [W] at *
  linarith only [hg0, hg1, hu, hj'', hk', hnorm]

theorem roughBox_high_pair_theta (m : ℕ) {η δ ε : ℝ}
    (hη : 0 < η) (hδ : 0 < δ) (hδhi : δ < 1 / 2) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible → 2 ≤ p.s →
      secondFunctionalMotherGammaSum p N δ (convolutionWuWindows N Δ V) 20 +
        secondFunctionalMotherGammaSum p N δ (convolutionWuWindows N Δ V) 21 ≤
        (2 / (1 - 2 * δ)) * pairedTheta N δ Δ V p +
          ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨ρ, hρ, T0, hT04, hnorm⟩ := roughBox_payload_density_slack m hη hδ hδhi
    (show 0 ≤ 2000 + sourceKCap by have := sourceKCap_pos; positivity) (half_pos he)
  obtain ⟨T1, _, hsource⟩ := roughBox_high_pair_mass m hη hδ hδhi hρ (half_pos he)
  refine ⟨max T0 T1, hT04.trans (le_max_left _ _), ?_⟩
  intro N hN heven i Δ V hb p hp hs
  have hn := hnorm N (by omega) i Δ V hb (fun d => paired N d δ p) (by
    intro d _
    have hu := unitPair_bounds N d δ hp hs
    have hk := sourceLegalK_pair_bounds N d δ hp hs
    exact ⟨add_nonneg hu.1 hk.1, add_le_add hu.2 hk.2⟩)
  have hc := hsource N (by omega) heven i Δ V hb p hp hs
  change _ ≤ _ * pairedTheta N δ Δ V p + _ at hn
  rw [mul_div_assoc] at hc
  nlinarith only [hc, hn]

theorem roughBox_mother_high_paid (m : ℕ) {η δ ε : ℝ}
    (hη : 0 < η) (hδ : 0 < δ) (hδhi : δ < 1 / 2) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible → 2 ≤ p.s →
      5 * wuBoxPhi N δ (convolutionWuWindows N Δ V) p.s ≤
        4 * wuBoxPhi N δ (convolutionWuWindows N Δ V) p.S +
          wuBoxPhi N δ (convolutionWuWindows N Δ V) p.kappa1 -
          wuOmega2Sum N δ p.s p.S (convolutionWuWindows N Δ V) -
          wuOmega2Sum N δ p.kappa2 p.S (convolutionWuWindows N Δ V) -
          wuOmega2Sum N δ p.kappa3 p.S (convolutionWuWindows N Δ V) +
          (∑ j ∈ Icc 5 19, secondFunctionalMotherGammaSum p N δ (convolutionWuWindows N Δ V) j) +
          (2 / (1 - 2 * δ)) * pairedTheta N δ Δ V p +
          ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨T0, hT04, hmother⟩ := roughBox_mother_source m hη hδ (half_pos he)
  obtain ⟨T1, _, hhigh⟩ := roughBox_high_pair_theta m hη hδ hδhi (half_pos he)
  refine ⟨max T0 T1, hT04.trans (le_max_left _ _), ?_⟩
  intro N hN heven i Δ V hb p hp hs
  have hm := hmother N (by omega) heven i Δ V hb p hp
  have hh := hhigh N (by omega) heven i Δ V hb p hp hs
  unfold secondFunctionalMotherRHS at hm
  rw [sum_Icc_succ_top (a := 5) (b := 20) (by omega),
    sum_Icc_succ_top (a := 5) (b := 19) (by omega)] at hm
  norm_num only [Nat.reduceAdd] at hm
  linarith only [hm, hh]

end Wu18938Campaign.M1.Confirmed
