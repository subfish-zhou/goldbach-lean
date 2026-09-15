import MathlibNt.Wu2008DoubleSieve.FourthRowTripleGatedNormalization
import MathlibNt.Wu2008DoubleSieve.FourthRowTripleGatedSieve

/-! # Actual Gamma10 and Gamma13 with the unchanged fixed-delta coefficient -/

namespace Wu2008DoubleSieve

open Finset Real Filter Set
open scoped Classical Topology

theorem fourthRowTripleGated_prefix_upper (k : ℕ) (ten : Bool) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
        fourthRowMotherPrefixSum N δ (convolutionWuWindows N Δ V) (fourthRowTripleGatedWord ten) ≤
          (2 / (1 - 2 * δ) * fourthRowTripleGatedEnvelope ten + ε) *
            boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  let f : ℝ → ℝ := fun ρ =>
    (1 + ρ) * ((1 + ρ) * (1 + ρ * exp (-eulerMascheroniConstant)) *
      (8 / (1 - 2 * δ))) / 4 * fourthRowTripleGatedEnvelope ten
  have hf : ContinuousAt f 0 := by dsimp [f]; fun_prop
  have hf0 : f 0 = 2 / (1 - 2 * δ) * fourthRowTripleGatedEnvelope ten := by dsimp [f]; ring
  have hlim := hf.tendsto.mono_left (nhdsWithin_le_nhds :
    𝓝[>] (0 : ℝ) ≤ 𝓝 0)
  rw [hf0] at hlim
  have hsmall := hlim.eventually (gt_mem_nhds
    (show 2 / (1 - 2 * δ) * fourthRowTripleGatedEnvelope ten <
      2 / (1 - 2 * δ) * fourthRowTripleGatedEnvelope ten + ε / 3 by linarith))
  have hpos : ∀ᶠ ρ : ℝ in 𝓝[>] (0 : ℝ), 0 < ρ := self_mem_nhdsWithin
  obtain ⟨ρ, hρ, hslack⟩ := (hpos.and hsmall).exists
  let K := (1 + ρ) * (1 + ρ * exp (-eulerMascheroniConstant)) * (8 / (1 - 2 * δ))
  have hK : 0 < K := omega3X_fixed_density_factor_pos hδhi hρ
  have hε3 : 0 < ε / 3 := by positivity
  have he : 0 < 2 * ε / (3 * K) := by positivity
  obtain ⟨TS, hTS4, hTS⟩ := fourthRowTripleGated_upper_density k hδ hδhi hρ hε3
  obtain ⟨TX, _, hTX⟩ := fourthRowTripleGated_X_scaled k hδ hδhi hK.le hρ he
  refine ⟨max TS TX, hTS4.trans (le_max_left _ _), ?_⟩
  intro N hN hEven i Δ V hb
  have hN4 : 4 ≤ N := hTS4.trans ((le_max_left _ _).trans hN)
  have hs := hTS N ((le_max_left _ _).trans hN) hEven i Δ V hb ten
  have hx := hTX N ((le_max_right _ _).trans hN) i Δ V hb ten
  have hC := (wuSingularSeries_pos N (by omega)).le
  have hmass : 0 ≤ boxConvolutionReciprocalMass (convolutionWuWindows N Δ V) :=
    sum_nonneg fun _ _ => by positivity
  have hθ : 0 ≤ boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) :=
    (show 0 ≤ 2 * wuSingularSeries N * (N : ℝ) / log N ^ 2 *
      boxConvolutionReciprocalMass (convolutionWuWindows N Δ V) by positivity).trans
      (omega3_source_theta_lower_singular hN4 hδ hδhi hb)
  have hepaid : (2 * ε / (3 * K)) * K / 2 = ε / 3 := by field_simp
  dsimp only at hs hx
  rw [hepaid] at hx
  have hcoef := mul_le_mul_of_nonneg_right hslack.le hθ
  change f ρ * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) ≤ _ at hcoef
  dsimp only [f, K] at hx hcoef
  linarith only [hs, hx, hcoef, mul_nonneg hε.le hθ]

theorem fourthRowTripleGated_gamma10_upper (k : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
        fourthRowMotherPrefixSum N δ (convolutionWuWindows N Δ V) [1, 1, 2] ≤
          (2 / (1 - 2 * δ) * fourthRowTripleGatedEnvelope true + ε) *
            boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) :=
  fourthRowTripleGated_prefix_upper k true hδ hδhi hε

theorem fourthRowTripleGated_gamma13_upper (k : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
        fourthRowMotherPrefixSum N δ (convolutionWuWindows N Δ V) [0, 1, 2] ≤
          (2 / (1 - 2 * δ) * fourthRowTripleGatedEnvelope false + ε) *
            boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) :=
  fourthRowTripleGated_prefix_upper k false hδ hδhi hε

theorem fourthRowTripleGated_natural_card_upper (k : ℕ) (ten : Bool) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
        (Nat.card {a // a ∈ fourthRowTripleGatedOriginalLabels N δ
          (convolutionWuWindows N Δ V) ten} : ℝ) ≤
          (2 / (1 - 2 * δ) * fourthRowTripleGatedEnvelope ten + ε) *
            boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨T, hT4, hT⟩ := fourthRowTripleGated_prefix_upper k ten hδ hδhi hε
  refine ⟨T, hT4, ?_⟩
  intro N hN he i Δ V hb
  rw [fourthRowTripleGated_natural_card]
  exact hT N hN he i Δ V hb

theorem fourthRowTripleGated_joint_upper (k : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
        fourthRowMotherPrefixSum N δ (convolutionWuWindows N Δ V) [1, 1, 2] +
          fourthRowMotherPrefixSum N δ (convolutionWuWindows N Δ V) [0, 1, 2] ≤
          (2 / (1 - 2 * δ) *
            (fourthRowTripleGatedEnvelope true + fourthRowTripleGatedEnvelope false) + ε) *
            boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨T1, hT1, h10⟩ := fourthRowTripleGated_gamma10_upper k hδ hδhi (half_pos hε)
  obtain ⟨T2, _, h13⟩ := fourthRowTripleGated_gamma13_upper k hδ hδhi (half_pos hε)
  refine ⟨max T1 T2, hT1.trans (le_max_left _ _), ?_⟩
  intro N hN he i Δ V hb
  have hh := add_le_add (h10 N ((le_max_left _ _).trans hN) he i Δ V hb)
    (h13 N ((le_max_right _ _).trans hN) he i Δ V hb)
  exact hh.trans_eq (by ring)

end Wu2008DoubleSieve
