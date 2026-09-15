import MathlibNt.Wu2008DoubleSieve.Gamma16Distribution
import MathlibNt.Wu2008DoubleSieve.Gamma16MissingMass
import MathlibNt.Wu2008DoubleSieve.Gamma16SwitchingPayment
import MathlibNt.Wu2008DoubleSieve.Omega3SourceDensity
import MathlibNt.Wu2008DoubleSieve.Omega3R2Source

/-! # Actual Gamma16 upper sieve with all additive errors paid -/

namespace Wu2008DoubleSieve

open Finset Real Filter
open scoped Classical Topology
open MathlibNt.SieveTheory.SwitchingPrinciple

theorem gamma16_R2_relative (k : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      let W := convolutionWuWindows N Δ V
      let Q := (N : ℝ) ^ (1 / 2 - δ)
      gamma16FamilyR2 N (⌊Q⌋₊ + 1) δ (sqrt Q) W (gamma16EncodedProfiles N δ W) ≤
        ε * boxTheta N Q W := by
  let η := wuLocalExponent k δ / 10
  let F := gamma16FibreConstant k δ
  have hη : 0 < η := div_pos (wuLocalExponent_pos k hδ hδhi) (by norm_num)
  have hF : 0 < F := by
    dsimp [F, gamma16FibreConstant]
    exact pow_pos (zero_lt_one.trans_le (le_max_left _ _)) _
  obtain ⟨C, hC, heuler⟩ := gamma16_family_R2_euler
  obtain ⟨T1, hT1, hdata⟩ := gamma16_source_layers k hδ hδhi
  obtain ⟨T2, _, hp⟩ := omega3_absolute_power_log_relative k 5 hδ hδhi hε
    (show 0 < 2 * C * F / log 2 by positivity) hη
  obtain ⟨T3, hl⟩ := eventually_atTop.mp
    ((tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (1 : ℝ)))
  refine ⟨max T1 (max T2 T3), hT1.trans (le_max_left _ _), ?_⟩
  intro N hN i Δ V hb W Q
  have hN1 := (le_max_left T1 _).trans hN
  have hN2 := (le_max_left T2 _).trans ((le_max_right T1 _).trans hN)
  have hN3 := (le_max_right T2 _).trans ((le_max_right T1 _).trans hN)
  have hN4 := hT1.trans hN1
  obtain ⟨hw, _, _, hrough⟩ := hdata N hN1 i Δ V hb
  have hgeom := omega3_source_sieve_geometry (show 2 ≤ N by omega) hδ hδhi
  have hqN : ∀ q ∈ omega3SieveModuli N (⌊Q⌋₊ + 1) (sqrt Q), q ≤ N := by
    intro q hq
    have hqd := (omega3SieveModuli_properties hq).2.2.2
    have hDN := hgeom.2.2.2.2.2.2.1
    dsimp only [Q] at hqd
    omega
  have h := heuler N (by omega) i δ (sqrt Q) ((N : ℝ) ^ η) F W
    (gamma16EncodedProfiles N δ W) (⌊Q⌋₊ + 1) hgeom.2.2.2.1
    (rpow_pos_of_pos (by positivity) _) hF.le hqN (fun c hc => by
      have hg := gamma16_encoded_geometry (show 2 ≤ N by omega) hδ hδhi hb hc
      exact ⟨hg.1, hg.2.1, hrough c hc⟩) hw
  have hlog1 : 1 ≤ log (N : ℝ) := hl N hN3
  calc
    _ ≤ C * F * N * ((1 + log N) * log N ^ 4 / ((N : ℝ) ^ η * log 2)) := h
    _ ≤ C * F * N * ((2 * log N) * log N ^ 4 / ((N : ℝ) ^ η * log 2)) := by
      gcongr
      linarith
    _ = (2 * C * F / log 2) * N * log N ^ 5 / (N : ℝ) ^ η := by ring
    _ ≤ _ := hp N hN2 i Δ V hb

theorem gamma16_prefix_upper_density (k : ℕ) {δ ρ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hρ : 0 < ρ) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      let W := convolutionWuWindows N Δ V
      gamma16PrefixSum N δ W ≤
        gamma16X N δ W * (((1 + ρ) * (1 + ρ * exp (-eulerMascheroniConstant)) *
          (8 / (1 - 2 * δ))) * wuSingularSeries N / log N) +
        ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) W := by
  have hε3 : 0 < ε / 3 := by positivity
  obtain ⟨T0, hT0, hs⟩ := gamma16_prefix_switching_paid k hδ hδhi hε3
  obtain ⟨T1, _, hR1⟩ := gamma16_R1_relative k hδ hδhi hε3
  obtain ⟨T2, _, hR2⟩ := gamma16_R2_relative k hδ hδhi hε3
  obtain ⟨T3, _, hden⟩ := omega3_source_rosser_density hδ hδhi hρ
  refine ⟨max T0 (max T1 (max T2 T3)), hT0.trans (le_max_left _ _), ?_⟩
  intro N hN he i Δ V hb W
  have hN0 := (le_max_left T0 _).trans hN
  have hN1 := (le_max_left T1 _).trans ((le_max_right T0 _).trans hN)
  have hN2 := (le_max_left T2 _).trans ((le_max_right T1 _).trans ((le_max_right T0 _).trans hN))
  have hN3 := (le_max_right T2 _).trans ((le_max_right T1 _).trans ((le_max_right T0 _).trans hN))
  have hN4 := hT0.trans hN0
  have hg := omega3_source_sieve_geometry (show 2 ≤ N by omega) hδ hδhi
  let Q := (N : ℝ) ^ (1 / 2 - δ)
  have hD : 1 < ⌊Q⌋₊ + 1 := hg.2.2.2.2.1
  have hZ : sqrt Q ≤ (⌊Q⌋₊ + 1 : ℕ) := hg.2.2.2.2.2.1
  have hf := gamma16_family_upper_finite he δ (sqrt Q) W
    (gamma16EncodedProfiles N δ W) hD hZ
  rw [(gamma16_actual_family N δ (sqrt Q) W).1,
    (gamma16_actual_family N δ (sqrt Q) W).2] at hf
  have hx : 0 ≤ gamma16X N δ W :=
    sum_nonneg fun _ _ => mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hmain := mul_le_mul_of_nonneg_left (hden N hN3 he) hx
  have hsw := hs N hN0 he i Δ V hb
  have hr1 := hR1 N hN1 i Δ V hb
  have hr2 := hR2 N hN2 i Δ V hb
  dsimp only at hr1 hr2
  dsimp only [Q, W] at hf hmain hsw ⊢
  linarith

end Wu2008DoubleSieve
