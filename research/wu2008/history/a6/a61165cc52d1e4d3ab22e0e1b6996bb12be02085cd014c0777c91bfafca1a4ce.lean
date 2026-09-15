import MathlibNt.Wu2008DoubleSieve.FourthRowTripleNoGateLayers
import MathlibNt.Wu2008DoubleSieve.Omega3R2Source
import MathlibNt.Wu2008DoubleSieve.Omega3NonCoprimeRelative

/-! # Actual filtered signed residuals, using the existing balanced distribution -/

namespace Wu2008DoubleSieve

open Finset Real Filter
open scoped Classical Topology

theorem fourthRowTripleNoGate_R1_log (k : ℕ) {δ A : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ eleven : Bool,
      let W := convolutionWuWindows N Δ V
      let Q := (N : ℝ) ^ (1 / 2 - δ)
      gamma16FamilyR1 N (⌊Q⌋₊ + 1) δ (sqrt Q) W (fourthRowTripleNoGateProfiles N δ W eleven) ≤
        C * N / log (N : ℝ) ^ A := by
  have hη := div_pos (wuLocalExponent_pos k hδ hδhi) (by norm_num : (0 : ℝ) < 10)
  obtain ⟨C, hC, T1, hT1, hdist⟩ := omega3_balanced_interval_distribution A
    (wuLocalExponent k δ / 10) (omega3LayerConstant k δ) hA hη
    (omega3LayerConstant_pos k δ).le hδ
  obtain ⟨T2, _, hlayers⟩ := fourthRowTripleNoGate_layers k hδ hδhi
  refine ⟨((omega3LayerCount k δ : ℝ) + 1) * C, by positivity,
    max T1 T2, hT1.trans (le_max_left _ _), ?_⟩
  intro N hN i Δ V hb eleven W Q
  have hN1 := (le_max_left T1 T2).trans hN
  have hN2 := (le_max_right T1 T2).trans hN
  have hN4 := hT1.trans hN1
  let L := fourthRowTripleNoGateProfiles N δ W eleven
  obtain ⟨_, hcard, hcoeff⟩ := hlayers N hN2 i Δ V hb eleven
  have hg := fun c hc => fourthRowTripleNoGate_geometry (by omega : 2 ≤ N)
    hδ hδhi hb (c := c) (eleven := eleven) hc
  have hj (j : ℕ) :
      (∑ q ∈ omega3SieveModuli N (⌊Q⌋₊ + 1) (sqrt Q), (3 : ℝ) ^ q.primeFactors.card *
        |∑ e ∈ (omega3LayerSupport L j).filter (fun e => e.Coprime q),
          omega3LayerCoefficient W L j e * omega3ProfileError N q e
            (omega3LayerLower L j e) (omega3LayerUpper N δ (5 / 2) L j e)|) ≤
        C * N / log (N : ℝ) ^ A := by
    apply hdist N hN1 (omega3LayerSupport L j) (omega3LayerCoefficient W L j)
      (omega3LayerLower L j) (omega3LayerUpper N δ (5 / 2) L j)
    · intro e he
      have hm := omega3LayerLabel_mem he
      have h := hg _ hm.1
      exact ⟨hm.2 ▸ h.2.2.1, hm.2 ▸ h.2.2.2.1⟩
    · intro e _
      rw [abs_of_nonneg (hcoeff j e).1]
      exact (hcoeff j e).2
    · intro e he
      have hm := omega3LayerLabel_mem he
      have h := hg _ hm.1
      refine ⟨by unfold omega3LayerLower; exact_mod_cast h.2.2.2.2.1, ?_, ?_⟩
      · simpa only [omega3LayerLower, omega3LayerUpper, hm.2] using h.2.2.2.2.2.1
      · simpa only [omega3LayerUpper, hm.2] using h.2.2.2.2.2.2
  have hf := gamma16_family_R1_le_layers (N := N) (D := ⌊Q⌋₊ + 1) (δ := δ)
    (Z := sqrt Q) W L hcard (fun c hc => (hg c hc).1)
  have hs := hf.trans (sum_le_sum fun j _ => hj j)
  simp only [sum_const, card_range, nsmul_eq_mul] at hs
  exact hs.trans (by
    have hlog := log_pos (by exact_mod_cast (show 1 < N by omega) : (1 : ℝ) < N)
    have hh : (omega3LayerCount k δ : ℝ) ≤ (omega3LayerCount k δ : ℝ) + 1 := by linarith
    exact (mul_le_mul_of_nonneg_right hh (by positivity :
      0 ≤ C * N / log (N : ℝ) ^ A)).trans_eq (by ring))

theorem fourthRowTripleNoGate_R1_relative (k : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ eleven : Bool,
      let W := convolutionWuWindows N Δ V
      let Q := (N : ℝ) ^ (1 / 2 - δ)
      gamma16FamilyR1 N (⌊Q⌋₊ + 1) δ (sqrt Q) W (fourthRowTripleNoGateProfiles N δ W eleven) ≤
        ε * boxTheta N Q W := by
  obtain ⟨C, hC, T1, hT1, hR⟩ := fourthRowTripleNoGate_R1_log k hδ hδhi
    (show (0 : ℝ) < (5 * k + 3 : ℕ) by positivity)
  obtain ⟨c, hc, T2, hTheta⟩ := wu_boxTheta_lower k hδ hδhi
  obtain ⟨T3, hlogT⟩ := eventually_atTop.mp
    ((tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (C / (ε * c))))
  refine ⟨max T1 (max T2 T3), hT1.trans (le_max_left _ _), ?_⟩
  intro N hN i Δ V hb eleven W Q
  have hN1 := (le_max_left T1 _).trans hN
  have hN2 := (le_max_left T2 _).trans ((le_max_right T1 _).trans hN)
  have hN3 := (le_max_right T2 _).trans ((le_max_right T1 _).trans hN)
  have hlog := log_pos (by exact_mod_cast (show 1 < N by have := hT1.trans hN1; omega) : (1 : ℝ) < N)
  have hr := hR N hN1 i Δ V hb eleven
  dsimp only at hr
  rw [rpow_natCast] at hr
  have htheta := hTheta N hN2 i hb.1 Δ hb.2.1 hb.2.2.1 V
    hb.2.2.2.2.1 hb.2.2.2.2.2
  have hbudget : C / log (N : ℝ) ≤ ε * c := by
    apply (div_le_iff₀ hlog).mpr
    have h := (div_le_iff₀ (mul_pos hε hc)).mp (hlogT N hN3)
    dsimp only [Function.comp_apply] at h
    nlinarith
  calc
    _ ≤ C * N / log (N : ℝ) ^ (5 * k + 3) := hr
    _ = (C / log (N : ℝ)) * ((N : ℝ) / log (N : ℝ) ^ (5 * k + 2)) := by
      rw [show 5 * k + 3 = (5 * k + 2) + 1 by omega, pow_succ]
      ring
    _ ≤ (ε * c) * ((N : ℝ) / log (N : ℝ) ^ (5 * k + 2)) :=
      mul_le_mul_of_nonneg_right hbudget (by positivity)
    _ = ε * (c * (N : ℝ) / log (N : ℝ) ^ (5 * k + 2)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left htheta hε.le

theorem fourthRowTripleNoGate_R2_relative (k : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ eleven : Bool,
      let W := convolutionWuWindows N Δ V
      let Q := (N : ℝ) ^ (1 / 2 - δ)
      gamma16FamilyR2 N (⌊Q⌋₊ + 1) δ (sqrt Q) W (fourthRowTripleNoGateProfiles N δ W eleven) ≤
        ε * boxTheta N Q W := by
  obtain ⟨T, hT4, hpay⟩ := omega3_non_coprime_relative k hδ hδhi hε
  refine ⟨T, hT4, ?_⟩
  intro N hN i Δ V hb eleven W Q
  have hg := omega3_source_sieve_geometry (by omega : 2 ≤ N) hδ hδhi
  have hqN : ∀ q ∈ omega3SieveModuli N (⌊Q⌋₊ + 1) (sqrt Q), q ≤ N := by
    intro q hq
    have hqd := (omega3SieveModuli_properties hq).2.2.2
    have hDN := hg.2.2.2.2.2.2.1
    dsimp only [Q] at hqd
    omega
  have h := hpay N hN i Δ V hb (5 / 2) (103 / 25) (by norm_num) (by norm_num)
    (by norm_num) (sqrt Q) hg.2.2.2.1 (omega3SieveModuli N (⌊Q⌋₊ + 1) (sqrt Q))
    (filter_subset _ _) hqN
  apply le_trans _ h
  apply sum_le_sum
  intro q _
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact sum_le_sum_of_subset_of_nonneg
    (filter_subset_filter _ (fourthRowTripleNoGate_profiles_subset N δ W eleven))
    (fun _ _ _ => mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))

end Wu2008DoubleSieve
