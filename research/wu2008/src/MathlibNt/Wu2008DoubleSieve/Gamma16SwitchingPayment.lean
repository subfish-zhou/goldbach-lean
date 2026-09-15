import MathlibNt.Wu2008DoubleSieve.Gamma16FiniteSwitching

/-! # Actual arity-four exceptional counts paid against source Theta -/

namespace Wu2008DoubleSieve

open Finset Real
open scoped Classical

theorem gamma16_bad_relative (k : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
        gamma16BadCount N δ (convolutionWuWindows N Δ V) ≤
          ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  let η := wuLocalExponent k δ / 10
  have hη : 0 < η := div_pos (wuLocalExponent_pos k hδ hδhi) (by norm_num)
  obtain ⟨T0, hT0, hw⟩ := omega3_source_window_lower k hδ hδhi
  obtain ⟨T1, _, hp⟩ := omega3_power_mass_relative k hδ hδhi hε
    (show 0 < (1 / η) ^ 5 by positivity) hη
  refine ⟨max T0 T1, hT0.trans (le_max_left _ _), ?_⟩
  intro N hN he i Δ V hb
  have hN0 := (le_max_left T0 T1).trans hN
  have hN4 := hT0.trans hN0
  have hbound (d : ℕ) (hd : d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V)) :
      (((gamma16OutputLabels N δ d).filter (fun a => Omega3BadD N d a.2)).card : ℝ) ≤
        (1 / η) ^ 5 * (N : ℝ) / ((d : ℝ) * (N : ℝ) ^ η) := by
    have hg := wu_buchstab_prime_window_bounds (by omega) hδ hδhi hb
      (s := 5 / 2) (t := 291 / 100) (by norm_num) (by norm_num) (by norm_num) hd
    unfold Omega3BadD
    convert omega3_bad_labels_card_le_power (N := N) (d := d) (η := η)
      (r := 4) (gamma16OutputLabels N δ d)
      Sigma.snd Sigma.fst gamma16_output_label_injective.injOn (by omega) hg.1 hg.2.1 hη
      ?_ ?_ ?_ ?_ using 1
    · congr 2
      ext a
      simp only [mem_filter]
    · intro q hq
      have hq' := Nat.mem_primeFactors.mp hq
      exact omega3_support_prime_lower _ (fun j p hp =>
        ⟨(hw N hN0 i Δ V hb j p hp).1, (hw N hN0 i Δ V hb j p hp).2.2⟩)
        hd hq'.1 hq'.2.1
    · exact fun a ha => gamma16_output_lt hN4 he ha
    · intro a ha
      exact (dvd_mul_right d (gamma16Product a.1)).trans
        (mem_filter.mp (mem_sigma.mp ha).2).2.2.1
    · exact fun a ha => gamma16_selected_large hg.2.2.2.1 ha
  have hs := sum_le_sum (s := boxConvolutionSupport (convolutionWuWindows N Δ V))
    (fun d hd => mul_le_mul_of_nonneg_left (hbound d hd)
      (Nat.cast_nonneg (convolutionCoeff (convolutionWuWindows N Δ V) d) : (0 : ℝ) ≤ _))
  have hnorm :
      (∑ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
        (convolutionCoeff (convolutionWuWindows N Δ V) d : ℝ) *
          ((1 / η) ^ 5 * (N : ℝ) / ((d : ℝ) * (N : ℝ) ^ η))) =
      (1 / η) ^ 5 * (N : ℝ) / (N : ℝ) ^ η *
        boxConvolutionReciprocalMass (convolutionWuWindows N Δ V) := by
    unfold boxConvolutionReciprocalMass
    rw [mul_sum]
    apply sum_congr rfl
    intro d _
    ring
  rw [hnorm] at hs
  exact hs.trans (by
    simpa only [mul_div_assoc] using (hp N ((le_max_right _ _).trans hN) i Δ V hb))

theorem gamma16_exceptional_relative (k : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
        gamma16ExceptionalCount N δ (convolutionWuWindows N Δ V) ≤
          ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  let η := wuLocalExponent k δ / 10
  have hη : 0 < η := div_pos (wuLocalExponent_pos k hδ hδhi) (by norm_num)
  obtain ⟨T, hT, hp⟩ := omega3_exceptional_weight_relative k hδ hδhi hε
    (show 0 < (1 / η) ^ 4 by positivity)
  refine ⟨T, hT, ?_⟩
  intro N hN he i Δ V hb
  have hN4 := hT.trans hN
  have hs : gamma16ExceptionalCount N δ (convolutionWuWindows N Δ V) ≤
      ∑ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
        (convolutionCoeff (convolutionWuWindows N Δ V) d : ℝ) *
          ((1 / η) ^ 4 * ((omega3ExceptionalOutputs N δ).card : ℝ)) := by
    apply sum_le_sum
    intro d hd
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    apply omega3_labels_card_le_allowed_outputs (N := N) (r := 4) (gamma16OutputLabels N δ d)
      Sigma.snd Sigma.fst (omega3ExceptionalOutputs N δ)
      gamma16_output_label_injective.injOn (by omega) hη
    · exact fun a ha => gamma16_output_lt hN4 he ha
    · exact fun a ha => gamma16_selected_large
        (wu_buchstab_prime_window_bounds (by omega) hδ hδhi hb
          (s := 5 / 2) (t := 291 / 100) (by norm_num) (by norm_num) (by norm_num) hd).2.2.2.1 ha
  exact hs.trans (hp N hN i Δ V hb)

theorem gamma16_prefix_switching_paid (k : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
        gamma16PrefixSum N δ (convolutionWuWindows N Δ V) ≤
          gamma16S N δ (sqrt ((N : ℝ) ^ (1 / 2 - δ))) (convolutionWuWindows N Δ V) +
          ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨T1, hT1, h1⟩ := gamma16_bad_relative k hδ hδhi (half_pos hε)
  obtain ⟨T2, _, h2⟩ := gamma16_exceptional_relative k hδ hδhi (half_pos hε)
  refine ⟨max T1 T2, hT1.trans (le_max_left _ _), ?_⟩
  intro N hN he i Δ V hb
  have hN1 := (le_max_left T1 T2).trans hN
  have hN4 := hT1.trans hN1
  have hbad := h1 N hN1 he i Δ V hb
  have hex := h2 N ((le_max_right _ _).trans hN) he i Δ V hb
  have hf := gamma16_prefix_finite_switching (δ := δ) hN4 he (fun d hd =>
    (omega3_source_support_le_Q (by omega) hδ hδhi hb hd).1)
  linarith

end Wu2008DoubleSieve