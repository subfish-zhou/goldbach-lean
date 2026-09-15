import MathlibNt.Wu2008DoubleSieve.Omega3FiniteErrorWeighted
import MathlibNt.Wu2008DoubleSieve.Omega3SwitchingExceptional

/-!
# Actual Omega3 switching with all losses paid

Wu04 (5.4), retaining the literal strict p3 endpoint and the full
convolution multiplicity. The switched sieve is not estimated here.
-/

namespace Wu2008DoubleSieve

open Finset Real
open scoped Classical

theorem omega3_badD_relative (k : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → t ≤ 10 →
        omega3BadDCount N δ s t (convolutionWuWindows N Δ V) ≤
          ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  let η := wuLocalExponent k δ / 10
  have hη : 0 < η := div_pos (wuLocalExponent_pos k hδ hδhi) (by norm_num)
  obtain ⟨T0, hT04, hT0⟩ := omega3_source_window_lower k hδ hδhi
  obtain ⟨T1, _, hT1⟩ := omega3_power_mass_relative k hδ hδhi hε
    (show 0 < (1 / η) ^ 4 by positivity) hη
  refine ⟨max T0 T1, hT04.trans (le_max_left _ _), ?_⟩
  intro N hN he i Δ V hb s t hs hst ht
  have hN0 := (le_max_left T0 T1).trans hN
  have hN4 := hT04.trans hN0
  have hsp := fun d hd => wu_buchstab_prime_window_bounds (d := d)
    (show 2 ≤ N by omega) hδ hδhi hb hs hst ht hd
  have hf := omega3_badDCount_le_reciprocal_mass (s := s) (convolutionWuWindows N Δ V)
    hN4 he hη (fun d hd => ⟨(hsp d hd).1, (hsp d hd).2.1⟩)
    (fun d hd => (hsp d hd).2.2.2.1) (by
      intro d hd q hq
      have hq' := Nat.mem_primeFactors.mp hq
      exact omega3_support_prime_lower _ (fun j p hp =>
        ⟨(hT0 N hN0 i Δ V hb j p hp).1, (hT0 N hN0 i Δ V hb j p hp).2.2⟩)
        hd hq'.1 hq'.2.1)
  exact hf.trans (hT1 N ((le_max_right _ _).trans hN) i Δ V hb)

/-- The finite exceptional count includes every selected triple over each
output. The Cartesian triple bound is applied before weighting by sigma. -/
theorem omega3_exceptional_count_le {i N : ℕ} {δ s t η : ℝ}
    (W : Fin i → Finset ℕ) (hN : 4 ≤ N) (he : Even N) (hη : 0 < η)
    (hlow : ∀ d ∈ boxConvolutionSupport W, (N : ℝ) ^ η ≤ wuLocalCutoff N δ d t) :
    omega3ExceptionalOutputCount N δ s t W ≤
      ∑ d ∈ boxConvolutionSupport W, (convolutionCoeff W d : ℝ) *
        ((1 / η) ^ 3 * ((omega3ExceptionalOutputs N δ).card : ℝ)) := by
  unfold omega3ExceptionalOutputCount omega3LabelSum omega3ExceptionalOutputFibre
  apply sum_le_sum
  intro d hd
  exact mul_le_mul_of_nonneg_left
    (omega3_source_filter_sum_le_outputs (fun ell => ell ∈ omega3ExceptionalOutputs N δ)
      (omega3ExceptionalOutputs N δ) hN he hη (hlow d hd) (fun _ _ _ h => h))
    (Nat.cast_nonneg _)

theorem omega3_exceptional_relative (k : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → t ≤ 10 →
        omega3ExceptionalOutputCount N δ s t (convolutionWuWindows N Δ V) ≤
          ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  let η := wuLocalExponent k δ / 10
  have hη : 0 < η := div_pos (wuLocalExponent_pos k hδ hδhi) (by norm_num)
  obtain ⟨T, hT4, hT⟩ := omega3_exceptional_weight_relative k hδ hδhi hε
    (show 0 < (1 / η) ^ 3 by positivity)
  refine ⟨T, hT4, ?_⟩
  intro N hN he i Δ V hb s t hs hst ht
  have hN4 := hT4.trans hN
  have hf := omega3_exceptional_count_le (s := s) (convolutionWuWindows N Δ V) hN4 he hη
    (fun d hd => (wu_buchstab_prime_window_bounds (d := d) (show 2 ≤ N by omega)
      hδ hδhi hb hs hst ht hd).2.2.2.1)
  exact hf.trans (hT N hN i Δ V hb)

/-- Actual multiplicity-preserving Wu04 (5.4) with an epsilon*Theta loss.
All strengthened-coprimality and exceptional-output losses are internal.
The only positive count on the right is the actual sifted B' multiset. -/
theorem wu04_54 (k : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N0 : ℕ, T ≤ N0 → ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → t ≤ 10 →
        wuOmega3Sum N δ s t (convolutionWuWindows N Δ V) ≤
          omega3SwitchedSiftedCount N δ s t (sqrt ((N : ℝ) ^ (1 / 2 - δ)))
            (convolutionWuWindows N Δ V) +
          ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨T1, hT14, hT1⟩ := omega3_badD_relative k hδ hδhi (half_pos hε)
  obtain ⟨T2, _, hT2⟩ := omega3_exceptional_relative k hδ hδhi (half_pos hε)
  refine ⟨max T1 T2, hT14.trans (le_max_left _ _), ?_⟩
  intro N0 hN0 N hN he i Δ V hb s t hs hst ht
  have hN1 := (le_max_left T1 T2).trans (hN0.trans hN)
  have hN4 := hT14.trans hN1
  have h1 := hT1 N hN1 he i Δ V hb s t hs hst ht
  have h2 := hT2 N ((le_max_right _ _).trans (hN0.trans hN)) he i Δ V hb s t hs hst ht
  have hf := wuOmega3Sum_le_switched_add_badD_add_exceptional (δ := δ) (s := s) (t := t)
    (W := convolutionWuWindows N Δ V) hN4 he (fun d hd =>
      (omega3_source_support_le_Q (by omega) hδ hδhi hb hd).1)
  linarith

end Wu2008DoubleSieve
