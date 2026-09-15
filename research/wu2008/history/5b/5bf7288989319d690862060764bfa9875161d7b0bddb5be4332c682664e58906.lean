import MathlibNt.Wu2008DoubleSieve.FourthRowMotherBadPrime

/-! # One actual common-threshold payment for the original negative windows -/

namespace Wu2008DoubleSieve

open Finset
open scoped Classical

noncomputable def fourthRowMotherError {i : ℕ} (N : ℕ) (δ : ℝ)
    (W : Fin i → Finset ℕ) : ℝ :=
  ∑ d ∈ boxConvolutionSupport W, (convolutionCoeff W d : ℝ) *
    (2 * fourthRowMotherBadPrime N d (wuLocalCutoff N δ d (103 / 25))
        (wuLocalCutoff N δ d (5 / 2)) +
      fourthRowMotherBadPrime N d (wuLocalCutoff N δ d (103 / 25))
        (wuLocalCutoff N δ d (291 / 100)))

theorem fourthRowMother_source_cutoffs {i k N d : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1 / 2)
    (hb : wuSourceBox k δ N i Δ V)
    (hd : d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V)) :
    0 < d ∧ d ≤ N ∧
      wuLocalCutoff N δ d (103 / 25) ≤ wuLocalCutoff N δ d (89 / 25) ∧
      wuLocalCutoff N δ d (89 / 25) ≤ wuLocalCutoff N δ d (291 / 100) ∧
      wuLocalCutoff N δ d (291 / 100) ≤ wuLocalCutoff N δ d (5 / 2) := by
  have hg := wu_buchstab_prime_window_bounds (s := 2) (t := 2)
    hN hδ hδhi hb le_rfl le_rfl (by norm_num) hd
  refine ⟨hg.1, hg.2.1, ?_, ?_, ?_⟩ <;>
    exact Real.rpow_le_rpow_of_exponent_le hg.2.2.1.le (by norm_num)

theorem fourthRowMother_error_relative (k : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
        fourthRowMotherError N δ (convolutionWuWindows N Δ V) ≤
          ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  let η : ℝ := wuLocalExponent k δ / 10
  have hη : 0 < η := div_pos (wuLocalExponent_pos k hδ hδhi) (by norm_num)
  obtain ⟨T₀, hT₀4, hT₀⟩ := omega3_source_window_lower k hδ hδhi
  obtain ⟨T₁, hT₁4, hT₁⟩ := omega3_power_mass_relative k hδ hδhi hε
    (show 0 < 3 / η by positivity) hη
  refine ⟨max T₀ T₁, hT₀4.trans (le_max_left _ _), ?_⟩
  intro N hN he i Δ V hb
  have hN4 : 4 ≤ N := hT₀4.trans ((le_max_left _ _).trans hN)
  have hw := hT₀ N ((le_max_left _ _).trans hN) i Δ V hb
  have hfinite :
      fourthRowMotherError N δ (convolutionWuWindows N Δ V) ≤
        ((3 / η) * ((N : ℝ) / (N : ℝ) ^ η)) *
          boxConvolutionReciprocalMass (convolutionWuWindows N Δ V) := by
    unfold fourthRowMotherError boxConvolutionReciprocalMass
    rw [mul_sum]
    apply sum_le_sum
    intro d hd
    obtain ⟨hd0, hdN, _, _, hcf⟩ := fourthRowMother_source_cutoffs
      (by omega : 2 ≤ N) hδ hδhi hb hd
    have hlarge : ∀ p ∈ d.primeFactors, (N : ℝ) ^ η ≤ (p : ℝ) := by
      intro p hp
      obtain ⟨hpp, hpd, _⟩ := Nat.mem_primeFactors.mp hp
      exact omega3_support_prime_lower (convolutionWuWindows N Δ V)
        (fun j q hq => ⟨(hw j q hq).1, (hw j q hq).2.2⟩) hd hpp hpd
    have h := mul_le_mul_of_nonneg_left
      (fourthRowMother_error_power (a := wuLocalCutoff N δ d (103 / 25))
        hN4 he hd0 hdN hcf hη hlarge)
      (Nat.cast_nonneg (convolutionCoeff (convolutionWuWindows N Δ V) d) : (0 : ℝ) ≤ _)
    convert h using 1
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  exact hfinite.trans (hT₁ N ((le_max_right _ _).trans hN) i Δ V hb)

end Wu2008DoubleSieve
