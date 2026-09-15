import MathlibNt.Wu2008DoubleSieve.SecondFunctionalMotherSourceCutoffs

/-! # Payment for the three genuine negative windows -/

namespace Wu2008DoubleSieve

/-- Three distinct windows cost the same factor as three copies of the largest. -/
theorem secondFunctionalMother_three_error_power {N d : ℕ} {a c e f η : ℝ}
    (hN : 4 ≤ N) (he : Even N) (hd : 0 < d) (hdN : d ≤ N)
    (hce : c ≤ e) (hef : e ≤ f) (hη : 0 < η)
    (hlarge : ∀ q ∈ d.primeFactors, (N : ℝ) ^ η ≤ (q : ℝ)) :
    fourthRowMotherBadPrime N d a f + fourthRowMotherBadPrime N d a c +
        fourthRowMotherBadPrime N d a e ≤
      (3 / η) * (N : ℝ) / ((d : ℝ) * (N : ℝ) ^ η) := by
  have hc := fourthRowMother_bad_prime_mono N d a (hce.trans hef)
  have he' := fourthRowMother_bad_prime_mono N d a hef
  have h := fourthRowMother_error_power (a := a) (c := f) (f := f)
    hN he hd hdN le_rfl hη hlarge
  linarith

open Finset
open scoped Classical

noncomputable def secondFunctionalMotherError (p : SecondFunctionalParameters)
    {i : ℕ} (N : ℕ) (δ : ℝ) (W : Fin i → Finset ℕ) : ℝ :=
  ∑ d ∈ boxConvolutionSupport W, (convolutionCoeff W d : ℝ) *
    (fourthRowMotherBadPrime N d (wuLocalCutoff N δ d p.S) (wuLocalCutoff N δ d p.s) +
      fourthRowMotherBadPrime N d (wuLocalCutoff N δ d p.S) (wuLocalCutoff N δ d p.kappa2) +
      fourthRowMotherBadPrime N d (wuLocalCutoff N δ d p.S) (wuLocalCutoff N δ d p.kappa3))

/-- The threshold is chosen before every source box and support divisor. -/
theorem secondFunctionalMother_error_relative
    (k : ℕ) (p : SecondFunctionalParameters) (hp : p.MotherAdmissible) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
        secondFunctionalMotherError p N δ (convolutionWuWindows N Δ V) ≤
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
      secondFunctionalMotherError p N δ (convolutionWuWindows N Δ V) ≤
        ((3 / η) * ((N : ℝ) / (N : ℝ) ^ η)) *
          boxConvolutionReciprocalMass (convolutionWuWindows N Δ V) := by
    unfold secondFunctionalMotherError boxConvolutionReciprocalMass
    rw [mul_sum]
    apply sum_le_sum
    intro d hd
    obtain ⟨hd0, hdN, _, _, hce, hef⟩ := secondFunctionalMother_source_cutoffs p hp
      (by omega : 2 ≤ N) hδ hδhi hb hd
    have hlarge : ∀ q ∈ d.primeFactors, (N : ℝ) ^ η ≤ (q : ℝ) := by
      intro q hq
      obtain ⟨hqp, hqd, _⟩ := Nat.mem_primeFactors.mp hq
      exact omega3_support_prime_lower (convolutionWuWindows N Δ V)
        (fun j r hr => ⟨(hw j r hr).1, (hw j r hr).2.2⟩) hd hqp hqd
    have h := mul_le_mul_of_nonneg_left
      (secondFunctionalMother_three_error_power (a := wuLocalCutoff N δ d p.S)
        hN4 he hd0 hdN hce hef hη hlarge)
      (Nat.cast_nonneg (convolutionCoeff (convolutionWuWindows N Δ V) d) : (0 : ℝ) ≤ _)
    convert h using 1
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  exact hfinite.trans (hT₁ N ((le_max_right _ _).trans hN) i Δ V hb)

end Wu2008DoubleSieve
