import Wu18938Campaign.M2.SelectedMother

namespace Wu18938Campaign.M2

open Finset Wu2008DoubleSieve
open scoped Classical

theorem selected_source_power_mass (k : ℕ) {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) :
    ∃ η C : ℝ, 0 < η ∧ 0 < C ∧ ∃ T : ℕ, 4 ≤ T ∧
      ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible →
        5 * wuBoxPhi N δ (convolutionWuWindows N Δ V) p.s ≤
          selectedWeighted p N δ (convolutionWuWindows N Δ V) +
            (C * ((N : ℝ) / (N : ℝ) ^ η)) *
              boxConvolutionReciprocalMass (convolutionWuWindows N Δ V) := by
  let η : ℝ := wuLocalExponent k δ / 10
  have hη : 0 < η := div_pos (wuLocalExponent_pos k hδ hδhi) (by norm_num)
  obtain ⟨T, hT4, hT⟩ := omega3_source_window_lower k hδ hδhi
  refine ⟨η, 3 / η, hη, by positivity, T, hT4, ?_⟩
  intro N hN he i Δ V hb p hp
  have hN4 : 4 ≤ N := hT4.trans hN
  have hw := hT N hN i Δ V hb
  have herr : secondFunctionalMotherError p N δ (convolutionWuWindows N Δ V) ≤
      ((3 / η) * ((N : ℝ) / (N : ℝ) ^ η)) *
        boxConvolutionReciprocalMass (convolutionWuWindows N Δ V) := by
    unfold secondFunctionalMotherError boxConvolutionReciprocalMass
    rw [mul_sum]
    apply sum_le_sum
    intro d hd
    obtain ⟨hd0, hdN, _, _, hce, hef⟩ :=
      secondFunctionalMother_source_cutoffs p hp (by omega) hδ hδhi hb hd
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
  exact (selected_source_finite p hp (by omega) hδ hδhi hb).trans
    (add_le_add le_rfl herr)

end Wu18938Campaign.M2
