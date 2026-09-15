import MathlibNt.Wu2008DoubleSieve.FourthRowTripleNoGateProfiles
import MathlibNt.Wu2008DoubleSieve.Omega3XBuchstabSource

/-! # The actual filtered X mass through the one-exemption Buchstab count -/

namespace Wu2008DoubleSieve

open Finset Real LiLiuPrereqBuchstab
open scoped Classical

noncomputable def fourthRowTripleNoGatePrimes (N d : ℕ) (δ : ℝ) (eleven : Bool) :
    Finset (ℕ × ℕ × ℕ) :=
  (omega3XPrimes N δ (5 / 2) (103 / 25) d).filter
    (fun p => fourthRowTripleNoGateBand N δ eleven d p.1 p.2.1)

noncomputable def fourthRowTripleNoGateBuchstab {i : ℕ} (N : ℕ) (δ : ℝ)
    (W : Fin i → Finset ℕ) (eleven : Bool) : ℝ :=
  ∑ d ∈ boxConvolutionSupport W, (convolutionCoeff W d : ℝ) *
    ∑ p ∈ fourthRowTripleNoGatePrimes N d δ eleven,
      omega3XScale N d p.1 p.2.1 p.2.2 *
        buchstab (log (omega3XScale N d p.1 p.2.1 p.2.2) / log p.2.1) / log p.2.1

theorem fourthRowTripleNoGate_X_buchstab (k : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ eleven : Bool,
      let W := convolutionWuWindows N Δ V
      fourthRowTripleNoGateX N δ W eleven ≤ fourthRowTripleNoGateBuchstab N δ W eleven +
        ε * ((N : ℝ) / log N) * boxConvolutionReciprocalMass W := by
  obtain ⟨C, T1, hC, hT1, hscale⟩ := omega3X_weighted_scale_mass_uniform k hδ hδhi
  obtain ⟨T2, _, hrough⟩ := omega3X_buchstab_uniform k hδ hδhi
    (div_pos (half_pos hε) hC)
  obtain ⟨T3, _, hrep⟩ := omega3XRepeatedMajorant_relative k hδ hδhi (half_pos hε)
  refine ⟨max T1 (max T2 T3), hT1.trans (le_max_left _ _), ?_⟩
  intro N hN i Δ V hb eleven W
  have hN1 := (le_max_left T1 _).trans hN
  have hN2 := (le_max_left T2 _).trans ((le_max_right T1 _).trans hN)
  have hN3 := (le_max_right T2 _).trans ((le_max_right T1 _).trans hN)
  have hN4 := hT1.trans hN1
  have hs := hscale N hN1 i Δ V hb (5 / 2) (103 / 25)
    (by norm_num) (by norm_num) (by norm_num)
  have hr := hrep N hN3 i Δ V hb (5 / 2) (103 / 25)
    (by norm_num) (by norm_num) (by norm_num)
  let E := ∑ d ∈ boxConvolutionSupport W, (convolutionCoeff W d : ℝ) *
    ∑ p ∈ omega3XPrimes N δ (5 / 2) (103 / 25) d,
      omega3XScale N d p.1 p.2.1 p.2.2 / log p.2.1
  have hf : fourthRowTripleNoGateX N δ W eleven ≤
      fourthRowTripleNoGateBuchstab N δ W eleven + (ε / 2 / C) * E +
        omega3XRepeatedMajorant N δ (5 / 2) (103 / 25) W := by
    rw [fourthRowTripleNoGate_X_reorder]
    unfold fourthRowTripleNoGateBuchstab omega3XRepeatedMajorant
    dsimp only [E, fourthRowTripleNoGatePrimes]
    rw [mul_sum, ← sum_add_distrib, ← sum_add_distrib]
    apply sum_le_sum
    intro d hd
    have hd0 := (omega3_source_support_le_Q (by omega : 2 ≤ N) hδ hδhi hb hd).1
    have hterm (p : ℕ × ℕ × ℕ)
        (hp : p ∈ omega3XPrimes N δ (5 / 2) (103 / 25) d) :
        ((omega3XNCountFibre N d p.1 p.2.1 p.2.2).card : ℝ) ≤
          omega3XScale N d p.1 p.2.1 p.2.2 *
            buchstab (log (omega3XScale N d p.1 p.2.1 p.2.2) / log p.2.1) / log p.2.1 +
          (ε / 2 / C) * (omega3XScale N d p.1 p.2.1 p.2.2 / log p.2.1) +
          (⌊omega3XScale N d p.1 p.2.1 p.2.2 / p.1⌋₊ : ℝ) := by
      have hp' := mem_omega3XPrimes.mp hp
      have hcard := omega3XNCountFibre_card_le_rough_add_floor (N := N) hd0
        (mem_primeWindow.mp hp'.2.1).1.pos (mem_primeWindow.mp hp'.1).1.pos hp'.2.2.2.1.pos
      have hb' := (hrough N hN2 i Δ V hb d hd (5 / 2) (103 / 25)
        (by norm_num) (by norm_num) (by norm_num) p hp).2.2
      have ha := (abs_sub_le_iff.mp hb').1
      have hcast : ((omega3XNCountFibre N d p.1 p.2.1 p.2.2).card : ℝ) ≤
          (roughCount (omega3XScale N d p.1 p.2.1 p.2.2) p.2.1 : ℝ) +
            (⌊omega3XScale N d p.1 p.2.1 p.2.2 / p.1⌋₊ : ℝ) := by exact_mod_cast hcard
      linarith
    have hsum :
        (∑ p ∈ (omega3XPrimes N δ (5 / 2) (103 / 25) d).filter
          (fun p => fourthRowTripleNoGateBand N δ eleven d p.1 p.2.1),
          ((omega3XNCountFibre N d p.1 p.2.1 p.2.2).card : ℝ)) ≤
        (∑ p ∈ (omega3XPrimes N δ (5 / 2) (103 / 25) d).filter
          (fun p => fourthRowTripleNoGateBand N δ eleven d p.1 p.2.1),
          omega3XScale N d p.1 p.2.1 p.2.2 *
            buchstab (log (omega3XScale N d p.1 p.2.1 p.2.2) / log p.2.1) / log p.2.1) +
        (ε / 2 / C) * (∑ p ∈ omega3XPrimes N δ (5 / 2) (103 / 25) d,
          omega3XScale N d p.1 p.2.1 p.2.2 / log p.2.1) +
        ∑ p ∈ omega3XPrimes N δ (5 / 2) (103 / 25) d,
          (⌊omega3XScale N d p.1 p.2.1 p.2.2 / p.1⌋₊ : ℝ) := by
      rw [sum_filter, sum_filter, mul_sum, ← sum_add_distrib, ← sum_add_distrib]
      apply sum_le_sum
      intro p hp
      have hl := log_pos (show (1 : ℝ) < p.2.1 by
        exact_mod_cast (mem_primeWindow.mp (mem_omega3XPrimes.mp hp).1).1.one_lt)
      by_cases hband : fourthRowTripleNoGateBand N δ eleven d p.1 p.2.1
      · simpa only [hband, if_true] using hterm p hp
      · simp only [hband, if_false]
        have hx := omega3XScale_nonneg N d p.1 p.2.1 p.2.2
        positivity
    convert mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg (convolutionCoeff W d) : (0 : ℝ) ≤ _) using 1
    ring
  have he := mul_le_mul_of_nonneg_left hs (show 0 ≤ ε / 2 / C by positivity)
  have hcancel : ε / 2 / C * (C * ((N : ℝ) / log N) * boxConvolutionReciprocalMass W) =
      ε / 2 * ((N : ℝ) / log N) * boxConvolutionReciprocalMass W := by field_simp
  change ε / 2 / C * E ≤ _ at he
  rw [hcancel] at he
  linarith

end Wu2008DoubleSieve
