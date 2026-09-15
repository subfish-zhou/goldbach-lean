import MathlibNt.Wu2008DoubleSieve.FourthRowMotherPrefixMass
import MathlibNt.Wu2008DoubleSieve.OmegaWeighted

/-! # Actual divisor bands and the per-output finite fivefold bound -/

namespace Wu2008DoubleSieve

open Finset
open scoped Classical

theorem fourthRowMother_colour_zero (b c : ℝ) (p : ℕ) :
    fourthRowMotherColour b c p = 0 ↔ (p : ℝ) < b := by
  unfold fourthRowMotherColour
  split_ifs <;> simp_all

theorem fourthRowMother_colour_low {b c : ℝ} (hbc : b ≤ c) (p : ℕ) :
    fourthRowMotherColour b c p ≤ 1 ↔ (p : ℝ) < c := by
  unfold fourthRowMotherColour
  split_ifs <;> simp_all
  linarith

theorem fourthRowMother_colour_two {b c : ℝ} (hbc : b ≤ c) (p : ℕ) :
    fourthRowMotherColour b c p = 2 ↔ c ≤ (p : ℝ) := by
  unfold fourthRowMotherColour
  split_ifs <;> simp_all
  linarith

theorem fourthRowMother_band_zero (M n : ℕ) {a b c f : ℝ} (hbf : b ≤ f) :
    (divisorsIn (primeWindow M a f) n).filter
      (fun p => fourthRowMotherColour b c p = 0) =
      divisorsIn (primeWindow M a b) n := by
  ext p
  simp only [divisorsIn, mem_filter, mem_primeWindow, fourthRowMother_colour_zero]
  constructor
  · rintro ⟨⟨⟨hp, hM, ha, _⟩, hd⟩, hb⟩
    exact ⟨⟨hp, hM, ha, hb⟩, hd⟩
  · rintro ⟨⟨hp, hM, ha, hb⟩, hd⟩
    exact ⟨⟨⟨hp, hM, ha, hb.trans_le hbf⟩, hd⟩, hb⟩

theorem fourthRowMother_band_low (M n : ℕ) {a b c f : ℝ}
    (hbc : b ≤ c) (hcf : c ≤ f) :
    (divisorsIn (primeWindow M a f) n).filter
      (fun p => fourthRowMotherColour b c p ≤ 1) =
      divisorsIn (primeWindow M a c) n := by
  ext p
  simp only [divisorsIn, mem_filter, mem_primeWindow, fourthRowMother_colour_low hbc]
  constructor
  · rintro ⟨⟨⟨hp, hM, ha, _⟩, hd⟩, hc⟩
    exact ⟨⟨hp, hM, ha, hc⟩, hd⟩
  · rintro ⟨⟨hp, hM, ha, hc⟩, hd⟩
    exact ⟨⟨⟨hp, hM, ha, hc.trans_le hcf⟩, hd⟩, hc⟩

theorem fourthRowMother_band_two (M n : ℕ) {a b c f : ℝ}
    (hab : a ≤ b) (hbc : b ≤ c) :
    (divisorsIn (primeWindow M a f) n).filter
      (fun p => fourthRowMotherColour b c p = 2) =
      divisorsIn (primeWindow M c f) n := by
  ext p
  simp only [divisorsIn, mem_filter, mem_primeWindow, fourthRowMother_colour_two hbc]
  constructor
  · rintro ⟨⟨⟨hp, hM, _, hf⟩, hd⟩, hc⟩
    exact ⟨⟨hp, hM, hc, hf⟩, hd⟩
  · rintro ⟨⟨hp, hM, hc, hf⟩, hd⟩
    exact ⟨⟨⟨hp, hM, hab.trans (hbc.trans hc), hf⟩, hd⟩, hc⟩

theorem fourthRowMother_band_high (M n : ℕ) {a b c f : ℝ} (hab : a ≤ b) :
    (divisorsIn (primeWindow M a f) n).filter
      (fun p => fourthRowMotherColour b c p ≠ 0) =
      divisorsIn (primeWindow M b f) n := by
  ext p
  simp only [divisorsIn, mem_filter, mem_primeWindow, ne_eq, fourthRowMother_colour_zero,
    not_lt]
  constructor
  · rintro ⟨⟨⟨hp, hM, _, hf⟩, hd⟩, hb⟩
    exact ⟨⟨hp, hM, hb, hf⟩, hd⟩
  · rintro ⟨⟨hp, hM, hb, hf⟩, hd⟩
    exact ⟨⟨⟨hp, hM, hab.trans hb, hf⟩, hd⟩, hb⟩

theorem fourthRowMother_single_mass (N d : ℕ) (a u : ℝ) :
    fourthRowMotherSingle N d (d * N) a u =
      ∑ ell ∈ sieveCarrier N d (d * N) a,
        ((divisorsIn (primeWindow (d * N) a u) ((N - ell) / d)).card : ℝ) := by
  simp only [fourthRowMotherSingle, sourceSieveCount, Int.cast_natCast]
  simp only [← fourthRowMother_fixed_carrier N d _ (d * N) a (dvd_mul_right d N),
    divisorsIn, ← sum_boole]
  rw [sum_comm]

theorem fourthRowMother_cutoff_card (N d : ℕ) {a b : ℝ} (hab : a ≤ b) :
    (sourceSieveCount N d (d * N) b : ℝ) =
      ∑ ell ∈ sieveCarrier N d (d * N) a,
        if divisorsIn (primeWindow (d * N) a b) ((N - ell) / d) = ∅
          then (1 : ℝ) else 0 := by
  rw [sum_boole]
  change _ = ((siftedIndices (sieveCarrier N d (d * N) a)
    (fun ell => (N - ell) / d) (primeWindow (d * N) a b)).card : ℝ)
  rw [siftedIndices_sieveCarrier N d (d * N) hab]
  simp only [sourceSieveCount, source_double_sieve_carriers, Int.cast_natCast]

theorem fourthRowMother_actual_weight_sum (N d : ℕ) {a b c f : ℝ} (haf : a ≤ f) :
    5 * (sourceSieveCount N d (d * N) f : ℝ) ≤
      ∑ ell ∈ sieveCarrier N d (d * N) a,
        fourthRowMotherLabelWeight
          (divisorsIn (primeWindow (d * N) a f) ((N - ell) / d))
          (fourthRowMotherColour b c) := by
  rw [fourthRowMother_cutoff_card N d haf, mul_sum]
  apply sum_le_sum
  intro ell _
  simpa only [mul_ite, mul_one, mul_zero] using
    fourthRowMother_actual_divisor_weight (primeWindow (d * N) a f)
      ((N - ell) / d) b c

end Wu2008DoubleSieve
