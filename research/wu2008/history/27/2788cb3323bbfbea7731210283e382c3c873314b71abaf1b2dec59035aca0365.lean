import MathlibNt.Wu2008DoubleSieve.FourthRowMotherPairMass
import MathlibNt.Wu2008DoubleSieve.FourthRowMotherNine

/-! # Actual no-error masked-prefix finite mother inequality -/

namespace Wu2008DoubleSieve

open Finset
open scoped Classical

theorem fourthRowMother_masked_identity (N d : ℕ) {a b c f : ℝ}
    (hab : a ≤ b) (hbc : b ≤ c) (hcf : c ≤ f) :
    fourthRowMotherLocal N d (d * N) a b c f =
      ∑ ell ∈ sieveCarrier N d (d * N) a,
        fourthRowMotherLabelWeight
          (divisorsIn (primeWindow (d * N) a f) ((N - ell) / d))
          (fourthRowMotherColour b c) := by
  unfold fourthRowMotherLocal
  rw [fourthRowMother_single_mass, fourthRowMother_single_mass,
    fourthRowMother_gamma5_mass N d hbc hcf, fourthRowMother_gamma6_mass N d hab hbc hcf,
    fourthRowMother_gamma9_mass N d hab (hbc.trans hcf)]
  rw [fourthRowMother_prefix_mass N d a b c f [0, 0] (by simp),
    fourthRowMother_prefix_mass N d a b c f [0, 1] (by simp),
    fourthRowMother_prefix_mass N d a b c f [1, 1, 2] (by simp),
    fourthRowMother_prefix_mass N d a b c f [1, 2, 2] (by simp),
    fourthRowMother_prefix_mass N d a b c f [0, 1, 2] (by simp),
    fourthRowMother_prefix_mass N d a b c f [0, 2, 2] (by simp),
    fourthRowMother_prefix_mass N d a b c f [2, 2, 2, 2] (by simp)]
  rw [fourthRowMother_cutoff_card N d hab]
  simp only [fourthRowMotherLabelWeight, fourthRowMother_band_zero _ _ (hbc.trans hcf),
    fourthRowMother_band_low _ _ hbc hcf, sum_add_distrib, sum_sub_distrib, mul_sum]
  simp only [sourceSieveCount, source_double_sieve_carriers, Int.cast_natCast,
    sum_const, nsmul_eq_mul]
  ring

theorem fourthRowMother_masked (N d : ℕ) {a b c f : ℝ}
    (hab : a ≤ b) (hbc : b ≤ c) (hcf : c ≤ f) :
    5 * (sourceSieveCount N d (d * N) f : ℝ) ≤ fourthRowMotherLocal N d (d * N) a b c f := by
  rw [fourthRowMother_masked_identity N d hab hbc hcf]
  exact fourthRowMother_actual_weight_sum N d (hab.trans (hbc.trans hcf))

end Wu2008DoubleSieve
