import MathlibNt.Wu2008DoubleSieve.FourModulusTransportCount
import MathlibNt.Wu2008DoubleSieve.ElevenTermAssembly

/-!
# Transport of the last two evaluations of the finite eleven expression

The first nine terms and both original four-prime domains are unchanged.
This compares two expressions; it proves neither eleven-term upper bound.
-/

namespace Wu2008DoubleSieve

open Finset
open scoped Classical

noncomputable def fourModulusQuotientEleven (N : ℕ) (z w u v V : ℝ) : ℤ :=
  finiteElevenExpression N z w u v V (sieveCount N) (fun D y => sieveCount N D N y)

theorem fourModulus_eleven_difference (N : ℕ) (z w u v V : ℝ) :
    fourModulusQuotientEleven N z w u v V - finiteElevenMixed N z w u v V =
      fourModulusGain N z w V := by
  rw [fourModulusGain_eq_source_sub_quotient]
  unfold fourModulusQuotientEleven finiteElevenMixed finiteElevenExpression
    s3FourSourceMajorant s3Upsilon11Source s3FourSourceTerm
    fourModulusQuotientTerm fourModulusProduct
  ring

theorem fourModulus_eleven_bounds {N : ℕ} {κ w u v V : ℝ}
    (hN : 4 ≤ N) (he : Even N) (hκ : 0 < κ) (hz : 2 ≤ (N : ℝ) ^ κ) :
    0 ≤ (fourModulusQuotientEleven N ((N : ℝ) ^ κ) w u v V : ℝ) -
      (finiteElevenMixed N ((N : ℝ) ^ κ) w u v V : ℝ) ∧
    (fourModulusQuotientEleven N ((N : ℝ) ^ κ) w u v V : ℝ) -
      (finiteElevenMixed N ((N : ℝ) ^ κ) w u v V : ℝ) ≤
        2 / κ ^ 4 * (N : ℝ) ^ (1 - κ) := by
  rw [← Int.cast_sub, fourModulus_eleven_difference]
  exact ⟨by exact_mod_cast fourModulusGain_nonneg N ((N : ℝ) ^ κ) w V,
    fourModulusGain_le hN he hκ hz⟩

end Wu2008DoubleSieve
