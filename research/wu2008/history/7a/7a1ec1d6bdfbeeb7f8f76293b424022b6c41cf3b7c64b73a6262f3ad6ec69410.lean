import W13TightMoments

noncomputable section
open Real Wu2008DoubleSieve Wu08OriginalFourWeights
open WuTarget.W13

namespace WuTarget.W13Tight

def pairUpper : ℝ :=
  a2*momentUpper 2+a3*momentUpper 3+a4*momentUpper 4

theorem original_pair_upper : original10+original11 ≤ pairUpper := by
  have h2 := mul_le_mul_of_nonneg_left (moment_upper 2) coefficients_positive.2.1.le
  have h3 := mul_le_mul_of_nonneg_left (moment_upper 3) coefficients_positive.2.2.1.le
  have h4 := mul_le_mul_of_nonneg_left (moment_upper 4) coefficients_positive.2.2.2.le
  exact original_pair_le_moments.trans (add_le_add (add_le_add h2 h3) h4)

theorem moment_strict :
    momentUpper 2 < W13.momentUpper 2 ∧
      momentUpper 3 < W13.momentUpper 3 ∧
      momentUpper 4 < W13.momentUpper 4 := by
  have hk : 0 < 8*k := by
    have hk := fixed_lower_logs.2.2.2.2
    positivity
  have h2 := mul_lt_mul_of_pos_left discount_strict.1 hk
  have h3 := mul_lt_mul_of_pos_left discount_strict.2.1 hk
  have h4 := mul_lt_mul_of_pos_left discount_strict.2.2 hk
  unfold momentUpper W13.momentUpper
  norm_num only [Nat.cast_ofNat]
  ring_nf at h2 h3 h4 ⊢
  exact ⟨by linarith only [h2], by linarith only [h3], by linarith only [h4]⟩

theorem pair_strict : pairUpper < W13.pairUpper := by
  exact add_lt_add (add_lt_add
    (mul_lt_mul_of_pos_left moment_strict.1 coefficients_positive.2.1)
    (mul_lt_mul_of_pos_left moment_strict.2.1 coefficients_positive.2.2.1))
    (mul_lt_mul_of_pos_left moment_strict.2.2 coefficients_positive.2.2.2)

theorem exact_recovery :
    W13.pairUpper-pairUpper =
      8*k*(a2*(2*h*d^3/3+d^4/4)+
        a3*(h^2*d^3+3*h*d^4/4+d^5/5)+
        a4*(4*h^3*d^3/3+3*h^2*d^4/2+4*h*d^5/5+d^6/6)) := by
  unfold W13.pairUpper pairUpper W13.momentUpper momentUpper
  rw [discount_two, discount_three, discount_four]
  norm_num only [Nat.cast_ofNat]
  ring

end WuTarget.W13Tight
