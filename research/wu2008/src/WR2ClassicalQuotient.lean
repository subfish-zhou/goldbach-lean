import WR2ClassicalTrapezoid

noncomputable section
namespace WuPaper.ClassicalQuotient
open Real

def value (f : ℝ → ℝ) (t : ℝ) : ℝ := f t/t
def first (f f' : ℝ → ℝ) (t : ℝ) : ℝ := f' t/t-f t/t^2
def second (f f' f'' : ℝ → ℝ) (t : ℝ) : ℝ := f'' t/t-2*f' t/t^2+2*f t/t^3

theorem value_deriv {f f' : ℝ → ℝ} {t : ℝ} (ht : t ≠ 0)
    (hf : HasDerivAt f (f' t) t) : HasDerivAt (value f) (first f f' t) t := by
  have h := hf.div (hasDerivAt_id t) ht
  change HasDerivAt (value f) _ t at h
  apply h.congr_deriv
  dsimp [first]
  field_simp

theorem first_deriv {f f' f'' : ℝ → ℝ} {t : ℝ} (ht : t ≠ 0)
    (hf : HasDerivAt f (f' t) t) (hf' : HasDerivAt f' (f'' t) t) :
    HasDerivAt (first f f') (second f f' f'' t) t := by
  have h := (hf'.div (hasDerivAt_id t) ht).sub
    (hf.div ((hasDerivAt_id t).pow 2) (pow_ne_zero 2 ht))
  change HasDerivAt (first f f') _ t at h
  apply h.congr_deriv
  dsimp [second]
  field_simp
  ring

/-- One bound serves every divide-by-parameter step in the sieve recurrence. -/
theorem second_bound {f f' f'' : ℝ → ℝ} {t m F0 F1 F2 : ℝ}
    (hm : 0 < m) (ht : m ≤ t)
    (h0 : |f t| ≤ F0) (h1 : |f' t| ≤ F1) (h2 : |f'' t| ≤ F2) :
    |second f f' f'' t| ≤ F2/m+2*F1/m^2+2*F0/m^3 := by
  have ht0 : 0 < t := hm.trans_le ht
  have hF0 : 0 ≤ F0 := (abs_nonneg _).trans h0
  have hF1 : 0 ≤ F1 := (abs_nonneg _).trans h1
  have hF2 : 0 ≤ F2 := (abs_nonneg _).trans h2
  have hA : |f'' t/t| ≤ F2/m := by
    rw [abs_div,abs_of_pos ht0]
    exact div_le_div₀ hF2 h2 hm ht
  have hB : |2*f' t/t^2| ≤ 2*F1/m^2 := by
    rw [abs_div,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2),abs_of_pos (sq_pos_of_pos ht0)]
    gcongr
  have hC : |2*f t/t^3| ≤ 2*F0/m^3 := by
    rw [abs_div,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2),abs_of_pos (pow_pos ht0 3)]
    gcongr
  have hh := abs_add_le (f'' t/t-2*f' t/t^2) (2*f t/t^3)
  have hs := abs_sub (f'' t/t) (2*f' t/t^2)
  unfold second
  linarith only [hh,hs,hA,hB,hC]

end WuPaper.ClassicalQuotient
#print axioms WuPaper.ClassicalQuotient.first_deriv
#print axioms WuPaper.ClassicalQuotient.second_bound
