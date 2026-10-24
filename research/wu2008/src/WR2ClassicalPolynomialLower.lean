import Wu08OriginalFirstSteps

noncomputable section
namespace WuPaper.ClassicalPolynomial
open Real Set MeasureTheory Wu08OriginalFirstSteps

theorem monomial_integral (a b c : ℝ) (n : ℕ) :
    (∫ t in a..b, c*(t-a)^n) = c*(b-a)^(n+1)/((n:ℝ)+1) := by
  have hn : (n:ℝ)+1 ≠ 0 := by positivity
  have hd (t : ℝ) (_ht : t ∈ uIcc a b) :
      HasDerivAt (fun t => c*(t-a)^(n+1)/((n:ℝ)+1)) (c*(t-a)^n) t := by
    have h := ((((hasDerivAt_id t).sub_const a).pow (n+1)).const_mul c).div_const ((n:ℝ)+1)
    change HasDerivAt (fun t => c*(t-a)^(n+1)/((n:ℝ)+1)) _ t at h
    apply h.congr_deriv
    simp only [Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one,mul_one,id_eq]
    field_simp [hn]
  have hi : IntervalIntegrable (fun t => c*(t-a)^n) volume a b :=
    (by fun_prop : Continuous (fun t : ℝ => c*(t-a)^n)).intervalIntegrable a b
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi]
  simp

theorem integral_lower {f : ℝ → ℝ} {a b c : ℝ} (n : ℕ)
    (hab : a ≤ b) (hf : IntervalIntegrable f volume a b)
    (hlo : ∀ t ∈ Icc a b, c*(t-a)^n ≤ f t) :
    c*(b-a)^(n+1)/((n:ℝ)+1) ≤ ∫ t in a..b, f t := by
  rw [← monomial_integral]
  exact intervalIntegral.integral_mono_on hab
    ((by fun_prop : Continuous (fun t : ℝ => c*(t-a)^n)).intervalIntegrable a b) hf hlo

theorem divided_integral_lower {f : ℝ → ℝ} {a b c R : ℝ} (n : ℕ)
    (ha : 1 ≤ a) (hab : a ≤ b) (hb : b ≤ R) (hc : 0 ≤ c) (hf : Continuous f)
    (hlo : ∀ t ∈ Icc a b, c*(t-a)^n ≤ f t) :
    c/R*(b-a)^(n+1)/((n:ℝ)+1) ≤ ∫ t in a..b, f t/max 1 t := by
  apply integral_lower n hab ((div_continuous hf).intervalIntegrable a b)
  intro t ht
  have ht0 : 0 < t := by linarith [ht.1]
  have hn : 0 ≤ c*(t-a)^n := mul_nonneg hc (pow_nonneg (sub_nonneg.mpr ht.1) n)
  rw [max_eq_right (ha.trans ht.1)]
  have h := div_le_div₀ (hn.trans (hlo t ht)) (hlo t ht) ht0 (ht.2.trans hb)
  calc
    c/R*(t-a)^n = c*(t-a)^n/R := by ring
    _ ≤ _ := h

end WuPaper.ClassicalPolynomial
#print axioms WuPaper.ClassicalPolynomial.divided_integral_lower
