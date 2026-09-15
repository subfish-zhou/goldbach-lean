import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighNonunitFinite
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighUnitSieveGeometry

namespace Wu2008DoubleSieve.HighNonunit

/-- The actual mother window itself gives the common large-prime threshold.
No unit equation or selected-colour case split is needed. -/
theorem mother_window_lower {k i N d q : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1/2)
    (hb : wuSourceBox k δ N i Δ V) (p : SecondFunctionalParameters)
    (hp : p.MotherAdmissible)
    (hd : d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V))
    (hq : q ∈ primeWindow N (wuLocalCutoff N δ d p.S) (wuLocalCutoff N δ d p.s)) :
    q.Prime ∧ (N:ℝ)^(wuLocalExponent k δ / 10) ≤ (q:ℝ) := by
  have hS : 0 < p.S := lt_of_lt_of_le (by norm_num : (0:ℝ) < 1)
    (hp.one_le_s.trans (hp.s_le_kappa3.trans (hp.kappa3_lt_kappa2.le.trans
      (hp.kappa2_lt_kappa1.le.trans hp.kappa1_le_S))))
  have hinv : (1:ℝ)/10 ≤ 1/p.S := one_div_le_one_div_of_le hS hp.S_le_ten
  have hg := omega3XPhi_source_bounds hN hδ hδhi hb hd
  have hpow := Real.rpow_le_rpow (Real.rpow_nonneg (Nat.cast_nonneg N) _) hg.1
    (by norm_num : (0:ℝ) ≤ 1/10)
  have hstep : (N:ℝ)^(wuLocalExponent k δ / 10) ≤
      ((N:ℝ)^(1/2-δ)/d)^(1/10:ℝ) := by
    simpa only [← Real.rpow_mul (Nat.cast_nonneg N), div_eq_mul_inv, one_mul] using hpow
  exact ⟨(mem_primeWindow.mp hq).1, hstep.trans
    ((Real.rpow_le_rpow_of_exponent_le hg.2.1.le hinv).trans (mem_primeWindow.mp hq).2.2.1)⟩

end Wu2008DoubleSieve.HighNonunit
