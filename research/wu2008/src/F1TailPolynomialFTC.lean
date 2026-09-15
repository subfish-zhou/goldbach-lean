import F1TailPolynomialSigns

noncomputable section
open Real Set MeasureTheory Polynomial
namespace F1TailPolynomialFTC

/-- Exact polynomial endpoint sum on the unchanged original interval. -/
def moment (p : ℝ[X]) : ℝ :=
  p.sum fun n c => c*((927/200)^(n+1)-2^(n+1))/(n+1)

theorem moment_exact (p : ℝ[X]) :
    (∫ u in (2:ℝ)..(927/200), p.eval u) = moment p := by
  simp_rw [Polynomial.eval_eq_sum, Polynomial.sum_def]
  rw [intervalIntegral.integral_finsetSum]
  · simp only [intervalIntegral.integral_const_mul, integral_pow]
    unfold moment
    rw [Polynomial.sum_def]
    apply Finset.sum_congr rfl
    intro n hn
    ring
  · intro n hn
    exact (continuous_const.mul (continuous_id.pow n)).intervalIntegrable _ _

/-- This is the fixed denominator square, integrated without new weights or cuts. -/
theorem fixed_payment (p d : ℝ[X]) (w : ℝ → ℝ)
    (hw : IntervalIntegrable w volume 2 (927/200))
    (hp : ∀ u ∈ Icc 2 (927/200), 0 ≤ p.eval u)
    (hd : ∀ u ∈ Icc 2 (927/200), 0 < d.eval u)
    (he : ∀ u ∈ Icc 2 (927/200), w u = p.eval u / d.eval u) :
    moment p ^ 2 / moment (p*d) ≤ ∫ u in (2:ℝ)..(927/200), w u := by
  have hpd : IntervalIntegrable (fun u => p.eval u*d.eval u) volume 2 (927/200) :=
    (p.continuous.mul d.continuous).intervalIntegrable _ _
  have hpI := p.continuous.intervalIntegrable (μ := volume) (2:ℝ) (927/200)
  have hJ : 0 ≤ moment (p*d) := by
    rw [← moment_exact]
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro u hu
    simpa only [Polynomial.eval_mul] using mul_nonneg (hp u hu) (hd u hu).le
  by_cases hz : moment (p*d)=0
  · rw [hz, div_zero]
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro u hu
    rw [he u hu]
    exact div_nonneg (hp u hu) (hd u hu).le
  · let a := moment p / moment (p*d)
    have hi := intervalIntegral.integral_mono_on (by norm_num : (2:ℝ) ≤ 927/200)
      ((hpI.const_mul (2*a)).sub (hpd.const_mul (a^2))) hw
      (fun u hu => by
        simpa only [mul_assoc] using
          (F1TailDenominatorPayment.fixed_affine_lower (hp u hu) (hd u hu) a).trans_eq
            (he u hu).symm)
    rw [intervalIntegral.integral_sub (hpI.const_mul (2*a)) (hpd.const_mul (a^2)),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      moment_exact] at hi
    have hid : (∫ u in (2:ℝ)..(927/200), p.eval u*d.eval u) = moment (p*d) := by
      simpa only [Polynomial.eval_mul] using moment_exact (p*d)
    rw [hid] at hi
    have ha : 2*a*moment p-a^2*moment (p*d)=moment p^2/moment (p*d) := by
      dsimp [a]
      field_simp
      ring
    rwa [ha] at hi

end F1TailPolynomialFTC
