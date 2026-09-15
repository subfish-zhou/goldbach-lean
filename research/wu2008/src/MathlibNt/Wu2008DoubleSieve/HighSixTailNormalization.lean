import MathlibNt.Wu2008DoubleSieve.HighSixTailDensity

namespace Wu2008DoubleSieve.HighSixTail
open Finset Set Real Filter MeasureTheory LiLiuPrereqBuchstab
open SingleUpperCounts SingleUpperSplice SingleUpperNormalization
open SingleUpperQuadrature SingleUpperPrimePayment SingleUpperHighQuadrature
open scoped Classical Topology
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne
/-- Actual normalized high density. Its 6*tau loss is still a genuine
weighted prime mass, not yet an epsilon times the final scale. -/
theorem tail_density_normalized {δ τ : ℝ} (hδ : 0 ≤ δ)
    (hδhi : δ ≤ 1/100) (hτ : 0 < τ) (hτ1 : τ ≤ 1) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      tailDensityMass N δ (exp eulerMascheroniConstant*τ/2) ≤
        (4*logarithmicIntegral N*wuSingularSeries N/log N) *
          ∑ p ∈ tailPrimes N,
            (wuUpperCoefficient (((1/2-δ)-log (p : ℝ)/log N)/truncatedSixthLowerAlpha)+6*τ) /
              ((Nat.totient p : ℝ)*((1/2-δ)-log (p : ℝ)/log N)) := by
  obtain ⟨T, hT4, hT⟩ := local_product_upper hτ
  refine ⟨T, hT4, ?_⟩
  intro N hN he
  have hN4 := hT4.trans hN
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 2 ≤ N by omega)
  have hN0 : (0 : ℝ) < N := by linarith
  have hlog : 0 < log (N : ℝ) := log_pos hNr
  have ha : 0 < truncatedSixthLowerAlpha := by norm_num [truncatedSixthLowerAlpha]
  have hC : 0 ≤ wuSingularSeries N := (wuSingularSeries_pos N (by omega)).le
  have hli : 0 ≤ logarithmicIntegral N :=
    MathlibNt.SieveTheory.LiuWeight.liuLogarithmicIntegral_nonneg 0 le_rfl
      (by exact_mod_cast (show 2 ≤ N by omega))
  unfold tailDensityMass
  rw [mul_sum]
  apply sum_le_sum
  intro p hp
  have hhigh := mem_filter.mp (tail_high (by omega) hδ hp)
  have hpw := hhigh.1
  have hp0 := (mem_primeWindow.mp hpw).1.pos
  have hpr : (0 : ℝ) < p := by exact_mod_cast hp0
  have hs := high_prime_s_bounds (by omega) hδ hδhi (le_refl (1/3 : ℝ)) hpw hhigh.2
  have hs0 : 0 < ((1/2-δ)-log (p : ℝ)/log N)/truncatedSixthLowerAlpha := by linarith
  have hc : 0 < (1/2-δ)-log (p : ℝ)/log N := (div_pos_iff_of_pos_right ha).mp hs0
  have hleq : log ((N : ℝ)^(1/2-δ)/(p : ℝ)) =
      ((1/2-δ)-log (p : ℝ)/log N)*log N := by
    rw [log_div (rpow_pos_of_pos hN0 _).ne' hpr.ne', log_rpow hN0]
    field_simp
  have hlp : 0 < log ((N : ℝ)^(1/2-δ)/(p : ℝ)) := by rw [hleq]; positivity
  have hloc := hT N hN he
  rw [local_normalization_identity (by omega) hp0 hs0] at hloc
  have hF : 0 ≤ jr1965F (((1/2-δ)-log (p : ℝ)/log N)/truncatedSixthLowerAlpha) +
      exp eulerMascheroniConstant*τ/2 := by
    have := jr1965F_pos hs0
    positivity
  have hb := (mul_le_mul_of_nonneg_left hloc hF).trans
    (canonical_upper_extended_normalization_budget (by linarith : 1 ≤
      ((1/2-δ)-log (p : ℝ)/log N)/truncatedSixthLowerAlpha) hs.2 hC hlp hτ.le hτ1)
  have hh := mul_le_mul_of_nonneg_left hb (div_nonneg hli (Nat.cast_nonneg (Nat.totient p)))
  change _ ≤ (logarithmicIntegral N / (Nat.totient p : ℝ))*
    ((wuUpperCoefficient (((1/2-δ)-log (p : ℝ)/log N)/truncatedSixthLowerAlpha)+6*τ)*
      (4*wuSingularSeries N/log ((N : ℝ)^(1/2-δ)/(p : ℝ)))) at hh
  rw [hleq] at hh
  convert hh using 1 <;> first | rfl | (simp only [div_eq_mul_inv, mul_inv_rev]; ring)

end Wu2008DoubleSieve.HighSixTail
