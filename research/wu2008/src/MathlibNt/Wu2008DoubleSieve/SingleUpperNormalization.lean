import MathlibNt.Wu2008DoubleSieve.SingleUpperLowPacking

namespace Wu2008DoubleSieve.SingleUpperNormalization
open Finset Real Filter SingleUpperCounts SingleUpperSplice SingleUpperLowPacking
open scoped Classical Topology
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne

/-- Exact normalization of the one-prime Theta; neither C(N) nor p-2 is
suppressed. Positivity of p-1 is checked before cancellation. -/
theorem theta_single_exact {N : ℕ} {δ : ℝ} (hN : 2 ≤ N) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ 2 < p ∧ p.Coprime N) :
    boxTheta N ((N : ℝ)^(1/2-δ)) (fun _ : Fin 1 => P) =
      (4*logarithmicIntegral N*wuSingularSeries N/log N) *
        ∑ p ∈ P, 1 / (((p : ℝ)-2)*((1/2-δ)-log (p : ℝ)/log N)) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hl : log (N : ℝ) ≠ 0 := (log_pos (by exact_mod_cast hN)).ne'
  unfold boxTheta
  have he : (∑ d ∈ boxConvolutionSupport (fun _ : Fin 1 => P),
      (convolutionCoeff (fun _ : Fin 1 => P) d : ℝ)*wuSingularSeries (d*N) /
        ((Nat.totient d : ℝ)*log ((N : ℝ)^(1/2-δ)/(d : ℝ)))) =
      ∑ p ∈ P, wuSingularSeries (p*N) /
        ((Nat.totient p : ℝ)*log ((N : ℝ)^(1/2-δ)/(p : ℝ))) := by
    simpa only [mul_div_assoc, boxConvolutionSupport] using single_weighted_sum P
      (fun p => wuSingularSeries (p*N) /
        ((Nat.totient p : ℝ)*log ((N : ℝ)^(1/2-δ)/(p : ℝ))))
  rw [he, mul_sum, mul_sum]
  apply sum_congr rfl
  intro p hp
  obtain ⟨hpp, hp2, hpc⟩ := hP p hp
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
  have hp1 : (p : ℝ)-1 ≠ 0 := ne_of_gt (by exact_mod_cast (show 0 < (p : ℤ)-1 by omega))
  have hpn : ¬p ∣ N := by
    intro hd
    have hh := Nat.dvd_gcd (dvd_refl p) hd
    rw [hpc] at hh
    exact hpp.ne_one (Nat.dvd_one.mp hh)
  rw [wuSingularSeries_mul_prime_of_not_dvd (by omega) hpp hp2 hpn,
    Nat.totient_prime hpp, Nat.cast_sub (by omega : 1 ≤ p), Nat.cast_one,
    log_div (rpow_pos_of_pos hN0 _).ne' hp0.ne', log_rpow hN0]
  have heq : (1/2-δ)*log (N : ℝ)-log (p : ℝ) =
      ((1/2-δ)-log (p : ℝ)/log N)*log N := by field_simp
  rw [heq]
  field_simp

/-- The fixed target cutoff has its genuine C(N)/log(N) normalization,
uniformly in every later prime and window. -/
theorem local_product_upper {τ : ℝ} (hτ : 0 < τ) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      localSieveProduct N ((N : ℝ)^truncatedSixthLowerAlpha) ≤
        (1+τ)*(2*exp (-eulerMascheroniConstant)*wuSingularSeries N /
          (truncatedSixthLowerAlpha*log N)) := by
  have ha : 0 < truncatedSixthLowerAlpha := by norm_num [truncatedSixthLowerAlpha]
  have ht : Tendsto (fun N : ℕ => (N : ℝ)^truncatedSixthLowerAlpha) atTop atTop :=
    (tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop
  obtain ⟨T, hT⟩ := eventually_atTop.mp
    (ht.eventually (eventually_localSieveProduct_relative (1/truncatedSixthLowerAlpha) τ
      (by positivity) hτ))
  refine ⟨max 4 T, le_max_left _ _, ?_⟩
  intro N hN he
  have hN4 : 4 ≤ N := (le_max_left _ _).trans hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hpow : (N : ℝ) ≤ ((N : ℝ)^truncatedSixthLowerAlpha)^(1/truncatedSixthLowerAlpha) := by
    rw [← rpow_mul hN0.le, mul_one_div_cancel ha.ne', rpow_one]
  have h := hT N ((le_max_right _ _).trans hN) N (by omega) he hpow
  rw [log_rpow hN0] at h
  have hC := wuSingularSeries_pos N (by omega)
  have hl := log_pos (by exact_mod_cast (show 1 < N by omega) : (1 : ℝ) < N)
  apply (div_le_iff₀ (by positivity : 0 < 2*exp (-eulerMascheroniConstant)*wuSingularSeries N /
      (truncatedSixthLowerAlpha*log N))).mp
  linarith [(abs_le.mp h).2]

/-- Conversion from the fixed cutoff to the actual moving s is exact. -/
theorem local_normalization_identity {N p : ℕ} {δ : ℝ} (hN : 2 ≤ N)
    (hp : 0 < p) (hs : 0 < ((1/2-δ)-log (p : ℝ)/log N)/truncatedSixthLowerAlpha) :
    2*exp (-eulerMascheroniConstant)*wuSingularSeries N /
        (truncatedSixthLowerAlpha*log N) =
      2*(((1/2-δ)-log (p : ℝ)/log N)/truncatedSixthLowerAlpha)*wuSingularSeries N /
        (exp eulerMascheroniConstant*log ((N : ℝ)^(1/2-δ)/(p : ℝ))) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have ha : 0 < truncatedSixthLowerAlpha := by norm_num [truncatedSixthLowerAlpha]
  have hl : log (N : ℝ) ≠ 0 := (log_pos (by exact_mod_cast hN)).ne'
  have hc : (1/2-δ)-log (p : ℝ)/log N ≠ 0 := ((div_pos_iff_of_pos_right ha).mp hs).ne'
  rw [exp_neg, log_div (rpow_pos_of_pos hN0 _).ne' hp0.ne', log_rpow hN0]
  have heq : (1/2-δ)*log (N : ℝ)-log (p : ℝ) =
      ((1/2-δ)-log (p : ℝ)/log N)*log N := by field_simp
  rw [heq]
  generalize (1/2-δ)-log (p : ℝ)/log N = c at hc ⊢
  field_simp


/-- Actual normalized high density. Its 6*tau loss is still a genuine
weighted prime mass, not yet an epsilon times the final scale. -/
theorem high_density_normalized {δ τ : ℝ} (hδ : 0 ≤ δ)
    (hδhi : δ ≤ 1/100) (hτ : 0 < τ) (hτ1 : τ ≤ 1) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ r : ℝ, r ≤ 1/3 →
      highDensityMass N δ (exp eulerMascheroniConstant*τ/2) r ≤
        (4*logarithmicIntegral N*wuSingularSeries N/log N) *
          ∑ p ∈ highPrimes N δ r,
            (wuUpperCoefficient (((1/2-δ)-log (p : ℝ)/log N)/truncatedSixthLowerAlpha)+6*τ) /
              ((Nat.totient p : ℝ)*((1/2-δ)-log (p : ℝ)/log N)) := by
  obtain ⟨T, hT4, hT⟩ := local_product_upper hτ
  refine ⟨T, hT4, ?_⟩
  intro N hN he r hr
  have hN4 := hT4.trans hN
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 2 ≤ N by omega)
  have hN0 : (0 : ℝ) < N := by linarith
  have hlog : 0 < log (N : ℝ) := log_pos hNr
  have ha : 0 < truncatedSixthLowerAlpha := by norm_num [truncatedSixthLowerAlpha]
  have hC : 0 ≤ wuSingularSeries N := (wuSingularSeries_pos N (by omega)).le
  have hli : 0 ≤ logarithmicIntegral N :=
    MathlibNt.SieveTheory.LiuWeight.liuLogarithmicIntegral_nonneg 0 le_rfl
      (by exact_mod_cast (show 2 ≤ N by omega))
  unfold highDensityMass
  rw [mul_sum]
  apply sum_le_sum
  intro p hp
  have hpw := (mem_filter.mp hp).1
  have hp0 := (mem_primeWindow.mp hpw).1.pos
  have hpr : (0 : ℝ) < p := by exact_mod_cast hp0
  have hs := high_prime_s_bounds (by omega) hδ hδhi hr hpw (mem_filter.mp hp).2
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

end Wu2008DoubleSieve.SingleUpperNormalization
